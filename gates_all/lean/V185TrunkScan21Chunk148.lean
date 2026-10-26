import V185TrunkScan21Chunk147

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1805561 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_1805561 : Nat := 118140960795 + 1805561 * 2 ^ 59
def prefixEnd_1805561 : Nat := 4983230072969 + 3 ^ 40 * 1805561 * 2
def baseEnd_1805561 : Nat := 412053619561206874659503

theorem tailTrace_1805561 : CollatzResearch.WordTrace tailWord_1805561 prefixEnd_1805561 412053619561206874659503 := by
  unfold tailWord_1805561
  simp only [CollatzResearch.WordTrace]
  refine ⟨65854219811768337113696537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43902813207845558075797691 65854219811768337113696537)
  ·
    refine ⟨49390664858826252835272403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65854219811768337113696537 49390664858826252835272403)
    ·
      refine ⟨74085997288239379252908605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49390664858826252835272403 74085997288239379252908605)
      ·
        refine ⟨27782248983089767219840727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74085997288239379252908605 27782248983089767219840727)
        ·
          refine ⟨41673373474634650829761091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27782248983089767219840727 41673373474634650829761091)
          ·
            refine ⟨62510060211951976244641637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41673373474634650829761091 62510060211951976244641637)
            ·
              refine ⟨11720636289740995545870307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62510060211951976244641637 11720636289740995545870307)
              ·
                refine ⟨17580954434611493318805461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11720636289740995545870307 17580954434611493318805461)
                ·
                  refine ⟨412053619561206874659503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17580954434611493318805461 412053619561206874659503)
                  ·
                    rfl

theorem cell21_1805561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_1805561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805561 prefixEnd_1805561 := by exact prefixLift 1805561
  have htrace : WordTrace (prefixWord ++ tailWord_1805561) baseStart_1805561 baseEnd_1805561 := by
    simpa [prefixWord, tailWord_1805561, baseEnd_1805561] using wordTrace_append hprefix tailTrace_1805561
  have hstable : (prefixWord ++ tailWord_1805561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805561).length < 2 ^ (prefixWord ++ tailWord_1805561).sum := by decide
  have hdescent : baseEnd_1805561 < baseStart_1805561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805598 : List Nat := [4, 3, 2, 1, 2, 2, 1, 6]
def baseStart_1805598 : Nat := 118140960795 + 1805598 * 2 ^ 59
def prefixEnd_1805598 : Nat := 4983230072969 + 3 ^ 40 * 1805598 * 2
def baseEnd_1805598 : Nat := 137354021155101010847587

theorem tailTrace_1805598 : CollatzResearch.WordTrace tailWord_1805598 prefixEnd_1805598 137354021155101010847587 := by
  unfold tailWord_1805598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231946164079286554099181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43903712875089528288528965 8231946164079286554099181)
  ·
    refine ⟨3086979811529732457787193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8231946164079286554099181 3086979811529732457787193)
    ·
      refine ⟨2315234858647299343340395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3086979811529732457787193 2315234858647299343340395)
      ·
        refine ⟨3472852287970949015010593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315234858647299343340395 3472852287970949015010593)
        ·
          refine ⟨2604639215978211761257945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472852287970949015010593 2604639215978211761257945)
          ·
            refine ⟨1953479411983658820943459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604639215978211761257945 1953479411983658820943459)
            ·
              refine ⟨2930219117975488231415189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953479411983658820943459 2930219117975488231415189)
              ·
                refine ⟨137354021155101010847587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2930219117975488231415189 137354021155101010847587)
                ·
                  rfl

theorem cell21_1805598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_1805598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805598 prefixEnd_1805598 := by exact prefixLift 1805598
  have htrace : WordTrace (prefixWord ++ tailWord_1805598) baseStart_1805598 baseEnd_1805598 := by
    simpa [prefixWord, tailWord_1805598, baseEnd_1805598] using wordTrace_append hprefix tailTrace_1805598
  have hstable : (prefixWord ++ tailWord_1805598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805598).length < 2 ^ (prefixWord ++ tailWord_1805598).sum := by decide
  have hdescent : baseEnd_1805598 < baseStart_1805598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805629 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1805629 : Nat := 118140960795 + 1805629 * 2 ^ 59
def prefixEnd_1805629 : Nat := 4983230072969 + 3 ^ 40 * 1805629 * 2
def baseEnd_1805629 : Nat := 412069138087653867526031

theorem tailTrace_1805629 : CollatzResearch.WordTrace tailWord_1805629 prefixEnd_1805629 412069138087653867526031 := by
  unfold tailWord_1805629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856699975521984727171941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43904466650347989818114627 65856699975521984727171941)
  ·
    refine ⟨12348131245410372136344739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65856699975521984727171941 12348131245410372136344739)
    ·
      refine ⟨18522196868115558204517109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348131245410372136344739 18522196868115558204517109)
      ·
        refine ⟨1736455956385833581673479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18522196868115558204517109 1736455956385833581673479)
        ·
          refine ⟨2604683934578750372510219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736455956385833581673479 2604683934578750372510219)
          ·
            refine ⟨3907025901868125558765329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604683934578750372510219 3907025901868125558765329)
            ·
              refine ⟨2930269426401094169073997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907025901868125558765329 2930269426401094169073997)
              ·
                refine ⟨1098851034900410313402749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2930269426401094169073997 1098851034900410313402749)
                ·
                  refine ⟨412069138087653867526031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098851034900410313402749 412069138087653867526031)
                  ·
                    rfl

theorem cell21_1805629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1805629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805629 prefixEnd_1805629 := by exact prefixLift 1805629
  have htrace : WordTrace (prefixWord ++ tailWord_1805629) baseStart_1805629 baseEnd_1805629 := by
    simpa [prefixWord, tailWord_1805629, baseEnd_1805629] using wordTrace_append hprefix tailTrace_1805629
  have hstable : (prefixWord ++ tailWord_1805629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805629).length < 2 ^ (prefixWord ++ tailWord_1805629).sum := by decide
  have hdescent : baseEnd_1805629 < baseStart_1805629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805674 : List Nat := [3, 1, 3, 3, 3, 1, 2, 5]
def baseStart_1805674 : Nat := 118140960795 + 1805674 * 2 ^ 59
def prefixEnd_1805674 : Nat := 4983230072969 + 3 ^ 40 * 1805674 * 2
def baseEnd_1805674 : Nat := 137359802566914596425313

theorem tailTrace_1805674 : CollatzResearch.WordTrace tailWord_1805674 prefixEnd_1805674 137359802566914596425313 := by
  unfold tailWord_1805674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464585315089739353140019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43905560840239304941706717 16464585315089739353140019)
  ·
    refine ⟨24696877972634609029710029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464585315089739353140019 24696877972634609029710029)
    ·
      refine ⟨9261329239737978386141261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24696877972634609029710029 9261329239737978386141261)
      ·
        refine ⟨3472998464901741894802973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9261329239737978386141261 3472998464901741894802973)
        ·
          refine ⟨1302374424338153210551115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3472998464901741894802973 1302374424338153210551115)
          ·
            refine ⟨1953561636507229815826673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302374424338153210551115 1953561636507229815826673)
            ·
              refine ⟨1465171227380422361870005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953561636507229815826673 1465171227380422361870005)
              ·
                refine ⟨137359802566914596425313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465171227380422361870005 137359802566914596425313)
                ·
                  rfl

theorem cell21_1805674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_1805674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805674 prefixEnd_1805674 := by exact prefixLift 1805674
  have htrace : WordTrace (prefixWord ++ tailWord_1805674) baseStart_1805674 baseEnd_1805674 := by
    simpa [prefixWord, tailWord_1805674, baseEnd_1805674] using wordTrace_append hprefix tailTrace_1805674
  have hstable : (prefixWord ++ tailWord_1805674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805674).length < 2 ^ (prefixWord ++ tailWord_1805674).sum := by decide
  have hdescent : baseEnd_1805674 < baseStart_1805674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805699 : List Nat := [1, 1, 1, 3, 5, 3, 7]
def baseStart_1805699 : Nat := 118140960795 + 1805699 * 2 ^ 59
def prefixEnd_1805699 : Nat := 4983230072969 + 3 ^ 40 * 1805699 * 2
def baseEnd_1805699 : Nat := 45787234782372144595469

theorem tailTrace_1805699 : CollatzResearch.WordTrace tailWord_1805699 prefixEnd_1805699 45787234782372144595469 := by
  unfold tailWord_1805699
  simp only [CollatzResearch.WordTrace]
  refine ⟨65859253085268386682220151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43906168723512257788146767 65859253085268386682220151)
  ·
    refine ⟨98788879627902580023330227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65859253085268386682220151 98788879627902580023330227)
    ·
      refine ⟨148183319441853870034995341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98788879627902580023330227 148183319441853870034995341)
      ·
        refine ⟨55568744790695201263123253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148183319441853870034995341 55568744790695201263123253)
        ·
          refine ⟨5209569824127675118417805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55568744790695201263123253 5209569824127675118417805)
          ·
            refine ⟨1953588684047878169406677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5209569824127675118417805 1953588684047878169406677)
            ·
              refine ⟨45787234782372144595469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1953588684047878169406677 45787234782372144595469)
              ·
                rfl

theorem cell21_1805699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 7].length) (baseStart_1805699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805699 prefixEnd_1805699 := by exact prefixLift 1805699
  have htrace : WordTrace (prefixWord ++ tailWord_1805699) baseStart_1805699 baseEnd_1805699 := by
    simpa [prefixWord, tailWord_1805699, baseEnd_1805699] using wordTrace_append hprefix tailTrace_1805699
  have hstable : (prefixWord ++ tailWord_1805699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805699).length < 2 ^ (prefixWord ++ tailWord_1805699).sum := by decide
  have hdescent : baseEnd_1805699 < baseStart_1805699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805716 : List Nat := [2, 4, 2, 1, 2, 2, 2, 6]
def baseStart_1805716 : Nat := 118140960795 + 1805716 * 2 ^ 59
def prefixEnd_1805716 : Nat := 4983230072969 + 3 ^ 40 * 1805716 * 2
def baseEnd_1805716 : Nat := 137362997557653683191951

theorem tailTrace_1805716 : CollatzResearch.WordTrace tailWord_1805716 prefixEnd_1805716 137362997557653683191951 := by
  unfold tailWord_1805716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32929936563103399292794501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43906582084137865723726001 32929936563103399292794501)
  ·
    refine ⟨6174363105581887367398969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32929936563103399292794501 6174363105581887367398969)
    ·
      refine ⟨4630772329186415525549227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6174363105581887367398969 4630772329186415525549227)
      ·
        refine ⟨6946158493779623288323841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4630772329186415525549227 6946158493779623288323841)
        ·
          refine ⟨5209618870334717466242881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6946158493779623288323841 5209618870334717466242881)
          ·
            refine ⟨3907214152751038099682161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209618870334717466242881 3907214152751038099682161)
            ·
              refine ⟨2930410614563278574761621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907214152751038099682161 2930410614563278574761621)
              ·
                refine ⟨137362997557653683191951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2930410614563278574761621 137362997557653683191951)
                ·
                  rfl

theorem cell21_1805716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_1805716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805716 prefixEnd_1805716 := by exact prefixLift 1805716
  have htrace : WordTrace (prefixWord ++ tailWord_1805716) baseStart_1805716 baseEnd_1805716 := by
    simpa [prefixWord, tailWord_1805716, baseEnd_1805716] using wordTrace_append hprefix tailTrace_1805716
  have hstable : (prefixWord ++ tailWord_1805716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805716).length < 2 ^ (prefixWord ++ tailWord_1805716).sum := by decide
  have hdescent : baseEnd_1805716 < baseStart_1805716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805764 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_1805764 : Nat := 118140960795 + 1805764 * 2 ^ 59
def prefixEnd_1805764 : Nat := 4983230072969 + 3 ^ 40 * 1805764 * 2
def baseEnd_1805764 : Nat := 412099946926923632775755

theorem tailTrace_1805764 : CollatzResearch.WordTrace tailWord_1805764 prefixEnd_1805764 412099946926923632775755 := by
  unfold tailWord_1805764
  simp only [CollatzResearch.WordTrace]
  refine ⟨32930811915016451391668173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43907749220021935188890897 32930811915016451391668173)
  ·
    refine ⟨12349054468131169271875565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32930811915016451391668173 12349054468131169271875565)
    ·
      refine ⟨4630895425549188476953337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12349054468131169271875565 4630895425549188476953337)
      ·
        refine ⟨3473171569161891357715003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4630895425549188476953337 3473171569161891357715003)
        ·
          refine ⟨5209757353742837036572505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473171569161891357715003 5209757353742837036572505)
          ·
            refine ⟨3907318015307127777429379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209757353742837036572505 3907318015307127777429379)
            ·
              refine ⟨5860977022960691666144069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907318015307127777429379 5860977022960691666144069)
              ·
                refine ⟨1098933191805129687402013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5860977022960691666144069 1098933191805129687402013)
                ·
                  refine ⟨412099946926923632775755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098933191805129687402013 412099946926923632775755)
                  ·
                    rfl

theorem cell21_1805764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_1805764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805764 prefixEnd_1805764 := by exact prefixLift 1805764
  have htrace : WordTrace (prefixWord ++ tailWord_1805764) baseStart_1805764 baseEnd_1805764 := by
    simpa [prefixWord, tailWord_1805764, baseEnd_1805764] using wordTrace_append hprefix tailTrace_1805764
  have hstable : (prefixWord ++ tailWord_1805764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805764).length < 2 ^ (prefixWord ++ tailWord_1805764).sum := by decide
  have hdescent : baseEnd_1805764 < baseStart_1805764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805933 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1805933 : Nat := 118140960795 + 1805933 * 2 ^ 59
def prefixEnd_1805933 : Nat := 4983230072969 + 3 ^ 40 * 1805933 * 2
def baseEnd_1805933 : Nat := 412138515029416894458743

theorem tailTrace_1805933 : CollatzResearch.WordTrace tailWord_1805933 prefixEnd_1805933 412138515029416894458743 := by
  unfold tailWord_1805933
  simp only [CollatzResearch.WordTrace]
  refine ⟨65867787766420644646238453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43911858510947096430825635 65867787766420644646238453)
  ·
    refine ⟨6175105103101935435584855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65867787766420644646238453 6175105103101935435584855)
    ·
      refine ⟨9262657654652903153377283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175105103101935435584855 9262657654652903153377283)
      ·
        refine ⟨13893986481979354730065925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262657654652903153377283 13893986481979354730065925)
        ·
          refine ⟨2605122465371129011887361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13893986481979354730065925 2605122465371129011887361)
          ·
            refine ⟨1953841849028346758915521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605122465371129011887361 1953841849028346758915521)
            ·
              refine ⟨1465381386771260069186641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953841849028346758915521 1465381386771260069186641)
              ·
                refine ⟨1099036040078445051889981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465381386771260069186641 1099036040078445051889981)
                ·
                  refine ⟨412138515029416894458743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099036040078445051889981 412138515029416894458743)
                  ·
                    rfl

theorem cell21_1805933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1805933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805933 prefixEnd_1805933 := by exact prefixLift 1805933
  have htrace : WordTrace (prefixWord ++ tailWord_1805933) baseStart_1805933 baseEnd_1805933 := by
    simpa [prefixWord, tailWord_1805933, baseEnd_1805933] using wordTrace_append hprefix tailTrace_1805933
  have hstable : (prefixWord ++ tailWord_1805933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805933).length < 2 ^ (prefixWord ++ tailWord_1805933).sum := by decide
  have hdescent : baseEnd_1805933 < baseStart_1805933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805955 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_1805955 : Nat := 118140960795 + 1805955 * 2 ^ 59
def prefixEnd_1805955 : Nat := 4983230072969 + 3 ^ 40 * 1805955 * 2
def baseEnd_1805955 : Nat := 412143535729149745092031

theorem tailTrace_1805955 : CollatzResearch.WordTrace tailWord_1805955 prefixEnd_1805955 412143535729149745092031 := by
  unfold tailWord_1805955
  simp only [CollatzResearch.WordTrace]
  refine ⟨65868590172340942403539319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43912393448227294935692879 65868590172340942403539319)
  ·
    refine ⟨98802885258511413605308979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65868590172340942403539319 98802885258511413605308979)
    ·
      refine ⟨148204327887767120407963469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98802885258511413605308979 148204327887767120407963469)
      ·
        refine ⟨55576622957912670152986301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148204327887767120407963469 55576622957912670152986301)
        ·
          refine ⟨20841233609217251307369863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55576622957912670152986301 20841233609217251307369863)
          ·
            refine ⟨31261850413825876961054795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20841233609217251307369863 31261850413825876961054795)
            ·
              refine ⟨46892775620738815441582193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31261850413825876961054795 46892775620738815441582193)
              ·
                refine ⟨35169581715554111581186645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46892775620738815441582193 35169581715554111581186645)
                ·
                  refine ⟨412143535729149745092031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35169581715554111581186645 412143535729149745092031)
                  ·
                    rfl

theorem cell21_1805955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_1805955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805955 prefixEnd_1805955 := by exact prefixLift 1805955
  have htrace : WordTrace (prefixWord ++ tailWord_1805955) baseStart_1805955 baseEnd_1805955 := by
    simpa [prefixWord, tailWord_1805955, baseEnd_1805955] using wordTrace_append hprefix tailTrace_1805955
  have hstable : (prefixWord ++ tailWord_1805955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805955).length < 2 ^ (prefixWord ++ tailWord_1805955).sum := by decide
  have hdescent : baseEnd_1805955 < baseStart_1805955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805975 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 3]
def baseStart_1805975 : Nat := 118140960795 + 1805975 * 2 ^ 59
def prefixEnd_1805975 : Nat := 4983230072969 + 3 ^ 40 * 1805975 * 2
def baseEnd_1805975 : Nat := 412148100001634154758657

theorem tailTrace_1805975 : CollatzResearch.WordTrace tailWord_1805975 prefixEnd_1805975 412148100001634154758657 := by
  unfold tailWord_1805975
  simp only [CollatzResearch.WordTrace]
  refine ⟨65869319632268485819267379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43912879754845657212844919 65869319632268485819267379)
  ·
    refine ⟨98803979448402728728901069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65869319632268485819267379 98803979448402728728901069)
    ·
      refine ⟨37051492293151023273337901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98803979448402728728901069 37051492293151023273337901)
      ·
        refine ⟨13894309609931633727501713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37051492293151023273337901 13894309609931633727501713)
        ·
          refine ⟨10420732207448725295626285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13894309609931633727501713 10420732207448725295626285)
          ·
            refine ⟨3907774577793271985859857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10420732207448725295626285 3907774577793271985859857)
            ·
              refine ⟨2930830933344953989394893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907774577793271985859857 2930830933344953989394893)
              ·
                refine ⟨1099061600004357746023085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2930830933344953989394893 1099061600004357746023085)
                ·
                  refine ⟨412148100001634154758657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099061600004357746023085 412148100001634154758657)
                  ·
                    rfl

theorem cell21_1805975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3].length) (baseStart_1805975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805975 prefixEnd_1805975 := by exact prefixLift 1805975
  have htrace : WordTrace (prefixWord ++ tailWord_1805975) baseStart_1805975 baseEnd_1805975 := by
    simpa [prefixWord, tailWord_1805975, baseEnd_1805975] using wordTrace_append hprefix tailTrace_1805975
  have hstable : (prefixWord ++ tailWord_1805975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805975).length < 2 ^ (prefixWord ++ tailWord_1805975).sum := by decide
  have hdescent : baseEnd_1805975 < baseStart_1805975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806051 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 5]
def baseStart_1806051 : Nat := 118140960795 + 1806051 * 2 ^ 59
def prefixEnd_1806051 : Nat := 4983230072969 + 3 ^ 40 * 1806051 * 2
def baseEnd_1806051 : Nat := 412165444237074911491835

theorem tailTrace_1806051 : CollatzResearch.WordTrace tailWord_1806051 prefixEnd_1806051 412165444237074911491835 := by
  unfold tailWord_1806051
  simp only [CollatzResearch.WordTrace]
  refine ⟨65872091579993150799034007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43914727719995433866022671 65872091579993150799034007)
  ·
    refine ⟨98808137369989726198551011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65872091579993150799034007 98808137369989726198551011)
    ·
      refine ⟨148212206054984589297826517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98808137369989726198551011 148212206054984589297826517)
      ·
        refine ⟨3473723579413701311667809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 148212206054984589297826517 3473723579413701311667809)
        ·
          refine ⟨2605292684560275983750857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473723579413701311667809 2605292684560275983750857)
          ·
            refine ⟨1953969513420206987813143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605292684560275983750857 1953969513420206987813143)
            ·
              refine ⟨2930954270130310481719715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953969513420206987813143 2930954270130310481719715)
              ·
                refine ⟨4396431405195465722579573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930954270130310481719715 4396431405195465722579573)
                ·
                  refine ⟨412165444237074911491835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396431405195465722579573 412165444237074911491835)
                  ·
                    rfl

theorem cell21_1806051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_1806051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806051 prefixEnd_1806051 := by exact prefixLift 1806051
  have htrace : WordTrace (prefixWord ++ tailWord_1806051) baseStart_1806051 baseEnd_1806051 := by
    simpa [prefixWord, tailWord_1806051, baseEnd_1806051] using wordTrace_append hprefix tailTrace_1806051
  have hstable : (prefixWord ++ tailWord_1806051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806051).length < 2 ^ (prefixWord ++ tailWord_1806051).sum := by decide
  have hdescent : baseEnd_1806051 < baseStart_1806051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806065 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 4]
def baseStart_1806065 : Nat := 118140960795 + 1806065 * 2 ^ 59
def prefixEnd_1806065 : Nat := 4983230072969 + 3 ^ 40 * 1806065 * 2
def baseEnd_1806065 : Nat := 412168639227813998258473

theorem tailTrace_1806065 : CollatzResearch.WordTrace tailWord_1806065 prefixEnd_1806065 412168639227813998258473 := by
  unfold tailWord_1806065
  simp only [CollatzResearch.WordTrace]
  refine ⟨65872602201942431190043649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43915068134628287460029099 65872602201942431190043649)
  ·
    refine ⟨49404451651456823392532737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65872602201942431190043649 49404451651456823392532737)
    ·
      refine ⟨37053338738592617544399553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49404451651456823392532737 37053338738592617544399553)
      ·
        refine ⟨27790004053944463158299665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37053338738592617544399553 27790004053944463158299665)
        ·
          refine ⟨20842503040458347368724749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27790004053944463158299665 20842503040458347368724749)
          ·
            refine ⟨7815938640171880263271781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20842503040458347368724749 7815938640171880263271781)
            ·
              refine ⟨1465488495032227549363459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7815938640171880263271781 1465488495032227549363459)
              ·
                refine ⟨2198232742548341324045189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465488495032227549363459 2198232742548341324045189)
                ·
                  refine ⟨412168639227813998258473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198232742548341324045189 412168639227813998258473)
                  ·
                    rfl

theorem cell21_1806065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_1806065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806065 prefixEnd_1806065 := by exact prefixLift 1806065
  have htrace : WordTrace (prefixWord ++ tailWord_1806065) baseStart_1806065 baseEnd_1806065 := by
    simpa [prefixWord, tailWord_1806065, baseEnd_1806065] using wordTrace_append hprefix tailTrace_1806065
  have hstable : (prefixWord ++ tailWord_1806065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806065).length < 2 ^ (prefixWord ++ tailWord_1806065).sum := by decide
  have hdescent : baseEnd_1806065 < baseStart_1806065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806124 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_1806124 : Nat := 118140960795 + 1806124 * 2 ^ 59
def prefixEnd_1806124 : Nat := 4983230072969 + 3 ^ 40 * 1806124 * 2
def baseEnd_1806124 : Nat := 412182103831643006775019

theorem tailTrace_1806124 : CollatzResearch.WordTrace tailWord_1806124 prefixEnd_1806124 412182103831643006775019 := by
  unfold tailWord_1806124
  simp only [CollatzResearch.WordTrace]
  refine ⟨32937377054364342133220713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43916502739152456177627617 32937377054364342133220713)
  ·
    refine ⟨24703032790773256599915535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32937377054364342133220713 24703032790773256599915535)
    ·
      refine ⟨37054549186159884899873303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24703032790773256599915535 37054549186159884899873303)
      ·
        refine ⟨55581823779239827349809955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37054549186159884899873303 55581823779239827349809955)
        ·
          refine ⟨83372735668859741024714933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55581823779239827349809955 83372735668859741024714933)
          ·
            refine ⟨7816193968955600721067025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83372735668859741024714933 7816193968955600721067025)
            ·
              refine ⟨5862145476716700540800269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816193968955600721067025 5862145476716700540800269)
              ·
                refine ⟨2198304553768762702800101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5862145476716700540800269 2198304553768762702800101)
                ·
                  refine ⟨412182103831643006775019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198304553768762702800101 412182103831643006775019)
                  ·
                    rfl

theorem cell21_1806124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_1806124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806124 prefixEnd_1806124 := by exact prefixLift 1806124
  have htrace : WordTrace (prefixWord ++ tailWord_1806124) baseStart_1806124 baseEnd_1806124 := by
    simpa [prefixWord, tailWord_1806124, baseEnd_1806124] using wordTrace_append hprefix tailTrace_1806124
  have hstable : (prefixWord ++ tailWord_1806124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806124).length < 2 ^ (prefixWord ++ tailWord_1806124).sum := by decide
  have hdescent : baseEnd_1806124 < baseStart_1806124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806169 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_1806169 : Nat := 118140960795 + 1806169 * 2 ^ 59
def prefixEnd_1806169 : Nat := 4983230072969 + 3 ^ 40 * 1806169 * 2
def baseEnd_1806169 : Nat := 412192373444732928524927

theorem tailTrace_1806169 : CollatzResearch.WordTrace tailWord_1806169 prefixEnd_1806169 412192373444732928524927 := by
  unfold tailWord_1806169
  simp only [CollatzResearch.WordTrace]
  refine ⟨65876395393565656951829561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43917596929043771301219707 65876395393565656951829561)
  ·
    refine ⟨49407296545174242713872171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65876395393565656951829561 49407296545174242713872171)
    ·
      refine ⟨74110944817761364070808257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49407296545174242713872171 74110944817761364070808257)
      ·
        refine ⟨55583208613321023053106193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74110944817761364070808257 55583208613321023053106193)
        ·
          refine ⟨41687406459990767289829645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55583208613321023053106193 41687406459990767289829645)
          ·
            refine ⟨15632777422496537733686117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41687406459990767289829645 15632777422496537733686117)
            ·
              refine ⟨2931145766718100825066147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15632777422496537733686117 2931145766718100825066147)
              ·
                refine ⟨4396718650077151237599221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931145766718100825066147 4396718650077151237599221)
                ·
                  refine ⟨412192373444732928524927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396718650077151237599221 412192373444732928524927)
                  ·
                    rfl

theorem cell21_1806169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_1806169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806169 prefixEnd_1806169 := by exact prefixLift 1806169
  have htrace : WordTrace (prefixWord ++ tailWord_1806169) baseStart_1806169 baseEnd_1806169 := by
    simpa [prefixWord, tailWord_1806169, baseEnd_1806169] using wordTrace_append hprefix tailTrace_1806169
  have hstable : (prefixWord ++ tailWord_1806169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806169).length < 2 ^ (prefixWord ++ tailWord_1806169).sum := by decide
  have hdescent : baseEnd_1806169 < baseStart_1806169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806234 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1806234 : Nat := 118140960795 + 1806234 * 2 ^ 59
def prefixEnd_1806234 : Nat := 4983230072969 + 3 ^ 40 * 1806234 * 2
def baseEnd_1806234 : Nat := 412207207330307259941461

theorem tailTrace_1806234 : CollatzResearch.WordTrace tailWord_1806234 prefixEnd_1806234 412207207330307259941461 := by
  unfold tailWord_1806234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469691534582543263236439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43919177425553448701963837 16469691534582543263236439)
  ·
    refine ⟨24704537301873814894854659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469691534582543263236439 24704537301873814894854659)
    ·
      refine ⟨37056805952810722342281989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24704537301873814894854659 37056805952810722342281989)
      ·
        refine ⟨6948151116152010439177873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37056805952810722342281989 6948151116152010439177873)
        ·
          refine ⟨5211113337114007829383405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6948151116152010439177873 5211113337114007829383405)
          ·
            refine ⟨1954167501417752936018777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5211113337114007829383405 1954167501417752936018777)
            ·
              refine ⟨1465625626063314702014083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954167501417752936018777 1465625626063314702014083)
              ·
                refine ⟨2198438439094972053021125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465625626063314702014083 2198438439094972053021125)
                ·
                  refine ⟨412207207330307259941461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198438439094972053021125 412207207330307259941461)
                  ·
                    rfl

theorem cell21_1806234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1806234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806234 prefixEnd_1806234 := by exact prefixLift 1806234
  have htrace : WordTrace (prefixWord ++ tailWord_1806234) baseStart_1806234 baseEnd_1806234 := by
    simpa [prefixWord, tailWord_1806234, baseEnd_1806234] using wordTrace_append hprefix tailTrace_1806234
  have hstable : (prefixWord ++ tailWord_1806234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806234).length < 2 ^ (prefixWord ++ tailWord_1806234).sum := by decide
  have hdescent : baseEnd_1806234 < baseStart_1806234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806273 : List Nat := [1, 2, 18]
def baseStart_1806273 : Nat := 118140960795 + 1806273 * 2 ^ 59
def prefixEnd_1806273 : Nat := 4983230072969 + 3 ^ 40 * 1806273 * 2
def baseEnd_1806273 : Nat := 565454194323253578589

theorem tailTrace_1806273 : CollatzResearch.WordTrace tailWord_1806273 prefixEnd_1806273 565454194323253578589 := by
  unfold tailWord_1806273
  simp only [CollatzResearch.WordTrace]
  refine ⟨65880188585188882713615473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43920125723459255142410315 65880188585188882713615473)
  ·
    refine ⟨49410141438891662035211605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65880188585188882713615473 49410141438891662035211605)
    ·
      refine ⟨565454194323253578589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 49410141438891662035211605 565454194323253578589)
      ·
        rfl

theorem cell21_1806273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 18].length) (baseStart_1806273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806273 prefixEnd_1806273 := by exact prefixLift 1806273
  have htrace : WordTrace (prefixWord ++ tailWord_1806273) baseStart_1806273 baseEnd_1806273 := by
    simpa [prefixWord, tailWord_1806273, baseEnd_1806273] using wordTrace_append hprefix tailTrace_1806273
  have hstable : (prefixWord ++ tailWord_1806273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806273).length < 2 ^ (prefixWord ++ tailWord_1806273).sum := by decide
  have hdescent : baseEnd_1806273 < baseStart_1806273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806307 : List Nat := [1, 1, 1, 6, 1, 3, 3, 5]
def baseStart_1806307 : Nat := 118140960795 + 1806307 * 2 ^ 59
def prefixEnd_1806307 : Nat := 4983230072969 + 3 ^ 40 * 1806307 * 2
def baseEnd_1806307 : Nat := 137407955641625118408215

theorem tailTrace_1806307 : CollatzResearch.WordTrace tailWord_1806307 prefixEnd_1806307 137407955641625118408215 := by
  unfold tailWord_1806307
  simp only [CollatzResearch.WordTrace]
  refine ⟨65881428667065706520353175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43920952444710471013568783 65881428667065706520353175)
  ·
    refine ⟨98822143000598559780529763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65881428667065706520353175 98822143000598559780529763)
    ·
      refine ⟨148233214500897839670794645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98822143000598559780529763 148233214500897839670794645)
      ·
        refine ⟨6948431929729586234568499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148233214500897839670794645 6948431929729586234568499)
        ·
          refine ⟨10422647894594379351852749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6948431929729586234568499 10422647894594379351852749)
          ·
            refine ⟨3908492960472892256944781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10422647894594379351852749 3908492960472892256944781)
            ·
              refine ⟨1465684860177334596354293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3908492960472892256944781 1465684860177334596354293)
              ·
                refine ⟨137407955641625118408215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465684860177334596354293 137407955641625118408215)
                ·
                  rfl

theorem cell21_1806307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 5].length) (baseStart_1806307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806307 prefixEnd_1806307 := by exact prefixLift 1806307
  have htrace : WordTrace (prefixWord ++ tailWord_1806307) baseStart_1806307 baseEnd_1806307 := by
    simpa [prefixWord, tailWord_1806307, baseEnd_1806307] using wordTrace_append hprefix tailTrace_1806307
  have hstable : (prefixWord ++ tailWord_1806307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806307).length < 2 ^ (prefixWord ++ tailWord_1806307).sum := by decide
  have hdescent : baseEnd_1806307 < baseStart_1806307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806372 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_1806372 : Nat := 118140960795 + 1806372 * 2 ^ 59
def prefixEnd_1806372 : Nat := 4983230072969 + 3 ^ 40 * 1806372 * 2
def baseEnd_1806372 : Nat := 412238700810449686641179

theorem tailTrace_1806372 : CollatzResearch.WordTrace tailWord_1806372 prefixEnd_1806372 412238700810449686641179 := by
  unfold tailWord_1806372
  simp only [CollatzResearch.WordTrace]
  refine ⟨32941899705915111310734685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43922532941220148414312913 32941899705915111310734685)
  ·
    refine ⟨12353212389718166741525507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32941899705915111310734685 12353212389718166741525507)
    ·
      refine ⟨18529818584577250112288261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12353212389718166741525507 18529818584577250112288261)
      ·
        refine ⟨3474340984608234396054049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18529818584577250112288261 3474340984608234396054049)
        ·
          refine ⟨2605755738456175797040537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474340984608234396054049 2605755738456175797040537)
          ·
            refine ⟨1954316803842131847780403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605755738456175797040537 1954316803842131847780403)
            ·
              refine ⟨2931475205763197771670605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954316803842131847780403 2931475205763197771670605)
              ·
                refine ⟨1099303202161199164376477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2931475205763197771670605 1099303202161199164376477)
                ·
                  refine ⟨412238700810449686641179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099303202161199164376477 412238700810449686641179)
                  ·
                    rfl

theorem cell21_1806372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_1806372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806372 prefixEnd_1806372 := by exact prefixLift 1806372
  have htrace : WordTrace (prefixWord ++ tailWord_1806372) baseStart_1806372 baseEnd_1806372 := by
    simpa [prefixWord, tailWord_1806372, baseEnd_1806372] using wordTrace_append hprefix tailTrace_1806372
  have hstable : (prefixWord ++ tailWord_1806372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806372).length < 2 ^ (prefixWord ++ tailWord_1806372).sum := by decide
  have hdescent : baseEnd_1806372 < baseStart_1806372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806411 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_1806411 : Nat := 118140960795 + 1806411 * 2 ^ 59
def prefixEnd_1806411 : Nat := 4983230072969 + 3 ^ 40 * 1806411 * 2
def baseEnd_1806411 : Nat := 412247601141794285491099

theorem tailTrace_1806411 : CollatzResearch.WordTrace tailWord_1806411 prefixEnd_1806411 412247601141794285491099 := by
  unfold tailWord_1806411
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885221858688932282139087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43923481239125954854759391 65885221858688932282139087)
  ·
    refine ⟨98827832788033398423208631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65885221858688932282139087 98827832788033398423208631)
    ·
      refine ⟨148241749182050097634812947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98827832788033398423208631 148241749182050097634812947)
      ·
        refine ⟨222362623773075146452219421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148241749182050097634812947 222362623773075146452219421)
        ·
          refine ⟨83385983914903179919582283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222362623773075146452219421 83385983914903179919582283)
          ·
            refine ⟨125078975872354769879373425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83385983914903179919582283 125078975872354769879373425)
            ·
              refine ⟨93809231904266077409530069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125078975872354769879373425 93809231904266077409530069)
              ·
                refine ⟨2198653872756236189285861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93809231904266077409530069 2198653872756236189285861)
                ·
                  refine ⟨412247601141794285491099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198653872756236189285861 412247601141794285491099)
                  ·
                    rfl

theorem cell21_1806411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_1806411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806411 prefixEnd_1806411 := by exact prefixLift 1806411
  have htrace : WordTrace (prefixWord ++ tailWord_1806411) baseStart_1806411 baseEnd_1806411 := by
    simpa [prefixWord, tailWord_1806411, baseEnd_1806411] using wordTrace_append hprefix tailTrace_1806411
  have hstable : (prefixWord ++ tailWord_1806411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806411).length < 2 ^ (prefixWord ++ tailWord_1806411).sum := by decide
  have hdescent : baseEnd_1806411 < baseStart_1806411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806425 : List Nat := [1, 2, 1, 2, 2, 1, 3, 9]
def baseStart_1806425 : Nat := 118140960795 + 1806425 * 2 ^ 59
def prefixEnd_1806425 : Nat := 4983230072969 + 3 ^ 40 * 1806425 * 2
def baseEnd_1806425 : Nat := 137416932044177790752579

theorem tailTrace_1806425 : CollatzResearch.WordTrace tailWord_1806425 prefixEnd_1806425 137416932044177790752579 := by
  unfold tailWord_1806425
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885732480638212673148729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43923821653758808448765819 65885732480638212673148729)
  ·
    refine ⟨49414299360478659504861547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65885732480638212673148729 49414299360478659504861547)
    ·
      refine ⟨74121449040717989257292321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49414299360478659504861547 74121449040717989257292321)
      ·
        refine ⟨55591086780538491942969241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74121449040717989257292321 55591086780538491942969241)
        ·
          refine ⟨41693315085403868957226931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55591086780538491942969241 41693315085403868957226931)
          ·
            refine ⟨62539972628105803435840397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41693315085403868957226931 62539972628105803435840397)
            ·
              refine ⟨23452489735539676288440149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62539972628105803435840397 23452489735539676288440149)
              ·
                refine ⟨137416932044177790752579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23452489735539676288440149 137416932044177790752579)
                ·
                  rfl

theorem cell21_1806425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_1806425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806425 prefixEnd_1806425 := by exact prefixLift 1806425
  have htrace : WordTrace (prefixWord ++ tailWord_1806425) baseStart_1806425 baseEnd_1806425 := by
    simpa [prefixWord, tailWord_1806425, baseEnd_1806425] using wordTrace_append hprefix tailTrace_1806425
  have hstable : (prefixWord ++ tailWord_1806425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806425).length < 2 ^ (prefixWord ++ tailWord_1806425).sum := by decide
  have hdescent : baseEnd_1806425 < baseStart_1806425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806442 : List Nat := [3, 1, 3, 2, 3, 9]
def baseStart_1806442 : Nat := 118140960795 + 1806442 * 2 ^ 59
def prefixEnd_1806442 : Nat := 4983230072969 + 3 ^ 40 * 1806442 * 2
def baseEnd_1806442 : Nat := 15268691694968337795347

theorem tailTrace_1806442 : CollatzResearch.WordTrace tailWord_1806442 prefixEnd_1806442 15268691694968337795347 := by
  unfold tailWord_1806442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471588130394156144129395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43924235014384416384345053 16471588130394156144129395)
  ·
    refine ⟨24707382195591234216194093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16471588130394156144129395 24707382195591234216194093)
    ·
      refine ⟨9265268323346712831072785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24707382195591234216194093 9265268323346712831072785)
      ·
        refine ⟨6948951242510034623304589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9265268323346712831072785 6948951242510034623304589)
        ·
          refine ⟨2605856715941262983739221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6948951242510034623304589 2605856715941262983739221)
          ·
            refine ⟨15268691694968337795347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2605856715941262983739221 15268691694968337795347)
            ·
              rfl

theorem cell21_1806442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 9].length) (baseStart_1806442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806442 prefixEnd_1806442 := by exact prefixLift 1806442
  have htrace : WordTrace (prefixWord ++ tailWord_1806442) baseStart_1806442 baseEnd_1806442 := by
    simpa [prefixWord, tailWord_1806442, baseEnd_1806442] using wordTrace_append hprefix tailTrace_1806442
  have hstable : (prefixWord ++ tailWord_1806442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806442).length < 2 ^ (prefixWord ++ tailWord_1806442).sum := by decide
  have hdescent : baseEnd_1806442 < baseStart_1806442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806456 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_1806456 : Nat := 118140960795 + 1806456 * 2 ^ 59
def prefixEnd_1806456 : Nat := 4983230072969 + 3 ^ 40 * 1806456 * 2
def baseEnd_1806456 : Nat := 412257870754884207241007

theorem tailTrace_1806456 : CollatzResearch.WordTrace tailWord_1806456 prefixEnd_1806456 412257870754884207241007 := by
  unfold tailWord_1806456
  simp only [CollatzResearch.WordTrace]
  refine ⟨32943431571762952483763611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43924575429017269978351481 32943431571762952483763611)
  ·
    refine ⟨49415147357644428725645417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32943431571762952483763611 49415147357644428725645417)
    ·
      refine ⟨37061360518233321544234063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49415147357644428725645417 37061360518233321544234063)
      ·
        refine ⟨55592040777349982316351095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37061360518233321544234063 55592040777349982316351095)
        ·
          refine ⟨83388061166024973474526643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55592040777349982316351095 83388061166024973474526643)
          ·
            refine ⟨125082091749037460211789965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83388061166024973474526643 125082091749037460211789965)
            ·
              refine ⟨46905784405889047579421237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125082091749037460211789965 46905784405889047579421237)
              ·
                refine ⟨4397417288052098210570741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46905784405889047579421237 4397417288052098210570741)
                ·
                  refine ⟨412257870754884207241007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4397417288052098210570741 412257870754884207241007)
                  ·
                    rfl

theorem cell21_1806456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_1806456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806456 prefixEnd_1806456 := by exact prefixLift 1806456
  have htrace : WordTrace (prefixWord ++ tailWord_1806456) baseStart_1806456 baseEnd_1806456 := by
    simpa [prefixWord, tailWord_1806456, baseEnd_1806456] using wordTrace_append hprefix tailTrace_1806456
  have hstable : (prefixWord ++ tailWord_1806456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806456).length < 2 ^ (prefixWord ++ tailWord_1806456).sum := by decide
  have hdescent : baseEnd_1806456 < baseStart_1806456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806501 : List Nat := [1, 3, 1, 2, 1, 3, 10]
def baseStart_1806501 : Nat := 118140960795 + 1806501 * 2 ^ 59
def prefixEnd_1806501 : Nat := 4983230072969 + 3 ^ 40 * 1806501 * 2
def baseEnd_1806501 : Nat := 45807571151997125443435

theorem tailTrace_1806501 : CollatzResearch.WordTrace tailWord_1806501 prefixEnd_1806501 45807571151997125443435 := by
  unfold tailWord_1806501
  simp only [CollatzResearch.WordTrace]
  refine ⟨65888504428362877652915357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43925669618908585101943571 65888504428362877652915357)
  ·
    refine ⟨24708189160636079119843259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65888504428362877652915357 24708189160636079119843259)
    ·
      refine ⟨37062283740954118679764889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24708189160636079119843259 37062283740954118679764889)
      ·
        refine ⟨27796712805715589009823667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37062283740954118679764889 27796712805715589009823667)
        ·
          refine ⟨41695069208573383514735501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27796712805715589009823667 41695069208573383514735501)
          ·
            refine ⟨15635650953215018818025813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41695069208573383514735501 15635650953215018818025813)
            ·
              refine ⟨45807571151997125443435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15635650953215018818025813 45807571151997125443435)
              ·
                rfl

theorem cell21_1806501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 10].length) (baseStart_1806501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806501 prefixEnd_1806501 := by exact prefixLift 1806501
  have htrace : WordTrace (prefixWord ++ tailWord_1806501) baseStart_1806501 baseEnd_1806501 := by
    simpa [prefixWord, tailWord_1806501, baseEnd_1806501] using wordTrace_append hprefix tailTrace_1806501
  have hstable : (prefixWord ++ tailWord_1806501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806501).length < 2 ^ (prefixWord ++ tailWord_1806501).sum := by decide
  have hdescent : baseEnd_1806501 < baseStart_1806501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806577 : List Nat := [1, 2, 2, 2, 2, 1, 3, 8]
def baseStart_1806577 : Nat := 118140960795 + 1806577 * 2 ^ 59
def prefixEnd_1806577 : Nat := 4983230072969 + 3 ^ 40 * 1806577 * 2
def baseEnd_1806577 : Nat := 137428494867804961908031

theorem tailTrace_1806577 : CollatzResearch.WordTrace tailWord_1806577 prefixEnd_1806577 137428494867804961908031 := by
  unfold tailWord_1806577
  simp only [CollatzResearch.WordTrace]
  refine ⟨65891276376087542632681985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43927517584058361755121323 65891276376087542632681985)
  ·
    refine ⟨49418457282065656974511489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65891276376087542632681985 49418457282065656974511489)
    ·
      refine ⟨37063842961549242730883617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49418457282065656974511489 37063842961549242730883617)
      ·
        refine ⟨27797882221161932048162713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37063842961549242730883617 27797882221161932048162713)
        ·
          refine ⟨20848411665871449036122035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27797882221161932048162713 20848411665871449036122035)
          ·
            refine ⟨31272617498807173554183053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20848411665871449036122035 31272617498807173554183053)
            ·
              refine ⟨11727231562052690082818645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31272617498807173554183053 11727231562052690082818645)
              ·
                refine ⟨137428494867804961908031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11727231562052690082818645 137428494867804961908031)
                ·
                  rfl

theorem cell21_1806577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_1806577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806577 prefixEnd_1806577 := by exact prefixLift 1806577
  have htrace : WordTrace (prefixWord ++ tailWord_1806577) baseStart_1806577 baseEnd_1806577 := by
    simpa [prefixWord, tailWord_1806577, baseEnd_1806577] using wordTrace_append hprefix tailTrace_1806577
  have hstable : (prefixWord ++ tailWord_1806577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806577).length < 2 ^ (prefixWord ++ tailWord_1806577).sum := by decide
  have hdescent : baseEnd_1806577 < baseStart_1806577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806639 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_1806639 : Nat := 118140960795 + 1806639 * 2 ^ 59
def prefixEnd_1806639 : Nat := 4983230072969 + 3 ^ 40 * 1806639 * 2
def baseEnd_1806639 : Nat := 412299633848116555690633

theorem tailTrace_1806639 : CollatzResearch.WordTrace tailWord_1806639 prefixEnd_1806639 412299633848116555690633 := by
  unfold tailWord_1806639
  simp only [CollatzResearch.WordTrace]
  refine ⟨65893537701862927221438971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43929025134575284814292647 65893537701862927221438971)
  ·
    refine ⟨98840306552794390832158457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65893537701862927221438971 98840306552794390832158457)
    ·
      refine ⟨74130229914595793124118843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98840306552794390832158457 74130229914595793124118843)
      ·
        refine ⟨111195344871893689686178265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74130229914595793124118843 111195344871893689686178265)
        ·
          refine ⟨83396508653920267264633699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111195344871893689686178265 83396508653920267264633699)
          ·
            refine ⟨125094762980880400896950549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83396508653920267264633699 125094762980880400896950549)
            ·
              refine ⟨5863817014728768792044557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125094762980880400896950549 5863817014728768792044557)
              ·
                refine ⟨2198931380523288297016709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863817014728768792044557 2198931380523288297016709)
                ·
                  refine ⟨412299633848116555690633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198931380523288297016709 412299633848116555690633)
                  ·
                    rfl

theorem cell21_1806639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_1806639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806639 prefixEnd_1806639 := by exact prefixLift 1806639
  have htrace : WordTrace (prefixWord ++ tailWord_1806639) baseStart_1806639 baseEnd_1806639 := by
    simpa [prefixWord, tailWord_1806639, baseEnd_1806639] using wordTrace_append hprefix tailTrace_1806639
  have hstable : (prefixWord ++ tailWord_1806639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806639).length < 2 ^ (prefixWord ++ tailWord_1806639).sum := by decide
  have hdescent : baseEnd_1806639 < baseStart_1806639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806729 : List Nat := [1, 2, 1, 1, 6, 1, 9]
def baseStart_1806729 : Nat := 118140960795 + 1806729 * 2 ^ 59
def prefixEnd_1806729 : Nat := 4983230072969 + 3 ^ 40 * 1806729 * 2
def baseEnd_1806729 : Nat := 45813352563810711021161

theorem tailTrace_1806729 : CollatzResearch.WordTrace tailWord_1806729 prefixEnd_1806729 45813352563810711021161 := by
  unfold tailWord_1806729
  simp only [CollatzResearch.WordTrace]
  refine ⟨65896820271536872592215241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43931213514357915061476827 65896820271536872592215241)
  ·
    refine ⟨49422615203652654444161431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65896820271536872592215241 49422615203652654444161431)
    ·
      refine ⟨74133922805478981666242147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49422615203652654444161431 74133922805478981666242147)
      ·
        refine ⟨111200884208218472499363221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74133922805478981666242147 111200884208218472499363221)
        ·
          refine ⟨5212541447260240898407651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111200884208218472499363221 5212541447260240898407651)
          ·
            refine ⟨7818812170890361347611477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212541447260240898407651 7818812170890361347611477)
            ·
              refine ⟨45813352563810711021161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7818812170890361347611477 45813352563810711021161)
              ·
                rfl

theorem cell21_1806729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 9].length) (baseStart_1806729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806729 prefixEnd_1806729 := by exact prefixLift 1806729
  have htrace : WordTrace (prefixWord ++ tailWord_1806729) baseStart_1806729 baseEnd_1806729 := by
    simpa [prefixWord, tailWord_1806729, baseEnd_1806729] using wordTrace_append hprefix tailTrace_1806729
  have hstable : (prefixWord ++ tailWord_1806729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806729).length < 2 ^ (prefixWord ++ tailWord_1806729).sum := by decide
  have hdescent : baseEnd_1806729 < baseStart_1806729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806746 : List Nat := [3, 1, 1, 4, 1, 3, 2, 6]
def baseStart_1806746 : Nat := 118140960795 + 1806746 * 2 ^ 59
def prefixEnd_1806746 : Nat := 4983230072969 + 3 ^ 40 * 1806746 * 2
def baseEnd_1806746 : Nat := 137441350901969382469027

theorem tailTrace_1806746 : CollatzResearch.WordTrace tailWord_1806746 prefixEnd_1806746 137441350901969382469027 := by
  unfold tailWord_1806746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474360078118821123896023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43931626874983522997056061 16474360078118821123896023)
  ·
    refine ⟨24711540117178231685844035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16474360078118821123896023 24711540117178231685844035)
    ·
      refine ⟨37067310175767347528766053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24711540117178231685844035 37067310175767347528766053)
      ·
        refine ⟨6950120657956377661643635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37067310175767347528766053 6950120657956377661643635)
        ·
          refine ⟨10425180986934566492465453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950120657956377661643635 10425180986934566492465453)
          ·
            refine ⟨3909442870100462434674545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10425180986934566492465453 3909442870100462434674545)
            ·
              refine ⟨2932082152575346826005909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909442870100462434674545 2932082152575346826005909)
              ·
                refine ⟨137441350901969382469027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2932082152575346826005909 137441350901969382469027)
                ·
                  rfl

theorem cell21_1806746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_1806746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806746 prefixEnd_1806746 := by exact prefixLift 1806746
  have htrace : WordTrace (prefixWord ++ tailWord_1806746) baseStart_1806746 baseEnd_1806746 := by
    simpa [prefixWord, tailWord_1806746, baseEnd_1806746] using wordTrace_append hprefix tailTrace_1806746
  have hstable : (prefixWord ++ tailWord_1806746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806746).length < 2 ^ (prefixWord ++ tailWord_1806746).sum := by decide
  have hdescent : baseEnd_1806746 < baseStart_1806746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806791 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_1806791 : Nat := 118140960795 + 1806791 * 2 ^ 59
def prefixEnd_1806791 : Nat := 4983230072969 + 3 ^ 40 * 1806791 * 2
def baseEnd_1806791 : Nat := 412334322318998069156989

theorem tailTrace_1806791 : CollatzResearch.WordTrace tailWord_1806791 prefixEnd_1806791 412334322318998069156989 := by
  unfold tailWord_1806791
  simp only [CollatzResearch.WordTrace]
  refine ⟨65899081597312257180972227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43932721064874838120648151 65899081597312257180972227)
  ·
    refine ⟨98848622395968385771458341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65899081597312257180972227 98848622395968385771458341)
    ·
      refine ⟨18534116699244072332148439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98848622395968385771458341 18534116699244072332148439)
      ·
        refine ⟨27801175048866108498222659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534116699244072332148439 27801175048866108498222659)
        ·
          refine ⟨41701762573299162747333989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27801175048866108498222659 41701762573299162747333989)
          ·
            refine ⟨7819080482493593015125123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41701762573299162747333989 7819080482493593015125123)
            ·
              refine ⟨11728620723740389522687685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819080482493593015125123 11728620723740389522687685)
              ·
                refine ⟨2199116385701323035503941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11728620723740389522687685 2199116385701323035503941)
                ·
                  refine ⟨412334322318998069156989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199116385701323035503941 412334322318998069156989)
                  ·
                    rfl

theorem cell21_1806791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_1806791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806791 prefixEnd_1806791 := by exact prefixLift 1806791
  have htrace : WordTrace (prefixWord ++ tailWord_1806791) baseStart_1806791 baseEnd_1806791 := by
    simpa [prefixWord, tailWord_1806791, baseEnd_1806791] using wordTrace_append hprefix tailTrace_1806791
  have hstable : (prefixWord ++ tailWord_1806791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806791).length < 2 ^ (prefixWord ++ tailWord_1806791).sum := by decide
  have hdescent : baseEnd_1806791 < baseStart_1806791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806853 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 3]
def baseStart_1806853 : Nat := 118140960795 + 1806853 * 2 ^ 59
def prefixEnd_1806853 : Nat := 4983230072969 + 3 ^ 40 * 1806853 * 2
def baseEnd_1806853 : Nat := 412348471563699739123529

theorem tailTrace_1806853 : CollatzResearch.WordTrace tailWord_1806853 prefixEnd_1806853 412348471563699739123529 := by
  unfold tailWord_1806853
  simp only [CollatzResearch.WordTrace]
  refine ⟨65901342923087641769729213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43934228615391761179819475 65901342923087641769729213)
  ·
    refine ⟨24713003596157865663648455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65901342923087641769729213 24713003596157865663648455)
    ·
      refine ⟨37069505394236798495472683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713003596157865663648455 37069505394236798495472683)
      ·
        refine ⟨55604258091355197743209025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37069505394236798495472683 55604258091355197743209025)
        ·
          refine ⟨41703193568516398307406769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55604258091355197743209025 41703193568516398307406769)
          ·
            refine ⟨31277395176387298730555077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41703193568516398307406769 31277395176387298730555077)
            ·
              refine ⟨5864511595572618511979077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31277395176387298730555077 5864511595572618511979077)
              ·
                refine ⟨1099595924169865970996077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5864511595572618511979077 1099595924169865970996077)
                ·
                  refine ⟨412348471563699739123529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099595924169865970996077 412348471563699739123529)
                  ·
                    rfl

theorem cell21_1806853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_1806853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806853 prefixEnd_1806853 := by exact prefixLift 1806853
  have htrace : WordTrace (prefixWord ++ tailWord_1806853) baseStart_1806853 baseEnd_1806853 := by
    simpa [prefixWord, tailWord_1806853, baseEnd_1806853] using wordTrace_append hprefix tailTrace_1806853
  have hstable : (prefixWord ++ tailWord_1806853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806853).length < 2 ^ (prefixWord ++ tailWord_1806853).sum := by decide
  have hdescent : baseEnd_1806853 < baseStart_1806853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806881 : List Nat := [1, 2, 3, 2, 2, 1, 3, 7]
def baseStart_1806881 : Nat := 118140960795 + 1806881 * 2 ^ 59
def prefixEnd_1806881 : Nat := 4983230072969 + 3 ^ 40 * 1806881 * 2
def baseEnd_1806881 : Nat := 137451620515059304218935

theorem tailTrace_1806881 : CollatzResearch.WordTrace tailWord_1806881 prefixEnd_1806881 137451620515059304218935 := by
  unfold tailWord_1806881
  simp only [CollatzResearch.WordTrace]
  refine ⟨65902364166986202551748497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43934909444657468367832331 65902364166986202551748497)
  ·
    refine ⟨49426773125239651913811373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65902364166986202551748497 49426773125239651913811373)
    ·
      refine ⟨18535039921964869467679265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49426773125239651913811373 18535039921964869467679265)
      ·
        refine ⟨13901279941473652100759449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18535039921964869467679265 13901279941473652100759449)
        ·
          refine ⟨10425959956105239075569587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13901279941473652100759449 10425959956105239075569587)
          ·
            refine ⟨15638939934157858613354381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425959956105239075569587 15638939934157858613354381)
            ·
              refine ⟨5864602475309196980007893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15638939934157858613354381 5864602475309196980007893)
              ·
                refine ⟨137451620515059304218935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5864602475309196980007893 137451620515059304218935)
                ·
                  rfl

theorem cell21_1806881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_1806881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806881 prefixEnd_1806881 := by exact prefixLift 1806881
  have htrace : WordTrace (prefixWord ++ tailWord_1806881) baseStart_1806881 baseEnd_1806881 := by
    simpa [prefixWord, tailWord_1806881, baseEnd_1806881] using wordTrace_append hprefix tailTrace_1806881
  have hstable : (prefixWord ++ tailWord_1806881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806881).length < 2 ^ (prefixWord ++ tailWord_1806881).sum := by decide
  have hdescent : baseEnd_1806881 < baseStart_1806881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806912 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_1806912 : Nat := 118140960795 + 1806912 * 2 ^ 59
def prefixEnd_1806912 : Nat := 4983230072969 + 3 ^ 40 * 1806912 * 2
def baseEnd_1806912 : Nat := 412361936167528747640075

theorem tailTrace_1806912 : CollatzResearch.WordTrace tailWord_1806912 prefixEnd_1806912 412361936167528747640075 := by
  unfold tailWord_1806912
  simp only [CollatzResearch.WordTrace]
  refine ⟨32951747414936947423063495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43935663219915929897417993 32951747414936947423063495)
  ·
    refine ⟨49427621122405421134595243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32951747414936947423063495 49427621122405421134595243)
    ·
      refine ⟨74141431683608131701892865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49427621122405421134595243 74141431683608131701892865)
      ·
        refine ⟨55606073762706098776419649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74141431683608131701892865 55606073762706098776419649)
        ·
          refine ⟨41704555322029574082314737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55606073762706098776419649 41704555322029574082314737)
          ·
            refine ⟨31278416491522180561736053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41704555322029574082314737 31278416491522180561736053)
            ·
              refine ⟨2932351546080204427662755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31278416491522180561736053 2932351546080204427662755)
              ·
                refine ⟨4398527319120306641494133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932351546080204427662755 4398527319120306641494133)
                ·
                  refine ⟨412361936167528747640075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398527319120306641494133 412361936167528747640075)
                  ·
                    rfl

theorem cell21_1806912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_1806912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806912 prefixEnd_1806912 := by exact prefixLift 1806912
  have htrace : WordTrace (prefixWord ++ tailWord_1806912) baseStart_1806912 baseEnd_1806912 := by
    simpa [prefixWord, tailWord_1806912, baseEnd_1806912] using wordTrace_append hprefix tailTrace_1806912
  have hstable : (prefixWord ++ tailWord_1806912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806912).length < 2 ^ (prefixWord ++ tailWord_1806912).sum := by decide
  have hdescent : baseEnd_1806912 < baseStart_1806912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806918 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1806918 : Nat := 118140960795 + 1806918 * 2 ^ 59
def prefixEnd_1806918 : Nat := 4983230072969 + 3 ^ 40 * 1806918 * 2
def baseEnd_1806918 : Nat := 412363305449274070540063

theorem tailTrace_1806918 : CollatzResearch.WordTrace tailWord_1806918 prefixEnd_1806918 412363305449274070540063 := by
  unfold tailWord_1806918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059491052120379933463919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43935809111901438580563605 2059491052120379933463919)
  ·
    refine ⟨3089236578180569900195879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2059491052120379933463919 3089236578180569900195879)
    ·
      refine ⟨4633854867270854850293819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089236578180569900195879 4633854867270854850293819)
      ·
        refine ⟨6950782300906282275440729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633854867270854850293819 6950782300906282275440729)
        ·
          refine ⟨5213086725679711706580547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6950782300906282275440729 5213086725679711706580547)
          ·
            refine ⟨7819630088519567559870821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213086725679711706580547 7819630088519567559870821)
            ·
              refine ⟨1466180641597418917475779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7819630088519567559870821 1466180641597418917475779)
              ·
                refine ⟨2199270962396128376213669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466180641597418917475779 2199270962396128376213669)
                ·
                  refine ⟨412363305449274070540063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199270962396128376213669 412363305449274070540063)
                  ·
                    rfl

theorem cell21_1806918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1806918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806918 prefixEnd_1806918 := by exact prefixLift 1806918
  have htrace : WordTrace (prefixWord ++ tailWord_1806918) baseStart_1806918 baseEnd_1806918 := by
    simpa [prefixWord, tailWord_1806918, baseEnd_1806918] using wordTrace_append hprefix tailTrace_1806918
  have hstable : (prefixWord ++ tailWord_1806918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806918).length < 2 ^ (prefixWord ++ tailWord_1806918).sum := by decide
  have hdescent : baseEnd_1806918 < baseStart_1806918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806957 : List Nat := [1, 5, 1, 1, 3, 10]
def baseStart_1806957 : Nat := 118140960795 + 1806957 * 2 ^ 59
def prefixEnd_1806957 : Nat := 4983230072969 + 3 ^ 40 * 1806957 * 2
def baseEnd_1806957 : Nat := 15273044658541432199629

theorem tailTrace_1806957 : CollatzResearch.WordTrace tailWord_1806957 prefixEnd_1806957 15273044658541432199629 := by
  unfold tailWord_1806957
  simp only [CollatzResearch.WordTrace]
  refine ⟨65905136114710867531515125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43936757409807245021010083 65905136114710867531515125)
  ·
    refine ⟨6178606510754143831079543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65905136114710867531515125 6178606510754143831079543)
    ·
      refine ⟨9267909766131215746619315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6178606510754143831079543 9267909766131215746619315)
      ·
        refine ⟨13901864649196823619928973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9267909766131215746619315 13901864649196823619928973)
        ·
          refine ⟨5213199243448808857473365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13901864649196823619928973 5213199243448808857473365)
          ·
            refine ⟨15273044658541432199629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5213199243448808857473365 15273044658541432199629)
            ·
              rfl

theorem cell21_1806957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 10].length) (baseStart_1806957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806957 prefixEnd_1806957 := by exact prefixLift 1806957
  have htrace : WordTrace (prefixWord ++ tailWord_1806957) baseStart_1806957 baseEnd_1806957 := by
    simpa [prefixWord, tailWord_1806957, baseEnd_1806957] using wordTrace_append hprefix tailTrace_1806957
  have hstable : (prefixWord ++ tailWord_1806957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806957).length < 2 ^ (prefixWord ++ tailWord_1806957).sum := by decide
  have hdescent : baseEnd_1806957 < baseStart_1806957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806960 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_1806960 : Nat := 118140960795 + 1806960 * 2 ^ 59
def prefixEnd_1806960 : Nat := 4983230072969 + 3 ^ 40 * 1806960 * 2
def baseEnd_1806960 : Nat := 412372890421491330839977

theorem tailTrace_1806960 : CollatzResearch.WordTrace tailWord_1806960 prefixEnd_1806960 412372890421491330839977 := by
  unfold tailWord_1806960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952622766849999521937167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43936830355799999362582889 32952622766849999521937167)
  ·
    refine ⟨49428934150274999282905751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32952622766849999521937167 49428934150274999282905751)
    ·
      refine ⟨74143401225412498924358627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49428934150274999282905751 74143401225412498924358627)
      ·
        refine ⟨111215101838118748386537941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74143401225412498924358627 111215101838118748386537941)
        ·
          refine ⟨2606603949330908165309483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 111215101838118748386537941 2606603949330908165309483)
          ·
            refine ⟨3909905923996362247964225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606603949330908165309483 3909905923996362247964225)
            ·
              refine ⟨2932429442997271685973169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909905923996362247964225 2932429442997271685973169)
              ·
                refine ⟨2199322082247953764479877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2932429442997271685973169 2199322082247953764479877)
                ·
                  refine ⟨412372890421491330839977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199322082247953764479877 412372890421491330839977)
                  ·
                    rfl

theorem cell21_1806960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_1806960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1806960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1806960 prefixEnd_1806960 := by exact prefixLift 1806960
  have htrace : WordTrace (prefixWord ++ tailWord_1806960) baseStart_1806960 baseEnd_1806960 := by
    simpa [prefixWord, tailWord_1806960, baseEnd_1806960] using wordTrace_append hprefix tailTrace_1806960
  have hstable : (prefixWord ++ tailWord_1806960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806960).length < 2 ^ (prefixWord ++ tailWord_1806960).sum := by decide
  have hdescent : baseEnd_1806960 < baseStart_1806960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807005 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1807005 : Nat := 118140960795 + 1807005 * 2 ^ 59
def prefixEnd_1807005 : Nat := 4983230072969 + 3 ^ 40 * 1807005 * 2
def baseEnd_1807005 : Nat := 412383160034581252589885

theorem tailTrace_1807005 : CollatzResearch.WordTrace tailWord_1807005 prefixEnd_1807005 412383160034581252589885 := by
  unfold tailWord_1807005
  simp only [CollatzResearch.WordTrace]
  refine ⟨65906886818536971729262469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43937924545691314486174979 65906886818536971729262469)
  ·
    refine ⟨12357541278475682199236713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65906886818536971729262469 12357541278475682199236713)
    ·
      refine ⟨9268155958856761649427535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12357541278475682199236713 9268155958856761649427535)
      ·
        refine ⟨13902233938285142474141303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268155958856761649427535 13902233938285142474141303)
        ·
          refine ⟨20853350907427713711211955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902233938285142474141303 20853350907427713711211955)
          ·
            refine ⟨31280026361141570566817933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20853350907427713711211955 31280026361141570566817933)
            ·
              refine ⟨11730009885428088962556725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31280026361141570566817933 11730009885428088962556725)
              ·
                refine ⟨1099688426758883340239693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11730009885428088962556725 1099688426758883340239693)
                ·
                  refine ⟨412383160034581252589885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099688426758883340239693 412383160034581252589885)
                  ·
                    rfl

theorem cell21_1807005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1807005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807005 prefixEnd_1807005 := by exact prefixLift 1807005
  have htrace : WordTrace (prefixWord ++ tailWord_1807005) baseStart_1807005 baseEnd_1807005 := by
    simpa [prefixWord, tailWord_1807005, baseEnd_1807005] using wordTrace_append hprefix tailTrace_1807005
  have hstable : (prefixWord ++ tailWord_1807005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807005).length < 2 ^ (prefixWord ++ tailWord_1807005).sum := by decide
  have hdescent : baseEnd_1807005 < baseStart_1807005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807022 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1807022 : Nat := 118140960795 + 1807022 * 2 ^ 59
def prefixEnd_1807022 : Nat := 4983230072969 + 3 ^ 40 * 1807022 * 2
def baseEnd_1807022 : Nat := 412387039666193000806517

theorem tailTrace_1807022 : CollatzResearch.WordTrace tailWord_1807022 prefixEnd_1807022 412387039666193000806517 := by
  unfold tailWord_1807022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8238438357434422954078915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43938337906316922421754213 8238438357434422954078915)
  ·
    refine ⟨12357657536151634431118373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8238438357434422954078915 12357657536151634431118373)
    ·
      refine ⟨2317060788028431455834695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12357657536151634431118373 2317060788028431455834695)
      ·
        refine ⟨3475591182042647183752043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317060788028431455834695 3475591182042647183752043)
        ·
          refine ⟨5213386773063970775628065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475591182042647183752043 5213386773063970775628065)
          ·
            refine ⟨3910040079797978081721049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5213386773063970775628065 3910040079797978081721049)
            ·
              refine ⟨2932530059848483561290787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910040079797978081721049 2932530059848483561290787)
              ·
                refine ⟨4398795089772725341936181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932530059848483561290787 4398795089772725341936181)
                ·
                  refine ⟨412387039666193000806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398795089772725341936181 412387039666193000806517)
                  ·
                    rfl

theorem cell21_1807022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1807022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807022 prefixEnd_1807022 := by exact prefixLift 1807022
  have htrace : WordTrace (prefixWord ++ tailWord_1807022) baseStart_1807022 baseEnd_1807022 := by
    simpa [prefixWord, tailWord_1807022, baseEnd_1807022] using wordTrace_append hprefix tailTrace_1807022
  have hstable : (prefixWord ++ tailWord_1807022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807022).length < 2 ^ (prefixWord ++ tailWord_1807022).sum := by decide
  have hdescent : baseEnd_1807022 < baseStart_1807022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807036 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_1807036 : Nat := 118140960795 + 1807036 * 2 ^ 59
def prefixEnd_1807036 : Nat := 4983230072969 + 3 ^ 40 * 1807036 * 2
def baseEnd_1807036 : Nat := 412390234656932087573155

theorem tailTrace_1807036 : CollatzResearch.WordTrace tailWord_1807036 prefixEnd_1807036 412390234656932087573155 := by
  unfold tailWord_1807036
  simp only [CollatzResearch.WordTrace]
  refine ⟨32954008740712332011820481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43938678320949776015760641 32954008740712332011820481)
  ·
    refine ⟨24715506555534249008865361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32954008740712332011820481 24715506555534249008865361)
    ·
      refine ⟨18536629916650686756649021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24715506555534249008865361 18536629916650686756649021)
      ·
        refine ⟨6951236218744007533743383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18536629916650686756649021 6951236218744007533743383)
        ·
          refine ⟨10426854328116011300615075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951236218744007533743383 10426854328116011300615075)
          ·
            refine ⟨15640281492174016950922613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426854328116011300615075 15640281492174016950922613)
            ·
              refine ⟨1466276389891314089148995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15640281492174016950922613 1466276389891314089148995)
              ·
                refine ⟨2199414584836971133723493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466276389891314089148995 2199414584836971133723493)
                ·
                  refine ⟨412390234656932087573155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2199414584836971133723493 412390234656932087573155)
                  ·
                    rfl

theorem cell21_1807036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_1807036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807036 prefixEnd_1807036 := by exact prefixLift 1807036
  have htrace : WordTrace (prefixWord ++ tailWord_1807036) baseStart_1807036 baseEnd_1807036 := by
    simpa [prefixWord, tailWord_1807036, baseEnd_1807036] using wordTrace_append hprefix tailTrace_1807036
  have hstable : (prefixWord ++ tailWord_1807036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807036).length < 2 ^ (prefixWord ++ tailWord_1807036).sum := by decide
  have hdescent : baseEnd_1807036 < baseStart_1807036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807047 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_1807047 : Nat := 118140960795 + 1807047 * 2 ^ 59
def prefixEnd_1807047 : Nat := 4983230072969 + 3 ^ 40 * 1807047 * 2
def baseEnd_1807047 : Nat := 412392745006798512889799

theorem tailTrace_1807047 : CollatzResearch.WordTrace tailWord_1807047 prefixEnd_1807047 412392745006798512889799 := by
  unfold tailWord_1807047
  simp only [CollatzResearch.WordTrace]
  refine ⟨65908418684384812902291395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43938945789589875268194263 65908418684384812902291395)
  ·
    refine ⟨98862628026577219353437093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65908418684384812902291395 98862628026577219353437093)
    ·
      refine ⟨18536742754983228628769455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98862628026577219353437093 18536742754983228628769455)
      ·
        refine ⟨27805114132474842943154183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18536742754983228628769455 27805114132474842943154183)
        ·
          refine ⟨41707671198712264414731275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27805114132474842943154183 41707671198712264414731275)
          ·
            refine ⟨62561506798068396622096913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41707671198712264414731275 62561506798068396622096913)
            ·
              refine ⟨46921130098551297466572685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62561506798068396622096913 46921130098551297466572685)
              ·
                refine ⟨17595423786956736549964757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46921130098551297466572685 17595423786956736549964757)
                ·
                  refine ⟨412392745006798512889799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17595423786956736549964757 412392745006798512889799)
                  ·
                    rfl

theorem cell21_1807047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_1807047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807047 prefixEnd_1807047 := by exact prefixLift 1807047
  have htrace : WordTrace (prefixWord ++ tailWord_1807047) baseStart_1807047 baseEnd_1807047 := by
    simpa [prefixWord, tailWord_1807047, baseEnd_1807047] using wordTrace_append hprefix tailTrace_1807047
  have hstable : (prefixWord ++ tailWord_1807047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807047).length < 2 ^ (prefixWord ++ tailWord_1807047).sum := by decide
  have hdescent : baseEnd_1807047 < baseStart_1807047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807050 : List Nat := [3, 1, 2, 1, 4, 1, 4, 5]
def baseStart_1807050 : Nat := 118140960795 + 1807050 * 2 ^ 59
def prefixEnd_1807050 : Nat := 4983230072969 + 3 ^ 40 * 1807050 * 2
def baseEnd_1807050 : Nat := 137464476549223724779931

theorem tailTrace_1807050 : CollatzResearch.WordTrace tailWord_1807050 prefixEnd_1807050 137464476549223724779931 := by
  unfold tailWord_1807050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477132025843486103662651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43939018735582629609767069 16477132025843486103662651)
  ·
    refine ⟨24715698038765229155493977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16477132025843486103662651 24715698038765229155493977)
    ·
      refine ⟨18536773529073921866620483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24715698038765229155493977 18536773529073921866620483)
      ·
        refine ⟨27805160293610882799930725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18536773529073921866620483 27805160293610882799930725)
        ·
          refine ⟨5213467555052040524987011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27805160293610882799930725 5213467555052040524987011)
          ·
            refine ⟨7820201332578060787480517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213467555052040524987011 7820201332578060787480517)
            ·
              refine ⟨1466287749858386397652597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7820201332578060787480517 1466287749858386397652597)
              ·
                refine ⟨137464476549223724779931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1466287749858386397652597 137464476549223724779931)
                ·
                  rfl

theorem cell21_1807050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_1807050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807050 prefixEnd_1807050 := by exact prefixLift 1807050
  have htrace : WordTrace (prefixWord ++ tailWord_1807050) baseStart_1807050 baseEnd_1807050 := by
    simpa [prefixWord, tailWord_1807050, baseEnd_1807050] using wordTrace_append hprefix tailTrace_1807050
  have hstable : (prefixWord ++ tailWord_1807050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807050).length < 2 ^ (prefixWord ++ tailWord_1807050).sum := by decide
  have hdescent : baseEnd_1807050 < baseStart_1807050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807168 : List Nat := [2, 1, 1, 2, 2, 1, 1, 11]
def baseStart_1807168 : Nat := 118140960795 + 1807168 * 2 ^ 59
def prefixEnd_1807168 : Nat := 4983230072969 + 3 ^ 40 * 1807168 * 2
def baseEnd_1807168 : Nat := 137473452951776397124295

theorem tailTrace_1807168 : CollatzResearch.WordTrace tailWord_1807168 prefixEnd_1807168 137473452951776397124295 := by
  unfold tailWord_1807168
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956415958473225283723079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43941887944630967044964105 32956415958473225283723079)
  ·
    refine ⟨49434623937709837925584619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32956415958473225283723079 49434623937709837925584619)
    ·
      refine ⟨74151935906564756888376929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49434623937709837925584619 74151935906564756888376929)
      ·
        refine ⟨55613951929923567666282697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74151935906564756888376929 55613951929923567666282697)
        ·
          refine ⟨41710463947442675749712023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55613951929923567666282697 41710463947442675749712023)
          ·
            refine ⟨62565695921164013624568035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41710463947442675749712023 62565695921164013624568035)
            ·
              refine ⟨93848543881746020436852053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62565695921164013624568035 93848543881746020436852053)
              ·
                refine ⟨137473452951776397124295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93848543881746020436852053 137473452951776397124295)
                ·
                  rfl

theorem cell21_1807168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_1807168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807168 prefixEnd_1807168 := by exact prefixLift 1807168
  have htrace : WordTrace (prefixWord ++ tailWord_1807168) baseStart_1807168 baseEnd_1807168 := by
    simpa [prefixWord, tailWord_1807168, baseEnd_1807168] using wordTrace_append hprefix tailTrace_1807168
  have hstable : (prefixWord ++ tailWord_1807168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807168).length < 2 ^ (prefixWord ++ tailWord_1807168).sum := by decide
  have hdescent : baseEnd_1807168 < baseStart_1807168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807185 : List Nat := [1, 2, 2, 1, 6, 1, 8]
def baseStart_1807185 : Nat := 118140960795 + 1807185 * 2 ^ 59
def prefixEnd_1807185 : Nat := 4983230072969 + 3 ^ 40 * 1807185 * 2
def baseEnd_1807185 : Nat := 45824915387437882176613

theorem tailTrace_1807185 : CollatzResearch.WordTrace tailWord_1807185 prefixEnd_1807185 45824915387437882176613 := by
  unfold tailWord_1807185
  simp only [CollatzResearch.WordTrace]
  refine ⟨65913451957884862470815009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43942301305256574980543339 65913451957884862470815009)
  ·
    refine ⟨49435088968413646853111257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65913451957884862470815009 49435088968413646853111257)
    ·
      refine ⟨37076316726310235139833443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49435088968413646853111257 37076316726310235139833443)
      ·
        refine ⟨55614475089465352709750165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37076316726310235139833443 55614475089465352709750165)
        ·
          refine ⟨2606928519818688408269539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55614475089465352709750165 2606928519818688408269539)
          ·
            refine ⟨3910392779728032612404309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606928519818688408269539 3910392779728032612404309)
            ·
              refine ⟨45824915387437882176613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3910392779728032612404309 45824915387437882176613)
              ·
                rfl

theorem cell21_1807185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 8].length) (baseStart_1807185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807185 prefixEnd_1807185 := by exact prefixLift 1807185
  have htrace : WordTrace (prefixWord ++ tailWord_1807185) baseStart_1807185 baseEnd_1807185 := by
    simpa [prefixWord, tailWord_1807185, baseEnd_1807185] using wordTrace_append hprefix tailTrace_1807185
  have hstable : (prefixWord ++ tailWord_1807185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807185).length < 2 ^ (prefixWord ++ tailWord_1807185).sum := by decide
  have hdescent : baseEnd_1807185 < baseStart_1807185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807244 : List Nat := [2, 2, 1, 2, 1, 2, 11]
def baseStart_1807244 : Nat := 118140960795 + 1807244 * 2 ^ 59
def prefixEnd_1807244 : Nat := 4983230072969 + 3 ^ 40 * 1807244 * 2
def baseEnd_1807244 : Nat := 45826411454529994234007

theorem tailTrace_1807244 : CollatzResearch.WordTrace tailWord_1807244 prefixEnd_1807244 45826411454529994234007 := by
  unfold tailWord_1807244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957801932335557773606393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43943735909780743698141857 32957801932335557773606393)
  ·
    refine ⟨24718351449251668330204795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32957801932335557773606393 24718351449251668330204795)
    ·
      refine ⟨37077527173877502495307193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24718351449251668330204795 37077527173877502495307193)
      ·
        refine ⟨27808145380408126871480395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37077527173877502495307193 27808145380408126871480395)
        ·
          refine ⟨41712218070612190307220593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27808145380408126871480395 41712218070612190307220593)
          ·
            refine ⟨31284163552959142730415445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41712218070612190307220593 31284163552959142730415445)
            ·
              refine ⟨45826411454529994234007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31284163552959142730415445 45826411454529994234007)
              ·
                rfl

theorem cell21_1807244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 11].length) (baseStart_1807244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807244 prefixEnd_1807244 := by exact prefixLift 1807244
  have htrace : WordTrace (prefixWord ++ tailWord_1807244) baseStart_1807244 baseEnd_1807244 := by
    simpa [prefixWord, tailWord_1807244, baseEnd_1807244] using wordTrace_append hprefix tailTrace_1807244
  have hstable : (prefixWord ++ tailWord_1807244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807244).length < 2 ^ (prefixWord ++ tailWord_1807244).sum := by decide
  have hdescent : baseEnd_1807244 < baseStart_1807244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807250 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1807250 : Nat := 118140960795 + 1807250 * 2 ^ 59
def prefixEnd_1807250 : Nat := 4983230072969 + 3 ^ 40 * 1807250 * 2
def baseEnd_1807250 : Nat := 412439072372515271006051

theorem tailTrace_1807250 : CollatzResearch.WordTrace tailWord_1807250 prefixEnd_1807250 412439072372515271006051 := by
  unfold tailWord_1807250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16478955675662344642982801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43943881801766252381287469 16478955675662344642982801)
  ·
    refine ⟨12359216756746758482237101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16478955675662344642982801 12359216756746758482237101)
    ·
      refine ⟨4634706283780034430838913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12359216756746758482237101 4634706283780034430838913)
      ·
        refine ⟨3476029712835025823129185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634706283780034430838913 3476029712835025823129185)
        ·
          refine ⟨2607022284626269367346889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3476029712835025823129185 2607022284626269367346889)
          ·
            refine ⟨1955266713469702025510167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607022284626269367346889 1955266713469702025510167)
            ·
              refine ⟨2932900070204553038265251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955266713469702025510167 2932900070204553038265251)
              ·
                refine ⟨4399350105306829557397877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932900070204553038265251 4399350105306829557397877)
                ·
                  refine ⟨412439072372515271006051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4399350105306829557397877 412439072372515271006051)
                  ·
                    rfl

theorem cell21_1807250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1807250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807250 prefixEnd_1807250 := by exact prefixLift 1807250
  have htrace : WordTrace (prefixWord ++ tailWord_1807250) baseStart_1807250 baseEnd_1807250 := by
    simpa [prefixWord, tailWord_1807250, baseEnd_1807250] using wordTrace_append hprefix tailTrace_1807250
  have hstable : (prefixWord ++ tailWord_1807250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807250).length < 2 ^ (prefixWord ++ tailWord_1807250).sum := by decide
  have hdescent : baseEnd_1807250 < baseStart_1807250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807261 : List Nat := [1, 4, 2, 1, 2, 1, 4, 6]
def baseStart_1807261 : Nat := 118140960795 + 1807261 * 2 ^ 59
def prefixEnd_1807261 : Nat := 4983230072969 + 3 ^ 40 * 1807261 * 2
def baseEnd_1807261 : Nat := 137480527574127232107565

theorem tailTrace_1807261 : CollatzResearch.WordTrace tailWord_1807261 prefixEnd_1807261 137480527574127232107565 := by
  unfold tailWord_1807261
  simp only [CollatzResearch.WordTrace]
  refine ⟨65916223905609527450581637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43944149270406351633721091 65916223905609527450581637)
  ·
    refine ⟨12359291982301786396984057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65916223905609527450581637 12359291982301786396984057)
    ·
      refine ⟨9269468986726339797738043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12359291982301786396984057 9269468986726339797738043)
      ·
        refine ⟨13904203480089509696607065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269468986726339797738043 13904203480089509696607065)
        ·
          refine ⟨10428152610067132272455299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13904203480089509696607065 10428152610067132272455299)
          ·
            refine ⟨15642228915100698408682949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428152610067132272455299 15642228915100698408682949)
            ·
              refine ⟨2932917921581380951628053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15642228915100698408682949 2932917921581380951628053)
              ·
                refine ⟨137480527574127232107565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2932917921581380951628053 137480527574127232107565)
                ·
                  rfl

theorem cell21_1807261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_1807261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807261 prefixEnd_1807261 := by exact prefixLift 1807261
  have htrace : WordTrace (prefixWord ++ tailWord_1807261) baseStart_1807261 baseEnd_1807261 := by
    simpa [prefixWord, tailWord_1807261, baseEnd_1807261] using wordTrace_append hprefix tailTrace_1807261
  have hstable : (prefixWord ++ tailWord_1807261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807261).length < 2 ^ (prefixWord ++ tailWord_1807261).sum := by decide
  have hdescent : baseEnd_1807261 < baseStart_1807261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807368 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_1807368 : Nat := 118140960795 + 1807368 * 2 ^ 59
def prefixEnd_1807368 : Nat := 4983230072969 + 3 ^ 40 * 1807368 * 2
def baseEnd_1807368 : Nat := 412466001580173288039143

theorem tailTrace_1807368 : CollatzResearch.WordTrace tailWord_1807368 prefixEnd_1807368 412466001580173288039143 := by
  unfold tailWord_1807368
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960063258110942362363379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43946751010814589816484505 32960063258110942362363379)
  ·
    refine ⟨49440094887166413543545069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32960063258110942362363379 49440094887166413543545069)
    ·
      refine ⟨18540035582687405078829401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49440094887166413543545069 18540035582687405078829401)
      ·
        refine ⟨13905026687015553809122051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18540035582687405078829401 13905026687015553809122051)
        ·
          refine ⟨20857540030523330713683077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13905026687015553809122051 20857540030523330713683077)
          ·
            refine ⟨3910788755723124508815577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20857540030523330713683077 3910788755723124508815577)
            ·
              refine ⟨2933091566792343381611683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910788755723124508815577 2933091566792343381611683)
              ·
                refine ⟨4399637350188515072417525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933091566792343381611683 4399637350188515072417525)
                ·
                  refine ⟨412466001580173288039143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4399637350188515072417525 412466001580173288039143)
                  ·
                    rfl

theorem cell21_1807368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_1807368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807368 prefixEnd_1807368 := by exact prefixLift 1807368
  have htrace : WordTrace (prefixWord ++ tailWord_1807368) baseStart_1807368 baseEnd_1807368 := by
    simpa [prefixWord, tailWord_1807368, baseEnd_1807368] using wordTrace_append hprefix tailTrace_1807368
  have hstable : (prefixWord ++ tailWord_1807368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807368).length < 2 ^ (prefixWord ++ tailWord_1807368).sum := by decide
  have hdescent : baseEnd_1807368 < baseStart_1807368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807399 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_1807399 : Nat := 118140960795 + 1807399 * 2 ^ 59
def prefixEnd_1807399 : Nat := 4983230072969 + 3 ^ 40 * 1807399 * 2
def baseEnd_1807399 : Nat := 412473076202524123022413

theorem tailTrace_1807399 : CollatzResearch.WordTrace tailWord_1807399 prefixEnd_1807399 412473076202524123022413 := by
  unfold tailWord_1807399
  simp only [CollatzResearch.WordTrace]
  refine ⟨65921257179109577019105251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43947504786073051346070167 65921257179109577019105251)
  ·
    refine ⟨98881885768664365528657877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65921257179109577019105251 98881885768664365528657877)
    ·
      refine ⟨2317544197703071067077919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 98881885768664365528657877 2317544197703071067077919)
      ·
        refine ⟨3476316296554606600616879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317544197703071067077919 3476316296554606600616879)
        ·
          refine ⟨5214474444831909900925319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476316296554606600616879 5214474444831909900925319)
          ·
            refine ⟨7821711667247864851387979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214474444831909900925319 7821711667247864851387979)
            ·
              refine ⟨11732567500871797277081969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821711667247864851387979 11732567500871797277081969)
              ·
                refine ⟨8799425625653847957811477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11732567500871797277081969 8799425625653847957811477)
                ·
                  refine ⟨412473076202524123022413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8799425625653847957811477 412473076202524123022413)
                  ·
                    rfl

theorem cell21_1807399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_1807399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807399 prefixEnd_1807399 := by exact prefixLift 1807399
  have htrace : WordTrace (prefixWord ++ tailWord_1807399) baseStart_1807399 baseEnd_1807399 := by
    simpa [prefixWord, tailWord_1807399, baseEnd_1807399] using wordTrace_append hprefix tailTrace_1807399
  have hstable : (prefixWord ++ tailWord_1807399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807399).length < 2 ^ (prefixWord ++ tailWord_1807399).sum := by decide
  have hdescent : baseEnd_1807399 < baseStart_1807399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807430 : List Nat := [6, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1807430 : Nat := 118140960795 + 1807430 * 2 ^ 59
def prefixEnd_1807430 : Nat := 4983230072969 + 3 ^ 40 * 1807430 * 2
def baseEnd_1807430 : Nat := 137493383608291652668561

theorem tailTrace_1807430 : CollatzResearch.WordTrace tailWord_1807430 prefixEnd_1807430 137493383608291652668561 := by
  unfold tailWord_1807430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060074620062414666046367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43948258561331512875655829 2060074620062414666046367)
  ·
    refine ⟨3090111930093621999069551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060074620062414666046367 3090111930093621999069551)
    ·
      refine ⟨4635167895140432998604327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090111930093621999069551 4635167895140432998604327)
      ·
        refine ⟨6952751842710649497906491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635167895140432998604327 6952751842710649497906491)
        ·
          refine ⟨10429127764065974246859737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6952751842710649497906491 10429127764065974246859737)
          ·
            refine ⟨7821845823049480685144803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10429127764065974246859737 7821845823049480685144803)
            ·
              refine ⟨11732768734574221027717205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821845823049480685144803 11732768734574221027717205)
              ·
                refine ⟨137493383608291652668561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11732768734574221027717205 137493383608291652668561)
                ·
                  rfl

theorem cell21_1807430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1807430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807430 prefixEnd_1807430 := by exact prefixLift 1807430
  have htrace : WordTrace (prefixWord ++ tailWord_1807430) baseStart_1807430 baseEnd_1807430 := by
    simpa [prefixWord, tailWord_1807430, baseEnd_1807430] using wordTrace_append hprefix tailTrace_1807430
  have hstable : (prefixWord ++ tailWord_1807430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807430).length < 2 ^ (prefixWord ++ tailWord_1807430).sum := by decide
  have hdescent : baseEnd_1807430 < baseStart_1807430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807489 : List Nat := [1, 2, 4, 2, 2, 1, 3, 6]
def baseStart_1807489 : Nat := 118140960795 + 1807489 * 2 ^ 59
def prefixEnd_1807489 : Nat := 4983230072969 + 3 ^ 40 * 1807489 * 2
def baseEnd_1807489 : Nat := 137497871809567988840743

theorem tailTrace_1807489 : CollatzResearch.WordTrace tailWord_1807489 prefixEnd_1807489 137497871809567988840743 := by
  unfold tailWord_1807489
  simp only [CollatzResearch.WordTrace]
  refine ⟨65924539748783522389881521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43949693165855681593254347 65924539748783522389881521)
  ·
    refine ⟨49443404811587641792411141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65924539748783522389881521 49443404811587641792411141)
    ·
      refine ⟨9270638402172682836077089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49443404811587641792411141 9270638402172682836077089)
      ·
        refine ⟨6952978801629512127057817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9270638402172682836077089 6952978801629512127057817)
        ·
          refine ⟨5214734101222134095293363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6952978801629512127057817 5214734101222134095293363)
          ·
            refine ⟨7822101151833201142940045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214734101222134095293363 7822101151833201142940045)
            ·
              refine ⟨2933287931937450428602517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7822101151833201142940045 2933287931937450428602517)
              ·
                refine ⟨137497871809567988840743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2933287931937450428602517 137497871809567988840743)
                ·
                  rfl

theorem cell21_1807489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_1807489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807489 prefixEnd_1807489 := by exact prefixLift 1807489
  have htrace : WordTrace (prefixWord ++ tailWord_1807489) baseStart_1807489 baseEnd_1807489 := by
    simpa [prefixWord, tailWord_1807489, baseEnd_1807489] using wordTrace_append hprefix tailTrace_1807489
  have hstable : (prefixWord ++ tailWord_1807489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807489).length < 2 ^ (prefixWord ++ tailWord_1807489).sum := by decide
  have hdescent : baseEnd_1807489 < baseStart_1807489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807506 : List Nat := [3, 2, 3, 1, 1, 3, 3, 5]
def baseStart_1807506 : Nat := 118140960795 + 1807506 * 2 ^ 59
def prefixEnd_1807506 : Nat := 4983230072969 + 3 ^ 40 * 1807506 * 2
def baseEnd_1807506 : Nat := 137499165020105238246287

theorem tailTrace_1807506 : CollatzResearch.WordTrace tailWord_1807506 prefixEnd_1807506 137499165020105238246287 := by
  unfold tailWord_1807506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481289947430483573312593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43950106526481289528833581 16481289947430483573312593)
  ·
    refine ⟨12360967460572862679984445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16481289947430483573312593 12360967460572862679984445)
    ·
      refine ⟨4635362797714823504994167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12360967460572862679984445 4635362797714823504994167)
      ·
        refine ⟨6953044196572235257491251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635362797714823504994167 6953044196572235257491251)
        ·
          refine ⟨10429566294858352886236877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953044196572235257491251 10429566294858352886236877)
          ·
            refine ⟨3911087360571882332338829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10429566294858352886236877 3911087360571882332338829)
            ·
              refine ⟨1466657760214455874627061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911087360571882332338829 1466657760214455874627061)
              ·
                refine ⟨137499165020105238246287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1466657760214455874627061 137499165020105238246287)
                ·
                  rfl

theorem cell21_1807506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_1807506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807506 prefixEnd_1807506 := by exact prefixLift 1807506
  have htrace : WordTrace (prefixWord ++ tailWord_1807506) baseStart_1807506 baseEnd_1807506 := by
    simpa [prefixWord, tailWord_1807506, baseEnd_1807506] using wordTrace_append hprefix tailTrace_1807506
  have hstable : (prefixWord ++ tailWord_1807506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807506).length < 2 ^ (prefixWord ++ tailWord_1807506).sum := by decide
  have hdescent : baseEnd_1807506 < baseStart_1807506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807537 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 3]
def baseStart_1807537 : Nat := 118140960795 + 1807537 * 2 ^ 59
def prefixEnd_1807537 : Nat := 4983230072969 + 3 ^ 40 * 1807537 * 2
def baseEnd_1807537 : Nat := 412504569682666549722131

theorem tailTrace_1807537 : CollatzResearch.WordTrace tailWord_1807537 prefixEnd_1807537 412504569682666549722131 := by
  unfold tailWord_1807537
  simp only [CollatzResearch.WordTrace]
  refine ⟨65926290452609626587628865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43950860301739751058419243 65926290452609626587628865)
  ·
    refine ⟨49444717839457219940721649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65926290452609626587628865 49444717839457219940721649)
    ·
      refine ⟨37083538379592914955541237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49444717839457219940721649 37083538379592914955541237)
      ·
        refine ⟨3476581723086835777081991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37083538379592914955541237 3476581723086835777081991)
        ·
          refine ⟨5214872584630253665622987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476581723086835777081991 5214872584630253665622987)
          ·
            refine ⟨7822308876945380498434481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214872584630253665622987 7822308876945380498434481)
            ·
              refine ⟨5866731657709035373825861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7822308876945380498434481 5866731657709035373825861)
              ·
                refine ⟨1100012185820444132592349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5866731657709035373825861 1100012185820444132592349)
                ·
                  refine ⟨412504569682666549722131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100012185820444132592349 412504569682666549722131)
                  ·
                    rfl

theorem cell21_1807537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_1807537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807537 prefixEnd_1807537 := by exact prefixLift 1807537
  have htrace : WordTrace (prefixWord ++ tailWord_1807537) baseStart_1807537 baseEnd_1807537 := by
    simpa [prefixWord, tailWord_1807537, baseEnd_1807537] using wordTrace_append hprefix tailTrace_1807537
  have hstable : (prefixWord ++ tailWord_1807537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807537).length < 2 ^ (prefixWord ++ tailWord_1807537).sum := by decide
  have hdescent : baseEnd_1807537 < baseStart_1807537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807596 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_1807596 : Nat := 118140960795 + 1807596 * 2 ^ 59
def prefixEnd_1807596 : Nat := 4983230072969 + 3 ^ 40 * 1807596 * 2
def baseEnd_1807596 : Nat := 412518034286495558238677

theorem tailTrace_1807596 : CollatzResearch.WordTrace tailWord_1807596 prefixEnd_1807596 412518034286495558238677 := by
  unfold tailWord_1807596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32964221179697939832013321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43952294906263919776017761 32964221179697939832013321)
  ·
    refine ⟨24723165884773454874009991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32964221179697939832013321 24723165884773454874009991)
    ·
      refine ⟨37084748827160182311014987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24723165884773454874009991 37084748827160182311014987)
      ·
        refine ⟨55627123240740273466522481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37084748827160182311014987 55627123240740273466522481)
        ·
          refine ⟨41720342430555205099891861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55627123240740273466522481 41720342430555205099891861)
          ·
            refine ⟨1955641051432275239057431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41720342430555205099891861 1955641051432275239057431)
            ·
              refine ⟨2933461577148412858586147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955641051432275239057431 2933461577148412858586147)
              ·
                refine ⟨4400192365722619287879221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933461577148412858586147 4400192365722619287879221)
                ·
                  refine ⟨412518034286495558238677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4400192365722619287879221 412518034286495558238677)
                  ·
                    rfl

theorem cell21_1807596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_1807596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807596 prefixEnd_1807596 := by exact prefixLift 1807596
  have htrace : WordTrace (prefixWord ++ tailWord_1807596) baseStart_1807596 baseEnd_1807596 := by
    simpa [prefixWord, tailWord_1807596, baseEnd_1807596] using wordTrace_append hprefix tailTrace_1807596
  have hstable : (prefixWord ++ tailWord_1807596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807596).length < 2 ^ (prefixWord ++ tailWord_1807596).sum := by decide
  have hdescent : baseEnd_1807596 < baseStart_1807596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807610 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1807610 : Nat := 118140960795 + 1807610 * 2 ^ 59
def prefixEnd_1807610 : Nat := 4983230072969 + 3 ^ 40 * 1807610 * 2
def baseEnd_1807610 : Nat := 412521229277234645005315

theorem tailTrace_1807610 : CollatzResearch.WordTrace tailWord_1807610 prefixEnd_1807610 412521229277234645005315 := by
  unfold tailWord_1807610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482238245336290013759071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43952635320896773370024189 16482238245336290013759071)
  ·
    refine ⟨24723357368004435020638607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16482238245336290013759071 24723357368004435020638607)
    ·
      refine ⟨37085036052006652530957911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24723357368004435020638607 37085036052006652530957911)
      ·
        refine ⟨55627554078009978796436867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37085036052006652530957911 55627554078009978796436867)
        ·
          refine ⟨83441331117014968194655301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55627554078009978796436867 83441331117014968194655301)
          ·
            refine ⟨15645249584440306536497869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83441331117014968194655301 15645249584440306536497869)
            ·
              refine ⟨5866968594165114951186701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15645249584440306536497869 5866968594165114951186701)
              ·
                refine ⟨2200113222811918106695013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5866968594165114951186701 2200113222811918106695013)
                ·
                  refine ⟨412521229277234645005315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200113222811918106695013 412521229277234645005315)
                  ·
                    rfl

theorem cell21_1807610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1807610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807610 prefixEnd_1807610 := by exact prefixLift 1807610
  have htrace : WordTrace (prefixWord ++ tailWord_1807610) baseStart_1807610 baseEnd_1807610 := by
    simpa [prefixWord, tailWord_1807610, baseEnd_1807610] using wordTrace_append hprefix tailTrace_1807610
  have hstable : (prefixWord ++ tailWord_1807610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807610).length < 2 ^ (prefixWord ++ tailWord_1807610).sum := by decide
  have hdescent : baseEnd_1807610 < baseStart_1807610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807647 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 3]
def baseStart_1807647 : Nat := 118140960795 + 1807647 * 2 ^ 59
def prefixEnd_1807647 : Nat := 4983230072969 + 3 ^ 40 * 1807647 * 2
def baseEnd_1807647 : Nat := 412529673181330802888573

theorem tailTrace_1807647 : CollatzResearch.WordTrace tailWord_1807647 prefixEnd_1807647 412529673181330802888573 := by
  unfold tailWord_1807647
  simp only [CollatzResearch.WordTrace]
  refine ⟨65930302482211115374133195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43953534988140743582755463 65930302482211115374133195)
  ·
    refine ⟨98895453723316673061199793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65930302482211115374133195 98895453723316673061199793)
    ·
      refine ⟨74171590292487504795899845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98895453723316673061199793 74171590292487504795899845)
      ·
        refine ⟨13907173179841407149231221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74171590292487504795899845 13907173179841407149231221)
        ·
          refine ⟨1303797485610131920240427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13907173179841407149231221 1303797485610131920240427)
          ·
            refine ⟨1955696228415197880360641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303797485610131920240427 1955696228415197880360641)
            ·
              refine ⟨1466772171311398410270481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955696228415197880360641 1466772171311398410270481)
              ·
                refine ⟨1100079128483548807702861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466772171311398410270481 1100079128483548807702861)
                ·
                  refine ⟨412529673181330802888573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100079128483548807702861 412529673181330802888573)
                  ·
                    rfl

theorem cell21_1807647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3].length) (baseStart_1807647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807647 prefixEnd_1807647 := by exact prefixLift 1807647
  have htrace : WordTrace (prefixWord ++ tailWord_1807647) baseStart_1807647 baseEnd_1807647 := by
    simpa [prefixWord, tailWord_1807647, baseEnd_1807647] using wordTrace_append hprefix tailTrace_1807647
  have hstable : (prefixWord ++ tailWord_1807647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807647).length < 2 ^ (prefixWord ++ tailWord_1807647).sum := by decide
  have hdescent : baseEnd_1807647 < baseStart_1807647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807658 : List Nat := [3, 1, 4, 2, 1, 3, 1, 6]
def baseStart_1807658 : Nat := 118140960795 + 1807658 * 2 ^ 59
def prefixEnd_1807658 : Nat := 4983230072969 + 3 ^ 40 * 1807658 * 2
def baseEnd_1807658 : Nat := 137510727843732409401739

theorem tailTrace_1807658 : CollatzResearch.WordTrace tailWord_1807658 prefixEnd_1807658 137510727843732409401739 := by
  unfold tailWord_1807658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482675921292816063195907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43953802456780842835189085 16482675921292816063195907)
  ·
    refine ⟨24724013881939224094793861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16482675921292816063195907 24724013881939224094793861)
    ·
      refine ⟨4635752602863604517773849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24724013881939224094793861 4635752602863604517773849)
      ·
        refine ⟨3476814452147703388330387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635752602863604517773849 3476814452147703388330387)
        ·
          refine ⟨5215221678221555082495581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476814452147703388330387 5215221678221555082495581)
          ·
            refine ⟨1955708129333083155935843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5215221678221555082495581 1955708129333083155935843)
            ·
              refine ⟨2933562193999624733903765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955708129333083155935843 2933562193999624733903765)
              ·
                refine ⟨137510727843732409401739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2933562193999624733903765 137510727843732409401739)
                ·
                  rfl

theorem cell21_1807658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_1807658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807658 prefixEnd_1807658 := by exact prefixLift 1807658
  have htrace : WordTrace (prefixWord ++ tailWord_1807658) baseStart_1807658 baseEnd_1807658 := by
    simpa [prefixWord, tailWord_1807658, baseEnd_1807658] using wordTrace_append hprefix tailTrace_1807658
  have hstable : (prefixWord ++ tailWord_1807658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807658).length < 2 ^ (prefixWord ++ tailWord_1807658).sum := by decide
  have hdescent : baseEnd_1807658 < baseStart_1807658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807700 : List Nat := [2, 4, 1, 1, 2, 1, 10]
def baseStart_1807700 : Nat := 118140960795 + 1807700 * 2 ^ 59
def prefixEnd_1807700 : Nat := 4983230072969 + 3 ^ 40 * 1807700 * 2
def baseEnd_1807700 : Nat := 45837974278157165389459

theorem tailTrace_1807700 : CollatzResearch.WordTrace tailWord_1807700 prefixEnd_1807700 45837974278157165389459 := by
  unfold tailWord_1807700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32966117775509552712906277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43954823700679403617208369 32966117775509552712906277)
  ·
    refine ⟨6181147082908041133669927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32966117775509552712906277 6181147082908041133669927)
    ·
      refine ⟨9271720624362061700504891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6181147082908041133669927 9271720624362061700504891)
      ·
        refine ⟨13907580936543092550757337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271720624362061700504891 13907580936543092550757337)
        ·
          refine ⟨10430685702407319413068003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13907580936543092550757337 10430685702407319413068003)
          ·
            refine ⟨15646028553610979119602005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430685702407319413068003 15646028553610979119602005)
            ·
              refine ⟨45837974278157165389459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15646028553610979119602005 45837974278157165389459)
              ·
                rfl

theorem cell21_1807700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 10].length) (baseStart_1807700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807700 prefixEnd_1807700 := by exact prefixLift 1807700
  have htrace : WordTrace (prefixWord ++ tailWord_1807700) baseStart_1807700 baseEnd_1807700 := by
    simpa [prefixWord, tailWord_1807700, baseEnd_1807700] using wordTrace_append hprefix tailTrace_1807700
  have hstable : (prefixWord ++ tailWord_1807700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807700).length < 2 ^ (prefixWord ++ tailWord_1807700).sum := by decide
  have hdescent : baseEnd_1807700 < baseStart_1807700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807703 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 4]
def baseStart_1807703 : Nat := 118140960795 + 1807703 * 2 ^ 59
def prefixEnd_1807703 : Nat := 4983230072969 + 3 ^ 40 * 1807703 * 2
def baseEnd_1807703 : Nat := 412542453144287149955125

theorem tailTrace_1807703 : CollatzResearch.WordTrace tailWord_1807703 prefixEnd_1807703 412542453144287149955125 := by
  unfold tailWord_1807703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65932344970008236938171763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43954896646672157958781175 65932344970008236938171763)
  ·
    refine ⟨98898517455012355407257645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65932344970008236938171763 98898517455012355407257645)
    ·
      refine ⟨37086944045629633277721617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98898517455012355407257645 37086944045629633277721617)
      ·
        refine ⟨27815208034222224958291213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37086944045629633277721617 27815208034222224958291213)
        ·
          refine ⟨10430703012833334359359205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27815208034222224958291213 10430703012833334359359205)
          ·
            refine ⟨1955756814906250192379851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10430703012833334359359205 1955756814906250192379851)
            ·
              refine ⟨2933635222359375288569777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955756814906250192379851 2933635222359375288569777)
              ·
                refine ⟨2200226416769531466427333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933635222359375288569777 2200226416769531466427333)
                ·
                  refine ⟨412542453144287149955125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200226416769531466427333 412542453144287149955125)
                  ·
                    rfl

theorem cell21_1807703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_1807703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807703 prefixEnd_1807703 := by exact prefixLift 1807703
  have htrace : WordTrace (prefixWord ++ tailWord_1807703) baseStart_1807703 baseEnd_1807703 := by
    simpa [prefixWord, tailWord_1807703, baseEnd_1807703] using wordTrace_append hprefix tailTrace_1807703
  have hstable : (prefixWord ++ tailWord_1807703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807703).length < 2 ^ (prefixWord ++ tailWord_1807703).sum := by decide
  have hdescent : baseEnd_1807703 < baseStart_1807703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807720 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_1807720 : Nat := 118140960795 + 1807720 * 2 ^ 59
def prefixEnd_1807720 : Nat := 4983230072969 + 3 ^ 40 * 1807720 * 2
def baseEnd_1807720 : Nat := 412546332775898898171757

theorem tailTrace_1807720 : CollatzResearch.WordTrace tailWord_1807720 prefixEnd_1807720 412546332775898898171757 := by
  unfold tailWord_1807720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32966482505473324420770307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43955310007297765894360409 32966482505473324420770307)
  ·
    refine ⟨49449723758209986631155461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32966482505473324420770307 49449723758209986631155461)
    ·
      refine ⟨9271823204664372493341649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49449723758209986631155461 9271823204664372493341649)
      ·
        refine ⟨6953867403498279370006237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9271823204664372493341649 6953867403498279370006237)
        ·
          refine ⟨2607700276311854763752339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6953867403498279370006237 2607700276311854763752339)
          ·
            refine ⟨3911550414467782145628509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607700276311854763752339 3911550414467782145628509)
            ·
              refine ⟨1466831405425418304610691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911550414467782145628509 1466831405425418304610691)
              ·
                refine ⟨2200247108138127456916037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466831405425418304610691 2200247108138127456916037)
                ·
                  refine ⟨412546332775898898171757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200247108138127456916037 412546332775898898171757)
                  ·
                    rfl

theorem cell21_1807720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_1807720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807720 prefixEnd_1807720 := by exact prefixLift 1807720
  have htrace : WordTrace (prefixWord ++ tailWord_1807720) baseStart_1807720 baseEnd_1807720 := by
    simpa [prefixWord, tailWord_1807720, baseEnd_1807720] using wordTrace_append hprefix tailTrace_1807720
  have hstable : (prefixWord ++ tailWord_1807720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807720).length < 2 ^ (prefixWord ++ tailWord_1807720).sum := by decide
  have hdescent : baseEnd_1807720 < baseStart_1807720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807776 : List Nat := [2, 1, 1, 4, 1, 2, 4, 6]
def baseStart_1807776 : Nat := 118140960795 + 1807776 * 2 ^ 59
def prefixEnd_1807776 : Nat := 4983230072969 + 3 ^ 40 * 1807776 * 2
def baseEnd_1807776 : Nat := 137519704246285081746103

theorem tailTrace_1807776 : CollatzResearch.WordTrace tailWord_1807776 prefixEnd_1807776 137519704246285081746103 := by
  unfold tailWord_1807776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32967503749371885202789591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43956671665829180270386121 32967503749371885202789591)
  ·
    refine ⟨49451255624057827804184387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32967503749371885202789591 49451255624057827804184387)
    ·
      refine ⟨74176883436086741706276581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49451255624057827804184387 74176883436086741706276581)
      ·
        refine ⟨13908165644266264069926859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74176883436086741706276581 13908165644266264069926859)
        ·
          refine ⟨20862248466399396104890289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908165644266264069926859 20862248466399396104890289)
          ·
            refine ⟨15646686349799547078667717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20862248466399396104890289 15646686349799547078667717)
            ·
              refine ⟨2933753690587415077250197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15646686349799547078667717 2933753690587415077250197)
              ·
                refine ⟨137519704246285081746103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2933753690587415077250197 137519704246285081746103)
                ·
                  rfl

theorem cell21_1807776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_1807776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807776 prefixEnd_1807776 := by exact prefixLift 1807776
  have htrace : WordTrace (prefixWord ++ tailWord_1807776) baseStart_1807776 baseEnd_1807776 := by
    simpa [prefixWord, tailWord_1807776, baseEnd_1807776] using wordTrace_append hprefix tailTrace_1807776
  have hstable : (prefixWord ++ tailWord_1807776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807776).length < 2 ^ (prefixWord ++ tailWord_1807776).sum := by decide
  have hdescent : baseEnd_1807776 < baseStart_1807776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807866 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1807866 : Nat := 118140960795 + 1807866 * 2 ^ 59
def prefixEnd_1807866 : Nat := 4983230072969 + 3 ^ 40 * 1807866 * 2
def baseEnd_1807866 : Nat := 412579651965035088738125

theorem tailTrace_1807866 : CollatzResearch.WordTrace tailWord_1807866 prefixEnd_1807866 412579651965035088738125 := by
  unfold tailWord_1807866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484572517104428944088863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43958860045611810517570301 16484572517104428944088863)
  ·
    refine ⟨24726858775656643416133295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16484572517104428944088863 24726858775656643416133295)
    ·
      refine ⟨37090288163484965124199943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24726858775656643416133295 37090288163484965124199943)
      ·
        refine ⟨55635432245227447686299915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37090288163484965124199943 55635432245227447686299915)
        ·
          refine ⟨83453148367841171529449873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55635432245227447686299915 83453148367841171529449873)
          ·
            refine ⟨62589861275880878647087405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83453148367841171529449873 62589861275880878647087405)
            ·
              refine ⟨23471197978455329492657777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62589861275880878647087405 23471197978455329492657777)
              ·
                refine ⟨17603398483841497119493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23471197978455329492657777 17603398483841497119493333)
                ·
                  refine ⟨412579651965035088738125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17603398483841497119493333 412579651965035088738125)
                  ·
                    rfl

theorem cell21_1807866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1807866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807866 prefixEnd_1807866 := by exact prefixLift 1807866
  have htrace : WordTrace (prefixWord ++ tailWord_1807866) baseStart_1807866 baseEnd_1807866 := by
    simpa [prefixWord, tailWord_1807866, baseEnd_1807866] using wordTrace_append hprefix tailTrace_1807866
  have hstable : (prefixWord ++ tailWord_1807866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807866).length < 2 ^ (prefixWord ++ tailWord_1807866).sum := by decide
  have hdescent : baseEnd_1807866 < baseStart_1807866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807928 : List Nat := [2, 1, 2, 1, 4, 4, 7]
def baseStart_1807928 : Nat := 118140960795 + 1807928 * 2 ^ 59
def prefixEnd_1807928 : Nat := 4983230072969 + 3 ^ 40 * 1807928 * 2
def baseEnd_1807928 : Nat := 45843755689970750967185

theorem tailTrace_1807928 : CollatzResearch.WordTrace tailWord_1807928 prefixEnd_1807928 45843755689970750967185 := by
  unfold tailWord_1807928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32970275697096550182556219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43960367596128733576741625 32970275697096550182556219)
  ·
    refine ⟨49455413545644825273834329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32970275697096550182556219 49455413545644825273834329)
    ·
      refine ⟨37091560159233618955375747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49455413545644825273834329 37091560159233618955375747)
      ·
        refine ⟨55637340238850428433063621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37091560159233618955375747 55637340238850428433063621)
        ·
          refine ⟨10432001294784455331199429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55637340238850428433063621 10432001294784455331199429)
          ·
            refine ⟨1956000242772085374599893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10432001294784455331199429 1956000242772085374599893)
            ·
              refine ⟨45843755689970750967185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1956000242772085374599893 45843755689970750967185)
              ·
                rfl

theorem cell21_1807928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 7].length) (baseStart_1807928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1807928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1807928 prefixEnd_1807928 := by exact prefixLift 1807928
  have htrace : WordTrace (prefixWord ++ tailWord_1807928) baseStart_1807928 baseEnd_1807928 := by
    simpa [prefixWord, tailWord_1807928, baseEnd_1807928] using wordTrace_append hprefix tailTrace_1807928
  have hstable : (prefixWord ++ tailWord_1807928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807928).length < 2 ^ (prefixWord ++ tailWord_1807928).sum := by decide
  have hdescent : baseEnd_1807928 < baseStart_1807928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808063 : List Nat := [1, 1, 2, 2, 2, 3, 2, 8]
def baseStart_1808063 : Nat := 118140960795 + 1808063 * 2 ^ 59
def prefixEnd_1808063 : Nat := 4983230072969 + 3 ^ 40 * 1808063 * 2
def baseEnd_1808063 : Nat := 137541536683002174651463

theorem tailTrace_1808063 : CollatzResearch.WordTrace tailWord_1808063 prefixEnd_1808063 137541536683002174651463 := by
  unfold tailWord_1808063
  simp only [CollatzResearch.WordTrace]
  refine ⟨65945475248704018421276843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43963650165802678947517895 65945475248704018421276843)
  ·
    refine ⟨98918212873056027631915265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65945475248704018421276843 98918212873056027631915265)
    ·
      refine ⟨74188659654792020723936449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98918212873056027631915265 74188659654792020723936449)
      ·
        refine ⟨55641494741094015542952337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74188659654792020723936449 55641494741094015542952337)
        ·
          refine ⟨41731121055820511657214253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55641494741094015542952337 41731121055820511657214253)
          ·
            refine ⟨15649170395932691871455345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41731121055820511657214253 15649170395932691871455345)
            ·
              refine ⟨11736877796949518903591509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15649170395932691871455345 11736877796949518903591509)
              ·
                refine ⟨137541536683002174651463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11736877796949518903591509 137541536683002174651463)
                ·
                  rfl

theorem cell21_1808063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_1808063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808063 prefixEnd_1808063 := by exact prefixLift 1808063
  have htrace : WordTrace (prefixWord ++ tailWord_1808063) baseStart_1808063 baseEnd_1808063 := by
    simpa [prefixWord, tailWord_1808063, baseEnd_1808063] using wordTrace_append hprefix tailTrace_1808063
  have hstable : (prefixWord ++ tailWord_1808063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808063).length < 2 ^ (prefixWord ++ tailWord_1808063).sum := by decide
  have hdescent : baseEnd_1808063 < baseStart_1808063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808097 : List Nat := [1, 2, 3, 1, 6, 1, 7]
def baseStart_1808097 : Nat := 118140960795 + 1808097 * 2 ^ 59
def prefixEnd_1808097 : Nat := 4983230072969 + 3 ^ 40 * 1808097 * 2
def baseEnd_1808097 : Nat := 45848041034692224487517

theorem tailTrace_1808097 : CollatzResearch.WordTrace tailWord_1808097 prefixEnd_1808097 45848041034692224487517 := by
  unfold tailWord_1808097
  simp only [CollatzResearch.WordTrace]
  refine ⟨65946715330580842228014545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43964476887053894818676363 65946715330580842228014545)
  ·
    refine ⟨49460036497935631671010909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65946715330580842228014545 49460036497935631671010909)
    ·
      refine ⟨18547513686725861876629091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49460036497935631671010909 18547513686725861876629091)
      ·
        refine ⟨27821270530088792814943637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18547513686725861876629091 27821270530088792814943637)
        ·
          refine ⟨1304122056097912163200483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27821270530088792814943637 1304122056097912163200483)
          ·
            refine ⟨1956183084146868244800725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304122056097912163200483 1956183084146868244800725)
            ·
              refine ⟨45848041034692224487517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1956183084146868244800725 45848041034692224487517)
              ·
                rfl

theorem cell21_1808097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 7].length) (baseStart_1808097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808097 prefixEnd_1808097 := by exact prefixLift 1808097
  have htrace : WordTrace (prefixWord ++ tailWord_1808097) baseStart_1808097 baseEnd_1808097 := by
    simpa [prefixWord, tailWord_1808097, baseEnd_1808097] using wordTrace_append hprefix tailTrace_1808097
  have hstable : (prefixWord ++ tailWord_1808097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808097).length < 2 ^ (prefixWord ++ tailWord_1808097).sum := by decide
  have hdescent : baseEnd_1808097 < baseStart_1808097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808139 : List Nat := [1, 1, 1, 1, 5, 1, 4, 7]
def baseStart_1808139 : Nat := 118140960795 + 1808139 * 2 ^ 59
def prefixEnd_1808139 : Nat := 4983230072969 + 3 ^ 40 * 1808139 * 2
def baseEnd_1808139 : Nat := 137547318094815760229189

theorem tailTrace_1808139 : CollatzResearch.WordTrace tailWord_1808139 prefixEnd_1808139 137547318094815760229189 := by
  unfold tailWord_1808139
  simp only [CollatzResearch.WordTrace]
  refine ⟨65948247196428683401043471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43965498130952455600695647 65948247196428683401043471)
  ·
    refine ⟨98922370794643025101565207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65948247196428683401043471 98922370794643025101565207)
    ·
      refine ⟨148383556191964537652347811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98922370794643025101565207 148383556191964537652347811)
      ·
        refine ⟨222575334287946806478521717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148383556191964537652347811 222575334287946806478521717)
        ·
          refine ⟨20866437589495013107361411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222575334287946806478521717 20866437589495013107361411)
          ·
            refine ⟨31299656384242519661042117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20866437589495013107361411 31299656384242519661042117)
            ·
              refine ⟨5868685572045472436445397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31299656384242519661042117 5868685572045472436445397)
              ·
                refine ⟨137547318094815760229189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5868685572045472436445397 137547318094815760229189)
                ·
                  rfl

theorem cell21_1808139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_1808139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808139 prefixEnd_1808139 := by exact prefixLift 1808139
  have htrace : WordTrace (prefixWord ++ tailWord_1808139) baseStart_1808139 baseEnd_1808139 := by
    simpa [prefixWord, tailWord_1808139, baseEnd_1808139] using wordTrace_append hprefix tailTrace_1808139
  have hstable : (prefixWord ++ tailWord_1808139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808139).length < 2 ^ (prefixWord ++ tailWord_1808139).sum := by decide
  have hdescent : baseEnd_1808139 < baseStart_1808139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808277 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_1808277 : Nat := 118140960795 + 1808277 * 2 ^ 59
def prefixEnd_1808277 : Nat := 4983230072969 + 3 ^ 40 * 1808277 * 2
def baseEnd_1808277 : Nat := 412673447764589707387285

theorem tailTrace_1808277 : CollatzResearch.WordTrace tailWord_1808277 prefixEnd_1808277 412673447764589707387285 := by
  unfold tailWord_1808277
  simp only [CollatzResearch.WordTrace]
  refine ⟨65953280469928732969567085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43968853646619155313044723 65953280469928732969567085)
  ·
    refine ⟨24732480176223274863587657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65953280469928732969567085 24732480176223274863587657)
    ·
      refine ⟨18549360132167456147690743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24732480176223274863587657 18549360132167456147690743)
      ·
        refine ⟨27824040198251184221536115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18549360132167456147690743 27824040198251184221536115)
        ·
          refine ⟨41736060297376776332304173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27824040198251184221536115 41736060297376776332304173)
          ·
            refine ⟨15651022611516291124614065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41736060297376776332304173 15651022611516291124614065)
            ·
              refine ⟨11738266958637218343460549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15651022611516291124614065 11738266958637218343460549)
              ·
                refine ⟨2200925054744478439398853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11738266958637218343460549 2200925054744478439398853)
                ·
                  refine ⟨412673447764589707387285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200925054744478439398853 412673447764589707387285)
                  ·
                    rfl

theorem cell21_1808277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_1808277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808277 prefixEnd_1808277 := by exact prefixLift 1808277
  have htrace : WordTrace (prefixWord ++ tailWord_1808277) baseStart_1808277 baseEnd_1808277 := by
    simpa [prefixWord, tailWord_1808277, baseEnd_1808277] using wordTrace_append hprefix tailTrace_1808277
  have hstable : (prefixWord ++ tailWord_1808277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808277).length < 2 ^ (prefixWord ++ tailWord_1808277).sum := by decide
  have hdescent : baseEnd_1808277 < baseStart_1808277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808286 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1808286 : Nat := 118140960795 + 1808286 * 2 ^ 59
def prefixEnd_1808286 : Nat := 4983230072969 + 3 ^ 40 * 1808286 * 2
def baseEnd_1808286 : Nat := 412675501687207691737267

theorem tailTrace_1808286 : CollatzResearch.WordTrace tailWord_1808286 prefixEnd_1808286 412675501687207691737267 := by
  unfold tailWord_1808286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8244201090862015938330589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43969072484597418337763141 8244201090862015938330589)
  ·
    refine ⟨3091575409073255976873971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8244201090862015938330589 3091575409073255976873971)
    ·
      refine ⟨4637363113609883965310957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091575409073255976873971 4637363113609883965310957)
      ·
        refine ⟨1739011167603706486991609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4637363113609883965310957 1739011167603706486991609)
        ·
          refine ⟨1304258375702779865243707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739011167603706486991609 1304258375702779865243707)
          ·
            refine ⟨1956387563554169797865561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304258375702779865243707 1956387563554169797865561)
            ·
              refine ⟨1467290672665627348399171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956387563554169797865561 1467290672665627348399171)
              ·
                refine ⟨2200936008998441022598757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467290672665627348399171 2200936008998441022598757)
                ·
                  refine ⟨412675501687207691737267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2200936008998441022598757 412675501687207691737267)
                  ·
                    rfl

theorem cell21_1808286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1808286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808286 prefixEnd_1808286 := by exact prefixLift 1808286
  have htrace : WordTrace (prefixWord ++ tailWord_1808286) baseStart_1808286 baseEnd_1808286 := by
    simpa [prefixWord, tailWord_1808286, baseEnd_1808286] using wordTrace_append hprefix tailTrace_1808286
  have hstable : (prefixWord ++ tailWord_1808286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808286).length < 2 ^ (prefixWord ++ tailWord_1808286).sum := by decide
  have hdescent : baseEnd_1808286 < baseStart_1808286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808336 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_1808336 : Nat := 118140960795 + 1808336 * 2 ^ 59
def prefixEnd_1808336 : Nat := 4983230072969 + 3 ^ 40 * 1808336 * 2
def baseEnd_1808336 : Nat := 412686912368418715903831

theorem tailTrace_1808336 : CollatzResearch.WordTrace tailWord_1808336 prefixEnd_1808336 412686912368418715903831 := by
  unfold tailWord_1808336
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977716188357493022982431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43970288251143324030643241 32977716188357493022982431)
  ·
    refine ⟨49466574282536239534473647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32977716188357493022982431 49466574282536239534473647)
    ·
      refine ⟨74199861423804359301710471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49466574282536239534473647 74199861423804359301710471)
      ·
        refine ⟨111299792135706538952565707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74199861423804359301710471 111299792135706538952565707)
        ·
          refine ⟨166949688203559808428848561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111299792135706538952565707 166949688203559808428848561)
          ·
            refine ⟨125212266152669856321636421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166949688203559808428848561 125212266152669856321636421)
            ·
              refine ⟨23477299903625598060306829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125212266152669856321636421 23477299903625598060306829)
              ·
                refine ⟨8803987463859599272615061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23477299903625598060306829 8803987463859599272615061)
                ·
                  refine ⟨412686912368418715903831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8803987463859599272615061 412686912368418715903831)
                  ·
                    rfl

theorem cell21_1808336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_1808336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808336 prefixEnd_1808336 := by exact prefixLift 1808336
  have htrace : WordTrace (prefixWord ++ tailWord_1808336) baseStart_1808336 baseEnd_1808336 := by
    simpa [prefixWord, tailWord_1808336, baseEnd_1808336] using wordTrace_append hprefix tailTrace_1808336
  have hstable : (prefixWord ++ tailWord_1808336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808336).length < 2 ^ (prefixWord ++ tailWord_1808336).sum := by decide
  have hdescent : baseEnd_1808336 < baseStart_1808336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808342 : List Nat := [5, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1808342 : Nat := 118140960795 + 1808342 * 2 ^ 59
def prefixEnd_1808342 : Nat := 4983230072969 + 3 ^ 40 * 1808342 * 2
def baseEnd_1808342 : Nat := 137562760550054679601273

theorem tailTrace_1808342 : CollatzResearch.WordTrace tailWord_1808342 prefixEnd_1808342 137562760550054679601273 := by
  unfold tailWord_1808342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122228200918328066917705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43970434143128832713788853 4122228200918328066917705)
  ·
    refine ⟨3091671150688746050188279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4122228200918328066917705 3091671150688746050188279)
    ·
      refine ⟨4637506726033119075282419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091671150688746050188279 4637506726033119075282419)
      ·
        refine ⟨6956260089049678612923629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637506726033119075282419 6956260089049678612923629)
        ·
          refine ⟨2608597533393629479846361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6956260089049678612923629 2608597533393629479846361)
          ·
            refine ⟨1956448150045222109884771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608597533393629479846361 1956448150045222109884771)
            ·
              refine ⟨2934672225067833164827157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956448150045222109884771 2934672225067833164827157)
              ·
                refine ⟨137562760550054679601273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2934672225067833164827157 137562760550054679601273)
                ·
                  rfl

theorem cell21_1808342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1808342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808342 prefixEnd_1808342 := by exact prefixLift 1808342
  have htrace : WordTrace (prefixWord ++ tailWord_1808342) baseStart_1808342 baseEnd_1808342 := by
    simpa [prefixWord, tailWord_1808342, baseEnd_1808342] using wordTrace_append hprefix tailTrace_1808342
  have hstable : (prefixWord ++ tailWord_1808342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808342).length < 2 ^ (prefixWord ++ tailWord_1808342).sum := by decide
  have hdescent : baseEnd_1808342 < baseStart_1808342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808353 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_1808353 : Nat := 118140960795 + 1808353 * 2 ^ 59
def prefixEnd_1808353 : Nat := 4983230072969 + 3 ^ 40 * 1808353 * 2
def baseEnd_1808353 : Nat := 412690792000030464120463

theorem tailTrace_1808353 : CollatzResearch.WordTrace tailWord_1808353 prefixEnd_1808353 412690792000030464120463 := by
  unfold tailWord_1808353
  simp only [CollatzResearch.WordTrace]
  refine ⟨65956052417653397949333713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43970701611768931966222475 65956052417653397949333713)
  ·
    refine ⟨49467039313240048462000285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65956052417653397949333713 49467039313240048462000285)
    ·
      refine ⟨18550139742465018173250107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49467039313240048462000285 18550139742465018173250107)
      ·
        refine ⟨27825209613697527259875161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18550139742465018173250107 27825209613697527259875161)
        ·
          refine ⟨20868907210273145444906371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27825209613697527259875161 20868907210273145444906371)
          ·
            refine ⟨31303360815409718167359557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20868907210273145444906371 31303360815409718167359557)
            ·
              refine ⟨5869380152889322156379917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31303360815409718167359557 5869380152889322156379917)
              ·
                refine ⟨2201017557333495808642469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5869380152889322156379917 2201017557333495808642469)
                ·
                  refine ⟨412690792000030464120463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201017557333495808642469 412690792000030464120463)
                  ·
                    rfl

theorem cell21_1808353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_1808353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808353 prefixEnd_1808353 := by exact prefixLift 1808353
  have htrace : WordTrace (prefixWord ++ tailWord_1808353) baseStart_1808353 baseEnd_1808353 := by
    simpa [prefixWord, tailWord_1808353, baseEnd_1808353] using wordTrace_append hprefix tailTrace_1808353
  have hstable : (prefixWord ++ tailWord_1808353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808353).length < 2 ^ (prefixWord ++ tailWord_1808353).sum := by decide
  have hdescent : baseEnd_1808353 < baseStart_1808353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808432 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_1808432 : Nat := 118140960795 + 1808432 * 2 ^ 59
def prefixEnd_1808432 : Nat := 4983230072969 + 3 ^ 40 * 1808432 * 2
def baseEnd_1808432 : Nat := 412708820876343882303635

theorem tailTrace_1808432 : CollatzResearch.WordTrace tailWord_1808432 prefixEnd_1808432 412708820876343882303635 := by
  unfold tailWord_1808432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979466892183597220729775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43972622522911462960973033 32979466892183597220729775)
  ·
    refine ⟨49469200338275395831094663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32979466892183597220729775 49469200338275395831094663)
    ·
      refine ⟨74203800507413093746641995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49469200338275395831094663 74203800507413093746641995)
      ·
        refine ⟨111305700761119640619962993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74203800507413093746641995 111305700761119640619962993)
        ·
          refine ⟨83479275570839730464972245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111305700761119640619962993 83479275570839730464972245)
          ·
            refine ⟨1956545521191556182772787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83479275570839730464972245 1956545521191556182772787)
            ·
              refine ⟨2934818281787334274159181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956545521191556182772787 2934818281787334274159181)
              ·
                refine ⟨1100556855670250352809693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2934818281787334274159181 1100556855670250352809693)
                ·
                  refine ⟨412708820876343882303635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100556855670250352809693 412708820876343882303635)
                  ·
                    rfl

theorem cell21_1808432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_1808432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808432 prefixEnd_1808432 := by exact prefixLift 1808432
  have htrace : WordTrace (prefixWord ++ tailWord_1808432) baseStart_1808432 baseEnd_1808432 := by
    simpa [prefixWord, tailWord_1808432, baseEnd_1808432] using wordTrace_append hprefix tailTrace_1808432
  have hstable : (prefixWord ++ tailWord_1808432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808432).length < 2 ^ (prefixWord ++ tailWord_1808432).sum := by decide
  have hdescent : baseEnd_1808432 < baseStart_1808432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808449 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 3]
def baseStart_1808449 : Nat := 118140960795 + 1808449 * 2 ^ 59
def prefixEnd_1808449 : Nat := 4983230072969 + 3 ^ 40 * 1808449 * 2
def baseEnd_1808449 : Nat := 412712700507955630520267

theorem tailTrace_1808449 : CollatzResearch.WordTrace tailWord_1808449 prefixEnd_1808449 412712700507955630520267 := by
  unfold tailWord_1808449
  simp only [CollatzResearch.WordTrace]
  refine ⟨65959553825305606344828401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43973035883537070896552267 65959553825305606344828401)
  ·
    refine ⟨49469665368979204758621301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65959553825305606344828401 49469665368979204758621301)
    ·
      refine ⟨4637781128341800446120747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49469665368979204758621301 4637781128341800446120747)
      ·
        refine ⟨6956671692512700669181121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637781128341800446120747 6956671692512700669181121)
        ·
          refine ⟨5217503769384525501885841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6956671692512700669181121 5217503769384525501885841)
          ·
            refine ⟨3913127827038394126414381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217503769384525501885841 3913127827038394126414381)
            ·
              refine ⟨1467422935139397797405393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913127827038394126414381 1467422935139397797405393)
              ·
                refine ⟨1100567201354548348054045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467422935139397797405393 1100567201354548348054045)
                ·
                  refine ⟨412712700507955630520267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100567201354548348054045 412712700507955630520267)
                  ·
                    rfl

theorem cell21_1808449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_1808449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808449 prefixEnd_1808449 := by exact prefixLift 1808449
  have htrace : WordTrace (prefixWord ++ tailWord_1808449) baseStart_1808449 baseEnd_1808449 := by
    simpa [prefixWord, tailWord_1808449, baseEnd_1808449] using wordTrace_append hprefix tailTrace_1808449
  have hstable : (prefixWord ++ tailWord_1808449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808449).length < 2 ^ (prefixWord ++ tailWord_1808449).sum := by decide
  have hdescent : baseEnd_1808449 < baseStart_1808449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808505 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_1808505 : Nat := 118140960795 + 1808505 * 2 ^ 59
def prefixEnd_1808505 : Nat := 4983230072969 + 3 ^ 40 * 1808505 * 2
def baseEnd_1808505 : Nat := 412725480470911977586819

theorem tailTrace_1808505 : CollatzResearch.WordTrace tailWord_1808505 prefixEnd_1808505 412725480470911977586819 := by
  unfold tailWord_1808505
  simp only [CollatzResearch.WordTrace]
  refine ⟨65961596313102727908866969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43974397542068485272577979 65961596313102727908866969)
  ·
    refine ⟨49471197234827045931650227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65961596313102727908866969 49471197234827045931650227)
    ·
      refine ⟨74206795852240568897475341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49471197234827045931650227 74206795852240568897475341)
      ·
        refine ⟨27827548444590213336553253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74206795852240568897475341 27827548444590213336553253)
        ·
          refine ⟨5217665333360665000603735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27827548444590213336553253 5217665333360665000603735)
          ·
            refine ⟨7826498000040997500905603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217665333360665000603735 7826498000040997500905603)
            ·
              refine ⟨11739747000061496251358405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826498000040997500905603 11739747000061496251358405)
              ·
                refine ⟨2201202562511530547129701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11739747000061496251358405 2201202562511530547129701)
                ·
                  refine ⟨412725480470911977586819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201202562511530547129701 412725480470911977586819)
                  ·
                    rfl

theorem cell21_1808505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_1808505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808505 prefixEnd_1808505 := by exact prefixLift 1808505
  have htrace : WordTrace (prefixWord ++ tailWord_1808505) baseStart_1808505 baseEnd_1808505 := by
    simpa [prefixWord, tailWord_1808505, baseEnd_1808505] using wordTrace_append hprefix tailTrace_1808505
  have hstable : (prefixWord ++ tailWord_1808505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808505).length < 2 ^ (prefixWord ++ tailWord_1808505).sum := by decide
  have hdescent : baseEnd_1808505 < baseStart_1808505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808508 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_1808508 : Nat := 118140960795 + 1808508 * 2 ^ 59
def prefixEnd_1808508 : Nat := 4983230072969 + 3 ^ 40 * 1808508 * 2
def baseEnd_1808508 : Nat := 412726165111784639036813

theorem tailTrace_1808508 : CollatzResearch.WordTrace tailWord_1808508 prefixEnd_1808508 412726165111784639036813 := by
  unfold tailWord_1808508
  simp only [CollatzResearch.WordTrace]
  refine ⟨32980852866045929710613089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43974470488061239614150785 32980852866045929710613089)
  ·
    refine ⟨24735639649534447282959817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32980852866045929710613089 24735639649534447282959817)
    ·
      refine ⟨18551729737150835462219863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24735639649534447282959817 18551729737150835462219863)
      ·
        refine ⟨27827594605726253193329795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551729737150835462219863 27827594605726253193329795)
        ·
          refine ⟨41741391908589379789994693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27827594605726253193329795 41741391908589379789994693)
          ·
            refine ⟨7826510982860508710624005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41741391908589379789994693 7826510982860508710624005)
            ·
              refine ⟨1467470809286345383242001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7826510982860508710624005 1467470809286345383242001)
              ·
                refine ⟨1100603106964759037431501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467470809286345383242001 1100603106964759037431501)
                ·
                  refine ⟨412726165111784639036813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100603106964759037431501 412726165111784639036813)
                  ·
                    rfl

theorem cell21_1808508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_1808508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808508 prefixEnd_1808508 := by exact prefixLift 1808508
  have htrace : WordTrace (prefixWord ++ tailWord_1808508) baseStart_1808508 baseEnd_1808508 := by
    simpa [prefixWord, tailWord_1808508, baseEnd_1808508] using wordTrace_append hprefix tailTrace_1808508
  have hstable : (prefixWord ++ tailWord_1808508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808508).length < 2 ^ (prefixWord ++ tailWord_1808508).sum := by decide
  have hdescent : baseEnd_1808508 < baseStart_1808508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808519 : List Nat := [1, 1, 4, 2, 1, 1, 5, 6]
def baseStart_1808519 : Nat := 118140960795 + 1808519 * 2 ^ 59
def prefixEnd_1808519 : Nat := 4983230072969 + 3 ^ 40 * 1808519 * 2
def baseEnd_1808519 : Nat := 137576225153883688117819

theorem tailTrace_1808519 : CollatzResearch.WordTrace tailWord_1808519 prefixEnd_1808519 137576225153883688117819 := by
  unfold tailWord_1808519
  simp only [CollatzResearch.WordTrace]
  refine ⟨65962106935052008299876611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43974737956701338866584407 65962106935052008299876611)
  ·
    refine ⟨98943160402578012449814917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65962106935052008299876611 98943160402578012449814917)
    ·
      refine ⟨18551842575483377334340297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98943160402578012449814917 18551842575483377334340297)
      ·
        refine ⟨13913881931612533000755223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18551842575483377334340297 13913881931612533000755223)
        ·
          refine ⟨20870822897418799501132835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13913881931612533000755223 20870822897418799501132835)
          ·
            refine ⟨31306234346128199251699253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870822897418799501132835 31306234346128199251699253)
            ·
              refine ⟨2934959469949518679846805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31306234346128199251699253 2934959469949518679846805)
              ·
                refine ⟨137576225153883688117819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2934959469949518679846805 137576225153883688117819)
                ·
                  rfl

theorem cell21_1808519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_1808519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808519 prefixEnd_1808519 := by exact prefixLift 1808519
  have htrace : WordTrace (prefixWord ++ tailWord_1808519) baseStart_1808519 baseEnd_1808519 := by
    simpa [prefixWord, tailWord_1808519, baseEnd_1808519] using wordTrace_append hprefix tailTrace_1808519
  have hstable : (prefixWord ++ tailWord_1808519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808519).length < 2 ^ (prefixWord ++ tailWord_1808519).sum := by decide
  have hdescent : baseEnd_1808519 < baseStart_1808519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808567 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 3]
def baseStart_1808567 : Nat := 118140960795 + 1808567 * 2 ^ 59
def prefixEnd_1808567 : Nat := 4983230072969 + 3 ^ 40 * 1808567 * 2
def baseEnd_1808567 : Nat := 412739629715613647553359

theorem tailTrace_1808567 : CollatzResearch.WordTrace tailWord_1808567 prefixEnd_1808567 412739629715613647553359 := by
  unfold tailWord_1808567
  simp only [CollatzResearch.WordTrace]
  refine ⟨65963857638878112497623955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43975905092585408331749303 65963857638878112497623955)
  ·
    refine ⟨98945786458317168746435933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65963857638878112497623955 98945786458317168746435933)
    ·
      refine ⟨37104669921868938279913475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98945786458317168746435933 37104669921868938279913475)
      ·
        refine ⟨55657004882803407419870213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37104669921868938279913475 55657004882803407419870213)
        ·
          refine ⟨10435688415525638891225665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55657004882803407419870213 10435688415525638891225665)
          ·
            refine ⟨7826766311644229168419249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10435688415525638891225665 7826766311644229168419249)
            ·
              refine ⟨5870074733733171876314437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7826766311644229168419249 5870074733733171876314437)
              ·
                refine ⟨1100639012574969726808957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5870074733733171876314437 1100639012574969726808957)
                ·
                  refine ⟨412739629715613647553359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100639012574969726808957 412739629715613647553359)
                  ·
                    rfl

theorem cell21_1808567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3].length) (baseStart_1808567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808567 prefixEnd_1808567 := by exact prefixLift 1808567
  have htrace : WordTrace (prefixWord ++ tailWord_1808567) baseStart_1808567 baseEnd_1808567 := by
    simpa [prefixWord, tailWord_1808567, baseEnd_1808567] using wordTrace_append hprefix tailTrace_1808567
  have hstable : (prefixWord ++ tailWord_1808567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808567).length < 2 ^ (prefixWord ++ tailWord_1808567).sum := by decide
  have hdescent : baseEnd_1808567 < baseStart_1808567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808598 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1808598 : Nat := 118140960795 + 1808598 * 2 ^ 59
def prefixEnd_1808598 : Nat := 4983230072969 + 3 ^ 40 * 1808598 * 2
def baseEnd_1808598 : Nat := 412746704337964482536629

theorem tailTrace_1808598 : CollatzResearch.WordTrace tailWord_1808598 prefixEnd_1808598 412746704337964482536629 := by
  unfold tailWord_1808598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122811768860362799500153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43976658867843869861334965 4122811768860362799500153)
  ·
    refine ⟨3092108826645272099625115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4122811768860362799500153 3092108826645272099625115)
    ·
      refine ⟨4638163239967908149437673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092108826645272099625115 4638163239967908149437673)
      ·
        refine ⟨3478622429975931112078255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638163239967908149437673 3478622429975931112078255)
        ·
          refine ⟨5217933644963896668117383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478622429975931112078255 5217933644963896668117383)
          ·
            refine ⟨7826900467445845002176075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217933644963896668117383 7826900467445845002176075)
            ·
              refine ⟨11740350701168767503264113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7826900467445845002176075 11740350701168767503264113)
              ·
                refine ⟨8805263025876575627448085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11740350701168767503264113 8805263025876575627448085)
                ·
                  refine ⟨412746704337964482536629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8805263025876575627448085 412746704337964482536629)
                  ·
                    rfl

theorem cell21_1808598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1808598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808598 prefixEnd_1808598 := by exact prefixLift 1808598
  have htrace : WordTrace (prefixWord ++ tailWord_1808598) baseStart_1808598 baseEnd_1808598 := by
    simpa [prefixWord, tailWord_1808598, baseEnd_1808598] using wordTrace_append hprefix tailTrace_1808598
  have hstable : (prefixWord ++ tailWord_1808598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808598).length < 2 ^ (prefixWord ++ tailWord_1808598).sum := by decide
  have hdescent : baseEnd_1808598 < baseStart_1808598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808674 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1808674 : Nat := 118140960795 + 1808674 * 2 ^ 59
def prefixEnd_1808674 : Nat := 4983230072969 + 3 ^ 40 * 1808674 * 2
def baseEnd_1808674 : Nat := 412764048573405239269807

theorem tailTrace_1808674 : CollatzResearch.WordTrace tailWord_1808674 prefixEnd_1808674 412764048573405239269807 := by
  unfold tailWord_1808674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491940062372617442942269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43978506832993646514512717 16491940062372617442942269)
  ·
    refine ⟨6184477523389731541103351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16491940062372617442942269 6184477523389731541103351)
    ·
      refine ⟨9276716285084597311655027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6184477523389731541103351 9276716285084597311655027)
      ·
        refine ⟨13915074427626895967482541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276716285084597311655027 13915074427626895967482541)
        ·
          refine ⟨5218152910360085987805953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13915074427626895967482541 5218152910360085987805953)
          ·
            refine ⟨3913614682770064490854465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218152910360085987805953 3913614682770064490854465)
            ·
              refine ⟨2935211012077548368140849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913614682770064490854465 2935211012077548368140849)
              ·
                refine ⟨2201408259058161276105637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935211012077548368140849 2201408259058161276105637)
                ·
                  refine ⟨412764048573405239269807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201408259058161276105637 412764048573405239269807)
                  ·
                    rfl

theorem cell21_1808674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1808674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808674 prefixEnd_1808674 := by exact prefixLift 1808674
  have htrace : WordTrace (prefixWord ++ tailWord_1808674) baseStart_1808674 baseEnd_1808674 := by
    simpa [prefixWord, tailWord_1808674, baseEnd_1808674] using wordTrace_append hprefix tailTrace_1808674
  have hstable : (prefixWord ++ tailWord_1808674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808674).length < 2 ^ (prefixWord ++ tailWord_1808674).sum := by decide
  have hdescent : baseEnd_1808674 < baseStart_1808674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808677 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 3]
def baseStart_1808677 : Nat := 118140960795 + 1808677 * 2 ^ 59
def prefixEnd_1808677 : Nat := 4983230072969 + 3 ^ 40 * 1808677 * 2
def baseEnd_1808677 : Nat := 412764733214277900719801

theorem tailTrace_1808677 : CollatzResearch.WordTrace tailWord_1808677 prefixEnd_1808677 412764733214277900719801 := by
  unfold tailWord_1808677
  simp only [CollatzResearch.WordTrace]
  refine ⟨65967869668479601284128285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43978579778986400856085523 65967869668479601284128285)
  ·
    refine ⟨24737951125679850481548107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65967869668479601284128285 24737951125679850481548107)
    ·
      refine ⟨37106926688519775722322161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24737951125679850481548107 37106926688519775722322161)
      ·
        refine ⟨27830195016389831791741621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37106926688519775722322161 27830195016389831791741621)
        ·
          refine ⟨2609080782786546730475777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27830195016389831791741621 2609080782786546730475777)
          ·
            refine ⟨1956810587089910047856833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609080782786546730475777 1956810587089910047856833)
            ·
              refine ⟨1467607940317432535892625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956810587089910047856833 1467607940317432535892625)
              ·
                refine ⟨1100705955238074401919469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467607940317432535892625 1100705955238074401919469)
                ·
                  refine ⟨412764733214277900719801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100705955238074401919469 412764733214277900719801)
                  ·
                    rfl

theorem cell21_1808677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_1808677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808677 prefixEnd_1808677 := by exact prefixLift 1808677
  have htrace : WordTrace (prefixWord ++ tailWord_1808677) baseStart_1808677 baseEnd_1808677 := by
    simpa [prefixWord, tailWord_1808677, baseEnd_1808677] using wordTrace_append hprefix tailTrace_1808677
  have hstable : (prefixWord ++ tailWord_1808677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808677).length < 2 ^ (prefixWord ++ tailWord_1808677).sum := by decide
  have hdescent : baseEnd_1808677 < baseStart_1808677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808702 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1808702 : Nat := 118140960795 + 1808702 * 2 ^ 59
def prefixEnd_1808702 : Nat := 4983230072969 + 3 ^ 40 * 1808702 * 2
def baseEnd_1808702 : Nat := 412770438554883412803083

theorem tailTrace_1808702 : CollatzResearch.WordTrace tailWord_1808702 prefixEnd_1808702 412770438554883412803083 := by
  unfold tailWord_1808702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246097686673628819223545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43979187662259353702525573 8246097686673628819223545)
  ·
    refine ⟨6184573265005221614417659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8246097686673628819223545 6184573265005221614417659)
    ·
      refine ⟨9276859897507832421626489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6184573265005221614417659 9276859897507832421626489)
      ·
        refine ⟨6957644923130874316219867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9276859897507832421626489 6957644923130874316219867)
        ·
          refine ⟨10436467384696311474329801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957644923130874316219867 10436467384696311474329801)
          ·
            refine ⟨7827350538522233605747351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10436467384696311474329801 7827350538522233605747351)
            ·
              refine ⟨11741025807783350408621027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827350538522233605747351 11741025807783350408621027)
              ·
                refine ⟨17611538711675025612931541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741025807783350408621027 17611538711675025612931541)
                ·
                  refine ⟨412770438554883412803083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17611538711675025612931541 412770438554883412803083)
                  ·
                    rfl

theorem cell21_1808702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1808702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808702 prefixEnd_1808702 := by exact prefixLift 1808702
  have htrace : WordTrace (prefixWord ++ tailWord_1808702) baseStart_1808702 baseEnd_1808702 := by
    simpa [prefixWord, tailWord_1808702, baseEnd_1808702] using wordTrace_append hprefix tailTrace_1808702
  have hstable : (prefixWord ++ tailWord_1808702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808702).length < 2 ^ (prefixWord ++ tailWord_1808702).sum := by decide
  have hdescent : baseEnd_1808702 < baseStart_1808702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808705 : List Nat := [1, 2, 5, 2, 2, 1, 3, 5]
def baseStart_1808705 : Nat := 118140960795 + 1808705 * 2 ^ 59
def prefixEnd_1808705 : Nat := 4983230072969 + 3 ^ 40 * 1808705 * 2
def baseEnd_1808705 : Nat := 137590374398585358084359

theorem tailTrace_1808705 : CollatzResearch.WordTrace tailWord_1808705 prefixEnd_1808705 137590374398585358084359 := by
  unfold tailWord_1808705
  simp only [CollatzResearch.WordTrace]
  refine ⟨65968890912378162066147569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43979260608252108044098379 65968890912378162066147569)
  ·
    refine ⟨49476668184283621549610677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65968890912378162066147569 49476668184283621549610677)
    ·
      refine ⟨4638437642276589520276001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49476668184283621549610677 4638437642276589520276001)
      ·
        refine ⟨3478828231707442140207001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638437642276589520276001 3478828231707442140207001)
        ·
          refine ⟨2609121173780581605155251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478828231707442140207001 2609121173780581605155251)
          ·
            refine ⟨3913681760670872407732877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609121173780581605155251 3913681760670872407732877)
            ·
              refine ⟨1467630660251577152899829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913681760670872407732877 1467630660251577152899829)
              ·
                refine ⟨137590374398585358084359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467630660251577152899829 137590374398585358084359)
                ·
                  rfl

theorem cell21_1808705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 5].length) (baseStart_1808705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808705 prefixEnd_1808705 := by exact prefixLift 1808705
  have htrace : WordTrace (prefixWord ++ tailWord_1808705) baseStart_1808705 baseEnd_1808705 := by
    simpa [prefixWord, tailWord_1808705, baseEnd_1808705] using wordTrace_append hprefix tailTrace_1808705
  have hstable : (prefixWord ++ tailWord_1808705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808705).length < 2 ^ (prefixWord ++ tailWord_1808705).sum := by decide
  have hdescent : baseEnd_1808705 < baseStart_1808705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808716 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_1808716 : Nat := 118140960795 + 1808716 * 2 ^ 59
def prefixEnd_1808716 : Nat := 4983230072969 + 3 ^ 40 * 1808716 * 2
def baseEnd_1808716 : Nat := 412773633545622499569721

theorem tailTrace_1808716 : CollatzResearch.WordTrace tailWord_1808716 prefixEnd_1808716 412773633545622499569721 := by
  unfold tailWord_1808716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32984646057669155472399001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43979528076892207296532001 32984646057669155472399001)
  ·
    refine ⟨24738484543251866604299251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32984646057669155472399001 24738484543251866604299251)
    ·
      refine ⟨37107726814877799906448877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24738484543251866604299251 37107726814877799906448877)
      ·
        refine ⟨13915397555579174964918329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37107726814877799906448877 13915397555579174964918329)
        ·
          refine ⟨10436548166684381223688747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13915397555579174964918329 10436548166684381223688747)
          ·
            refine ⟨15654822250026571835533121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436548166684381223688747 15654822250026571835533121)
            ·
              refine ⟨11741116687519928876649841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15654822250026571835533121 11741116687519928876649841)
              ·
                refine ⟨8805837515639946657487381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11741116687519928876649841 8805837515639946657487381)
                ·
                  refine ⟨412773633545622499569721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8805837515639946657487381 412773633545622499569721)
                  ·
                    rfl

theorem cell21_1808716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_1808716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808716 prefixEnd_1808716 := by exact prefixLift 1808716
  have htrace : WordTrace (prefixWord ++ tailWord_1808716) baseStart_1808716 baseEnd_1808716 := by
    simpa [prefixWord, tailWord_1808716, baseEnd_1808716] using wordTrace_append hprefix tailTrace_1808716
  have hstable : (prefixWord ++ tailWord_1808716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808716).length < 2 ^ (prefixWord ++ tailWord_1808716).sum := by decide
  have hdescent : baseEnd_1808716 < baseStart_1808716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808770 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1808770 : Nat := 118140960795 + 1808770 * 2 ^ 59
def prefixEnd_1808770 : Nat := 4983230072969 + 3 ^ 40 * 1808770 * 2
def baseEnd_1808770 : Nat := 412785957081330405669611

theorem tailTrace_1808770 : CollatzResearch.WordTrace tailWord_1808770 prefixEnd_1808770 412785957081330405669611 := by
  unfold tailWord_1808770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492815414285669541815941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43980841104761785444842509 16492815414285669541815941)
  ·
    refine ⟨3092402890178563039090489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16492815414285669541815941 3092402890178563039090489)
    ·
      refine ⟨2319302167633922279317867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3092402890178563039090489 2319302167633922279317867)
      ·
        refine ⟨3478953251450883418976801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319302167633922279317867 3478953251450883418976801)
        ·
          refine ⟨2609214938588162564232601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478953251450883418976801 2609214938588162564232601)
          ·
            refine ⟨1956911203941121923174451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609214938588162564232601 1956911203941121923174451)
            ·
              refine ⟨2935366805911682884761677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956911203941121923174451 2935366805911682884761677)
              ·
                refine ⟨1100762552216881081785629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2935366805911682884761677 1100762552216881081785629)
                ·
                  refine ⟨412785957081330405669611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100762552216881081785629 412785957081330405669611)
                  ·
                    rfl

theorem cell21_1808770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1808770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808770 prefixEnd_1808770 := by exact prefixLift 1808770
  have htrace : WordTrace (prefixWord ++ tailWord_1808770) baseStart_1808770 baseEnd_1808770 := by
    simpa [prefixWord, tailWord_1808770, baseEnd_1808770] using wordTrace_append hprefix tailTrace_1808770
  have hstable : (prefixWord ++ tailWord_1808770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808770).length < 2 ^ (prefixWord ++ tailWord_1808770).sum := by decide
  have hdescent : baseEnd_1808770 < baseStart_1808770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808851 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_1808851 : Nat := 118140960795 + 1808851 * 2 ^ 59
def prefixEnd_1808851 : Nat := 4983230072969 + 3 ^ 40 * 1808851 * 2
def baseEnd_1808851 : Nat := 412804442384892264819445

theorem tailTrace_1808851 : CollatzResearch.WordTrace tailWord_1808851 prefixEnd_1808851 412804442384892264819445 := by
  unfold tailWord_1808851
  simp only [CollatzResearch.WordTrace]
  refine ⟨65974215969849229000962407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43982810646566152667308271 65974215969849229000962407)
  ·
    refine ⟨98961323954773843501443611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65974215969849229000962407 98961323954773843501443611)
    ·
      refine ⟨148441985932160765252165417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98961323954773843501443611 148441985932160765252165417)
      ·
        refine ⟨111331489449120573939124063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148441985932160765252165417 111331489449120573939124063)
        ·
          refine ⟨166997234173680860908686095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111331489449120573939124063 166997234173680860908686095)
          ·
            refine ⟨250495851260521291363029143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166997234173680860908686095 250495851260521291363029143)
            ·
              refine ⟨375743776890781937044543715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250495851260521291363029143 375743776890781937044543715)
              ·
                refine ⟨563615665336172905566815573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375743776890781937044543715 563615665336172905566815573)
                ·
                  refine ⟨412804442384892264819445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 563615665336172905566815573 412804442384892264819445)
                  ·
                    rfl

theorem cell21_1808851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_1808851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808851 prefixEnd_1808851 := by exact prefixLift 1808851
  have htrace : WordTrace (prefixWord ++ tailWord_1808851) baseStart_1808851 baseEnd_1808851 := by
    simpa [prefixWord, tailWord_1808851, baseEnd_1808851] using wordTrace_append hprefix tailTrace_1808851
  have hstable : (prefixWord ++ tailWord_1808851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808851).length < 2 ^ (prefixWord ++ tailWord_1808851).sum := by decide
  have hdescent : baseEnd_1808851 < baseStart_1808851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808919 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 4]
def baseStart_1808919 : Nat := 118140960795 + 1808919 * 2 ^ 59
def prefixEnd_1808919 : Nat := 4983230072969 + 3 ^ 40 * 1808919 * 2
def baseEnd_1808919 : Nat := 412819960911339257685973

theorem tailTrace_1808919 : CollatzResearch.WordTrace tailWord_1808919 prefixEnd_1808919 412819960911339257685973 := by
  unfold tailWord_1808919
  simp only [CollatzResearch.WordTrace]
  refine ⟨65976696133602876614437811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43984464089068584409625207 65976696133602876614437811)
  ·
    refine ⟨98965044200404314921656717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65976696133602876614437811 98965044200404314921656717)
    ·
      refine ⟨37111891575151618095621269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98965044200404314921656717 37111891575151618095621269)
      ·
        refine ⟨1739619917585232098232247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37111891575151618095621269 1739619917585232098232247)
        ·
          refine ⟨2609429876377848147348371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739619917585232098232247 2609429876377848147348371)
          ·
            refine ⟨3914144814566772221022557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609429876377848147348371 3914144814566772221022557)
            ·
              refine ⟨1467804305462539582883459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914144814566772221022557 1467804305462539582883459)
              ·
                refine ⟨2201706458193809374325189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467804305462539582883459 2201706458193809374325189)
                ·
                  refine ⟨412819960911339257685973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201706458193809374325189 412819960911339257685973)
                  ·
                    rfl

theorem cell21_1808919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4].length) (baseStart_1808919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1808919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1808919 prefixEnd_1808919 := by exact prefixLift 1808919
  have htrace : WordTrace (prefixWord ++ tailWord_1808919) baseStart_1808919 baseEnd_1808919 := by
    simpa [prefixWord, tailWord_1808919, baseEnd_1808919] using wordTrace_append hprefix tailTrace_1808919
  have hstable : (prefixWord ++ tailWord_1808919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808919).length < 2 ^ (prefixWord ++ tailWord_1808919).sum := by decide
  have hdescent : baseEnd_1808919 < baseStart_1808919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809003 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_1809003 : Nat := 118140960795 + 1809003 * 2 ^ 59
def prefixEnd_1809003 : Nat := 4983230072969 + 3 ^ 40 * 1809003 * 2
def baseEnd_1809003 : Nat := 412839130855773778285801

theorem tailTrace_1809003 : CollatzResearch.WordTrace tailWord_1809003 prefixEnd_1809003 412839130855773778285801 := by
  unfold tailWord_1809003
  simp only [CollatzResearch.WordTrace]
  refine ⟨65979759865298558960495663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43986506576865705973663775 65979759865298558960495663)
  ·
    refine ⟨98969639797947838440743495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65979759865298558960495663 98969639797947838440743495)
    ·
      refine ⟨148454459696921757661115243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98969639797947838440743495 148454459696921757661115243)
      ·
        refine ⟨222681689545382636491672865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148454459696921757661115243 222681689545382636491672865)
        ·
          refine ⟨167011267159036977368754649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222681689545382636491672865 167011267159036977368754649)
          ·
            refine ⟨125258450369277733026565987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167011267159036977368754649 125258450369277733026565987)
            ·
              refine ⟨187887675553916599539848981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125258450369277733026565987 187887675553916599539848981)
              ·
                refine ⟨8807234791589840603430421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187887675553916599539848981 8807234791589840603430421)
                ·
                  refine ⟨412839130855773778285801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8807234791589840603430421 412839130855773778285801)
                  ·
                    rfl

theorem cell21_1809003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_1809003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809003 prefixEnd_1809003 := by exact prefixLift 1809003
  have htrace : WordTrace (prefixWord ++ tailWord_1809003) baseStart_1809003 baseEnd_1809003 := by
    simpa [prefixWord, tailWord_1809003, baseEnd_1809003] using wordTrace_append hprefix tailTrace_1809003
  have hstable : (prefixWord ++ tailWord_1809003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809003).length < 2 ^ (prefixWord ++ tailWord_1809003).sum := by decide
  have hdescent : baseEnd_1809003 < baseStart_1809003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809020 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1809020 : Nat := 118140960795 + 1809020 * 2 ^ 59
def prefixEnd_1809020 : Nat := 4983230072969 + 3 ^ 40 * 1809020 * 2
def baseEnd_1809020 : Nat := 412843010487385526502433

theorem tailTrace_1809020 : CollatzResearch.WordTrace tailWord_1809020 prefixEnd_1809020 412843010487385526502433 := by
  unfold tailWord_1809020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32990189953118485431932257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43986919937491313909243009 32990189953118485431932257)
  ·
    refine ⟨24742642464838864073949193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32990189953118485431932257 24742642464838864073949193)
    ·
      refine ⟨18556981848629148055461895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24742642464838864073949193 18556981848629148055461895)
      ·
        refine ⟨27835472772943722083192843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556981848629148055461895 27835472772943722083192843)
        ·
          refine ⟨41753209159415583124789265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27835472772943722083192843 41753209159415583124789265)
          ·
            refine ⟨31314906869561687343591949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41753209159415583124789265 31314906869561687343591949)
            ·
              refine ⟨11743090076085632753846981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31314906869561687343591949 11743090076085632753846981)
              ·
                refine ⟨2201829389266056141346309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11743090076085632753846981 2201829389266056141346309)
                ·
                  refine ⟨412843010487385526502433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201829389266056141346309 412843010487385526502433)
                  ·
                    rfl

theorem cell21_1809020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1809020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809020 prefixEnd_1809020 := by exact prefixLift 1809020
  have htrace : WordTrace (prefixWord ++ tailWord_1809020) baseStart_1809020 baseEnd_1809020 := by
    simpa [prefixWord, tailWord_1809020, baseEnd_1809020] using wordTrace_append hprefix tailTrace_1809020
  have hstable : (prefixWord ++ tailWord_1809020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809020).length < 2 ^ (prefixWord ++ tailWord_1809020).sum := by decide
  have hdescent : baseEnd_1809020 < baseStart_1809020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809082 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1809082 : Nat := 118140960795 + 1809082 * 2 ^ 59
def prefixEnd_1809082 : Nat := 4983230072969 + 3 ^ 40 * 1809082 * 2
def baseEnd_1809082 : Nat := 412857159732087196468973

theorem tailTrace_1809082 : CollatzResearch.WordTrace tailWord_1809082 prefixEnd_1809082 412857159732087196468973 := by
  unfold tailWord_1809082
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495660308003088863155375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43988427488008236968414333 16495660308003088863155375)
  ·
    refine ⟨24743490462004633294733063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16495660308003088863155375 24743490462004633294733063)
    ·
      refine ⟨37115235693006949942099595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24743490462004633294733063 37115235693006949942099595)
      ·
        refine ⟨55672853539510424913149393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37115235693006949942099595 55672853539510424913149393)
        ·
          refine ⟨41754640154632818684862045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55672853539510424913149393 41754640154632818684862045)
          ·
            refine ⟨15657990057987307006823267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41754640154632818684862045 15657990057987307006823267)
            ·
              refine ⟨23486985086980960510234901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15657990057987307006823267 23486985086980960510234901)
              ·
                refine ⟨1100952425952232523917261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23486985086980960510234901 1100952425952232523917261)
                ·
                  refine ⟨412857159732087196468973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100952425952232523917261 412857159732087196468973)
                  ·
                    rfl

theorem cell21_1809082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1809082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809082 prefixEnd_1809082 := by exact prefixLift 1809082
  have htrace : WordTrace (prefixWord ++ tailWord_1809082) baseStart_1809082 baseEnd_1809082 := by
    simpa [prefixWord, tailWord_1809082, baseEnd_1809082] using wordTrace_append hprefix tailTrace_1809082
  have hstable : (prefixWord ++ tailWord_1809082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809082).length < 2 ^ (prefixWord ++ tailWord_1809082).sum := by decide
  have hdescent : baseEnd_1809082 < baseStart_1809082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809116 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_1809116 : Nat := 118140960795 + 1809116 * 2 ^ 59
def prefixEnd_1809116 : Nat := 4983230072969 + 3 ^ 40 * 1809116 * 2
def baseEnd_1809116 : Nat := 412864918995310692902237

theorem tailTrace_1809116 : CollatzResearch.WordTrace tailWord_1809116 prefixEnd_1809116 412864918995310692902237 := by
  unfold tailWord_1809116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991940656944589629679601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43989254209259452839572801 32991940656944589629679601)
  ·
    refine ⟨24743955492708442222259701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32991940656944589629679601 24743955492708442222259701)
    ·
      refine ⟨2319745827441416458336847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24743955492708442222259701 2319745827441416458336847)
      ·
        refine ⟨3479618741162124687505271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319745827441416458336847 3479618741162124687505271)
        ·
          refine ⟨5219428111743187031257907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479618741162124687505271 5219428111743187031257907)
          ·
            refine ⟨7829142167614780546886861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219428111743187031257907 7829142167614780546886861)
            ·
              refine ⟨2935928312855542705082573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7829142167614780546886861 2935928312855542705082573)
              ·
                refine ⟨1100973117320828514405965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2935928312855542705082573 1100973117320828514405965)
                ·
                  refine ⟨412864918995310692902237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1100973117320828514405965 412864918995310692902237)
                  ·
                    rfl

theorem cell21_1809116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_1809116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809116 prefixEnd_1809116 := by exact prefixLift 1809116
  have htrace : WordTrace (prefixWord ++ tailWord_1809116) baseStart_1809116 baseEnd_1809116 := by
    simpa [prefixWord, tailWord_1809116, baseEnd_1809116] using wordTrace_append hprefix tailTrace_1809116
  have hstable : (prefixWord ++ tailWord_1809116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809116).length < 2 ^ (prefixWord ++ tailWord_1809116).sum := by decide
  have hdescent : baseEnd_1809116 < baseStart_1809116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809186 : List Nat := [3, 3, 1, 1, 2, 11]
def baseStart_1809186 : Nat := 118140960795 + 1809186 * 2 ^ 59
def prefixEnd_1809186 : Nat := 4983230072969 + 3 ^ 40 * 1809186 * 2
def baseEnd_1809186 : Nat := 15291884961074300990201

theorem tailTrace_1809186 : CollatzResearch.WordTrace tailWord_1809186 prefixEnd_1809186 15291884961074300990201 := by
  unfold tailWord_1809186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496608605908895303601853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43990956282423720809604941 16496608605908895303601853)
  ·
    refine ⟨6186228227215835738850695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16496608605908895303601853 6186228227215835738850695)
    ·
      refine ⟨9279342340823753608276043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186228227215835738850695 9279342340823753608276043)
      ·
        refine ⟨13919013511235630412414065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279342340823753608276043 13919013511235630412414065)
        ·
          refine ⟨10439260133426722809310549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13919013511235630412414065 10439260133426722809310549)
          ·
            refine ⟨15291884961074300990201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10439260133426722809310549 15291884961074300990201)
            ·
              rfl

theorem cell21_1809186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 11].length) (baseStart_1809186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809186 prefixEnd_1809186 := by exact prefixLift 1809186
  have htrace : WordTrace (prefixWord ++ tailWord_1809186) baseStart_1809186 baseEnd_1809186 := by
    simpa [prefixWord, tailWord_1809186, baseEnd_1809186] using wordTrace_append hprefix tailTrace_1809186
  have hstable : (prefixWord ++ tailWord_1809186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809186).length < 2 ^ (prefixWord ++ tailWord_1809186).sum := by decide
  have hdescent : baseEnd_1809186 < baseStart_1809186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809200 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_1809200 : Nat := 118140960795 + 1809200 * 2 ^ 59
def prefixEnd_1809200 : Nat := 4983230072969 + 3 ^ 40 * 1809200 * 2
def baseEnd_1809200 : Nat := 412884088939745213502065

theorem tailTrace_1809200 : CollatzResearch.WordTrace tailWord_1809200 prefixEnd_1809200 412884088939745213502065 := by
  unfold tailWord_1809200
  simp only [CollatzResearch.WordTrace]
  refine ⟨32993472522792430802708527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43991296697056574403611369 32993472522792430802708527)
  ·
    refine ⟨49490208784188646204062791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32993472522792430802708527 49490208784188646204062791)
    ·
      refine ⟨74235313176282969306094187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49490208784188646204062791 74235313176282969306094187)
      ·
        refine ⟨111352969764424453959141281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74235313176282969306094187 111352969764424453959141281)
        ·
          refine ⟨83514727323318340469355961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111352969764424453959141281 83514727323318340469355961)
          ·
            refine ⟨62636045492488755352016971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83514727323318340469355961 62636045492488755352016971)
            ·
              refine ⟨93954068238733133028025457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62636045492488755352016971 93954068238733133028025457)
              ·
                refine ⟨70465551179049849771019093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93954068238733133028025457 70465551179049849771019093)
                ·
                  refine ⟨412884088939745213502065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70465551179049849771019093 412884088939745213502065)
                  ·
                    rfl

theorem cell21_1809200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_1809200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809200 prefixEnd_1809200 := by exact prefixLift 1809200
  have htrace : WordTrace (prefixWord ++ tailWord_1809200) baseStart_1809200 baseEnd_1809200 := by
    simpa [prefixWord, tailWord_1809200, baseEnd_1809200] using wordTrace_append hprefix tailTrace_1809200
  have hstable : (prefixWord ++ tailWord_1809200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809200).length < 2 ^ (prefixWord ++ tailWord_1809200).sum := by decide
  have hdescent : baseEnd_1809200 < baseStart_1809200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809203 : List Nat := [1, 1, 1, 2, 6, 3, 1, 6]
def baseStart_1809203 : Nat := 118140960795 + 1809203 * 2 ^ 59
def prefixEnd_1809203 : Nat := 4983230072969 + 3 ^ 40 * 1809203 * 2
def baseEnd_1809203 : Nat := 137628257860205958317353

theorem tailTrace_1809203 : CollatzResearch.WordTrace tailWord_1809203 prefixEnd_1809203 137628257860205958317353 := by
  unfold tailWord_1809203
  simp only [CollatzResearch.WordTrace]
  refine ⟨65987054464573993117776263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43991369643049328745184175 65987054464573993117776263)
  ·
    refine ⟨98980581696860989676664395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65987054464573993117776263 98980581696860989676664395)
    ·
      refine ⟨148470872545291484514996593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98980581696860989676664395 148470872545291484514996593)
      ·
        refine ⟨111353154408968613386247445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148470872545291484514996593 111353154408968613386247445)
        ·
          refine ⟨5219679112920403752480349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111353154408968613386247445 5219679112920403752480349)
          ·
            refine ⟨1957379667345151407180131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5219679112920403752480349 1957379667345151407180131)
            ·
              refine ⟨2936069501017727110770197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957379667345151407180131 2936069501017727110770197)
              ·
                refine ⟨137628257860205958317353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2936069501017727110770197 137628257860205958317353)
                ·
                  rfl

theorem cell21_1809203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 6].length) (baseStart_1809203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809203 prefixEnd_1809203 := by exact prefixLift 1809203
  have htrace : WordTrace (prefixWord ++ tailWord_1809203) baseStart_1809203 baseEnd_1809203 := by
    simpa [prefixWord, tailWord_1809203, baseEnd_1809203] using wordTrace_append hprefix tailTrace_1809203
  have hstable : (prefixWord ++ tailWord_1809203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809203).length < 2 ^ (prefixWord ++ tailWord_1809203).sum := by decide
  have hdescent : baseEnd_1809203 < baseStart_1809203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809265 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 4]
def baseStart_1809265 : Nat := 118140960795 + 1809265 * 2 ^ 59
def prefixEnd_1809265 : Nat := 4983230072969 + 3 ^ 40 * 1809265 * 2
def baseEnd_1809265 : Nat := 412898922825319544918599

theorem tailTrace_1809265 : CollatzResearch.WordTrace tailWord_1809265 prefixEnd_1809265 412898922825319544918599 := by
  unfold tailWord_1809265
  simp only [CollatzResearch.WordTrace]
  refine ⟨65989315790349377706533249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43992877193566251804355499 65989315790349377706533249)
  ·
    refine ⟨49491986842762033279899937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65989315790349377706533249 49491986842762033279899937)
    ·
      refine ⟨37118990132071524959924953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49491986842762033279899937 37118990132071524959924953)
      ·
        refine ⟨27839242599053643719943715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37118990132071524959924953 27839242599053643719943715)
        ·
          refine ⟨41758863898580465579915573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27839242599053643719943715 41758863898580465579915573)
          ·
            refine ⟨3914893490491918648117085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41758863898580465579915573 3914893490491918648117085)
            ·
              refine ⟨1468085058934469493043907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914893490491918648117085 1468085058934469493043907)
              ·
                refine ⟨2202127588401704239565861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468085058934469493043907 2202127588401704239565861)
                ·
                  refine ⟨412898922825319544918599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202127588401704239565861 412898922825319544918599)
                  ·
                    rfl

theorem cell21_1809265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_1809265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809265 prefixEnd_1809265 := by exact prefixLift 1809265
  have htrace : WordTrace (prefixWord ++ tailWord_1809265) baseStart_1809265 baseEnd_1809265 := by
    simpa [prefixWord, tailWord_1809265, baseEnd_1809265] using wordTrace_append hprefix tailTrace_1809265
  have hstable : (prefixWord ++ tailWord_1809265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809265).length < 2 ^ (prefixWord ++ tailWord_1809265).sum := by decide
  have hdescent : baseEnd_1809265 < baseStart_1809265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809302 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1809302 : Nat := 118140960795 + 1809302 * 2 ^ 59
def prefixEnd_1809302 : Nat := 4983230072969 + 3 ^ 40 * 1809302 * 2
def baseEnd_1809302 : Nat := 412907366729415702801857

theorem tailTrace_1809302 : CollatzResearch.WordTrace tailWord_1809302 prefixEnd_1809302 412907366729415702801857 := by
  unfold tailWord_1809302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124416580700958314101885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43993776860810222017086773 4124416580700958314101885)
  ·
    refine ⟨1546656217762859367788207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4124416580700958314101885 1546656217762859367788207)
    ·
      refine ⟨2319984326644289051682311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546656217762859367788207 2319984326644289051682311)
      ·
        refine ⟨3479976489966433577523467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319984326644289051682311 3479976489966433577523467)
        ·
          refine ⟨5219964734949650366285201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479976489966433577523467 5219964734949650366285201)
          ·
            refine ⟨3914973551212237774713901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219964734949650366285201 3914973551212237774713901)
            ·
              refine ⟨1468115081704589165517713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914973551212237774713901 1468115081704589165517713)
              ·
                refine ⟨1101086311278441874138285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468115081704589165517713 1101086311278441874138285)
                ·
                  refine ⟨412907366729415702801857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101086311278441874138285 412907366729415702801857)
                  ·
                    rfl

theorem cell21_1809302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1809302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809302 prefixEnd_1809302 := by exact prefixLift 1809302
  have htrace : WordTrace (prefixWord ++ tailWord_1809302) baseStart_1809302 baseEnd_1809302 := by
    simpa [prefixWord, tailWord_1809302, baseEnd_1809302] using wordTrace_append hprefix tailTrace_1809302
  have hstable : (prefixWord ++ tailWord_1809302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809302).length < 2 ^ (prefixWord ++ tailWord_1809302).sum := by decide
  have hdescent : baseEnd_1809302 < baseStart_1809302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809479 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 3]
def baseStart_1809479 : Nat := 118140960795 + 1809479 * 2 ^ 59
def prefixEnd_1809479 : Nat := 4983230072969 + 3 ^ 40 * 1809479 * 2
def baseEnd_1809479 : Nat := 412947760540902728351495

theorem tailTrace_1809479 : CollatzResearch.WordTrace tailWord_1809479 prefixEnd_1809479 412947760540902728351495 := by
  unfold tailWord_1809479
  simp only [CollatzResearch.WordTrace]
  refine ⟨65997121011574092254823491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43998080674382728169882327 65997121011574092254823491)
  ·
    refine ⟨98995681517361138382235237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65997121011574092254823491 98995681517361138382235237)
    ·
      refine ⟨18561690284505213446669107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98995681517361138382235237 18561690284505213446669107)
      ·
        refine ⟨27842535426757820170003661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18561690284505213446669107 27842535426757820170003661)
        ·
          refine ⟨10440950785034182563751373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27842535426757820170003661 10440950785034182563751373)
          ·
            refine ⟨3915356544387818461406765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10440950785034182563751373 3915356544387818461406765)
            ·
              refine ⟨1468258704145431923027537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915356544387818461406765 1468258704145431923027537)
              ·
                refine ⟨1101194028109073942270653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468258704145431923027537 1101194028109073942270653)
                ·
                  refine ⟨412947760540902728351495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101194028109073942270653 412947760540902728351495)
                  ·
                    rfl

theorem cell21_1809479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3].length) (baseStart_1809479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809479 prefixEnd_1809479 := by exact prefixLift 1809479
  have htrace : WordTrace (prefixWord ++ tailWord_1809479) baseStart_1809479 baseEnd_1809479 := by
    simpa [prefixWord, tailWord_1809479, baseEnd_1809479] using wordTrace_append hprefix tailTrace_1809479
  have hstable : (prefixWord ++ tailWord_1809479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809479).length < 2 ^ (prefixWord ++ tailWord_1809479).sum := by decide
  have hdescent : baseEnd_1809479 < baseStart_1809479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809490 : List Nat := [3, 2, 2, 1, 3, 1, 1, 8]
def baseStart_1809490 : Nat := 118140960795 + 1809490 * 2 ^ 59
def prefixEnd_1809490 : Nat := 4983230072969 + 3 ^ 40 * 1809490 * 2
def baseEnd_1809490 : Nat := 137650090296923051222713

theorem tailTrace_1809490 : CollatzResearch.WordTrace tailWord_1809490 prefixEnd_1809490 137650090296923051222713 := by
  unfold tailWord_1809490
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499380553633560283368481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43998348143022827422315949 16499380553633560283368481)
  ·
    refine ⟨12374535415225170212526361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16499380553633560283368481 12374535415225170212526361)
    ·
      refine ⟨9280901561418877659394771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12374535415225170212526361 9280901561418877659394771)
      ·
        refine ⟨13921352342128316489092157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9280901561418877659394771 13921352342128316489092157)
        ·
          refine ⟨5220507128298118683409559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13921352342128316489092157 5220507128298118683409559)
          ·
            refine ⟨7830760692447178025114339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220507128298118683409559 7830760692447178025114339)
            ·
              refine ⟨11746141038670767037671509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830760692447178025114339 11746141038670767037671509)
              ·
                refine ⟨137650090296923051222713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11746141038670767037671509 137650090296923051222713)
                ·
                  rfl

theorem cell21_1809490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_1809490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809490 prefixEnd_1809490 := by exact prefixLift 1809490
  have htrace : WordTrace (prefixWord ++ tailWord_1809490) baseStart_1809490 baseEnd_1809490 := by
    simpa [prefixWord, tailWord_1809490, baseEnd_1809490] using wordTrace_append hprefix tailTrace_1809490
  have hstable : (prefixWord ++ tailWord_1809490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809490).length < 2 ^ (prefixWord ++ tailWord_1809490).sum := by decide
  have hdescent : baseEnd_1809490 < baseStart_1809490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809504 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_1809504 : Nat := 118140960795 + 1809504 * 2 ^ 59
def prefixEnd_1809504 : Nat := 4983230072969 + 3 ^ 40 * 1809504 * 2
def baseEnd_1809504 : Nat := 412953465881508240434777

theorem tailTrace_1809504 : CollatzResearch.WordTrace tailWord_1809504 prefixEnd_1809504 412953465881508240434777 := by
  unfold tailWord_1809504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32999016418241760762241783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43998688557655681016322377 32999016418241760762241783)
  ·
    refine ⟨49498524627362641143362675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32999016418241760762241783 49498524627362641143362675)
    ·
      refine ⟨74247786941043961715044013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49498524627362641143362675 74247786941043961715044013)
      ·
        refine ⟨27842920102891485643141505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74247786941043961715044013 27842920102891485643141505)
        ·
          refine ⟨20882190077168614232356129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27842920102891485643141505 20882190077168614232356129)
          ·
            refine ⟨15661642557876460674267097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20882190077168614232356129 15661642557876460674267097)
            ·
              refine ⟨11746231918407345505700323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15661642557876460674267097 11746231918407345505700323)
              ·
                refine ⟨17619347877611018258550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11746231918407345505700323 17619347877611018258550485)
                ·
                  refine ⟨412953465881508240434777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17619347877611018258550485 412953465881508240434777)
                  ·
                    rfl

theorem cell21_1809504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_1809504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809504 prefixEnd_1809504 := by exact prefixLift 1809504
  have htrace : WordTrace (prefixWord ++ tailWord_1809504) baseStart_1809504 baseEnd_1809504 := by
    simpa [prefixWord, tailWord_1809504, baseEnd_1809504] using wordTrace_append hprefix tailTrace_1809504
  have hstable : (prefixWord ++ tailWord_1809504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809504).length < 2 ^ (prefixWord ++ tailWord_1809504).sum := by decide
  have hdescent : baseEnd_1809504 < baseStart_1809504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809642 : List Nat := [3, 1, 3, 1, 1, 5, 7]
def baseStart_1809642 : Nat := 118140960795 + 1809642 * 2 ^ 59
def prefixEnd_1809642 : Nat := 4983230072969 + 3 ^ 40 * 1809642 * 2
def baseEnd_1809642 : Nat := 45887217706850074126055

theorem tailTrace_1809642 : CollatzResearch.WordTrace tailWord_1809642 prefixEnd_1809642 45887217706850074126055 := by
  unfold tailWord_1809642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500766527495892773251795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44002044073322380728671453 16500766527495892773251795)
  ·
    refine ⟨24751149791243839159877693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16500766527495892773251795 24751149791243839159877693)
    ·
      refine ⟨9281681171716439684954135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24751149791243839159877693 9281681171716439684954135)
      ·
        refine ⟨13922521757574659527431203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281681171716439684954135 13922521757574659527431203)
        ·
          refine ⟨20883782636361989291146805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922521757574659527431203 20883782636361989291146805)
          ·
            refine ⟨1957854622158936496045013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20883782636361989291146805 1957854622158936496045013)
            ·
              refine ⟨45887217706850074126055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1957854622158936496045013 45887217706850074126055)
              ·
                rfl

theorem cell21_1809642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 7].length) (baseStart_1809642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809642 prefixEnd_1809642 := by exact prefixLift 1809642
  have htrace : WordTrace (prefixWord ++ tailWord_1809642) baseStart_1809642 baseEnd_1809642 := by
    simpa [prefixWord, tailWord_1809642, baseEnd_1809642] using wordTrace_append hprefix tailTrace_1809642
  have hstable : (prefixWord ++ tailWord_1809642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809642).length < 2 ^ (prefixWord ++ tailWord_1809642).sum := by decide
  have hdescent : baseEnd_1809642 < baseStart_1809642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809662 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1809662 : Nat := 118140960795 + 1809662 * 2 ^ 59
def prefixEnd_1809662 : Nat := 4983230072969 + 3 ^ 40 * 1809662 * 2
def baseEnd_1809662 : Nat := 412989523634135076801121

theorem tailTrace_1809662 : CollatzResearch.WordTrace tailWord_1809662 prefixEnd_1809662 412989523634135076801121 := by
  unfold tailWord_1809662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250474446238889313591905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44002530379940743005823493 8250474446238889313591905)
  ·
    refine ⟨6187855834679166985193929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8250474446238889313591905 6187855834679166985193929)
    ·
      refine ⟨4640891876009375238895447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6187855834679166985193929 4640891876009375238895447)
      ·
        refine ⟨6961337814014062858343171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640891876009375238895447 6961337814014062858343171)
        ·
          refine ⟨10442006721021094287514757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961337814014062858343171 10442006721021094287514757)
          ·
            refine ⟨1957876260191455178909017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10442006721021094287514757 1957876260191455178909017)
            ·
              refine ⟨1468407195143591384181763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957876260191455178909017 1468407195143591384181763)
              ·
                refine ⟨2202610792715387076272645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468407195143591384181763 2202610792715387076272645)
                ·
                  refine ⟨412989523634135076801121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202610792715387076272645 412989523634135076801121)
                  ·
                    rfl

theorem cell21_1809662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1809662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809662 prefixEnd_1809662 := by exact prefixLift 1809662
  have htrace : WordTrace (prefixWord ++ tailWord_1809662) baseStart_1809662 baseEnd_1809662 := by
    simpa [prefixWord, tailWord_1809662, baseEnd_1809662] using wordTrace_append hprefix tailTrace_1809662
  have hstable : (prefixWord ++ tailWord_1809662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809662).length < 2 ^ (prefixWord ++ tailWord_1809662).sum := by decide
  have hdescent : baseEnd_1809662 < baseStart_1809662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809701 : List Nat := [1, 3, 1, 2, 4, 10]
def baseStart_1809701 : Nat := 118140960795 + 1809701 * 2 ^ 59
def prefixEnd_1809701 : Nat := 4983230072969 + 3 ^ 40 * 1809701 * 2
def baseEnd_1809701 : Nat := 15296237924647395394483

theorem tailTrace_1809701 : CollatzResearch.WordTrace tailWord_1809701 prefixEnd_1809701 15296237924647395394483 := by
  unfold tailWord_1809701
  simp only [CollatzResearch.WordTrace]
  refine ⟨66005218016769824169404957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44003478677846549446269971 66005218016769824169404957)
  ·
    refine ⟨24751956756288684063526859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66005218016769824169404957 24751956756288684063526859)
    ·
      refine ⟨37127935134433026095290289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24751956756288684063526859 37127935134433026095290289)
      ·
        refine ⟨27845951350824769571467717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37127935134433026095290289 27845951350824769571467717)
        ·
          refine ⟨5221115878279644294650197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27845951350824769571467717 5221115878279644294650197)
          ·
            refine ⟨15296237924647395394483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5221115878279644294650197 15296237924647395394483)
            ·
              rfl

theorem cell21_1809701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 10].length) (baseStart_1809701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809701 prefixEnd_1809701 := by exact prefixLift 1809701
  have htrace : WordTrace (prefixWord ++ tailWord_1809701) baseStart_1809701 baseEnd_1809701 := by
    simpa [prefixWord, tailWord_1809701, baseEnd_1809701] using wordTrace_append hprefix tailTrace_1809701
  have hstable : (prefixWord ++ tailWord_1809701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809701).length < 2 ^ (prefixWord ++ tailWord_1809701).sum := by decide
  have hdescent : baseEnd_1809701 < baseStart_1809701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809704 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_1809704 : Nat := 118140960795 + 1809704 * 2 ^ 59
def prefixEnd_1809704 : Nat := 4983230072969 + 3 ^ 40 * 1809704 * 2
def baseEnd_1809704 : Nat := 412999108606352337101035

theorem tailTrace_1809704 : CollatzResearch.WordTrace tailWord_1809704 prefixEnd_1809704 412999108606352337101035 := by
  unfold tailWord_1809704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33002663717879477840882083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44003551623839303787842777 33002663717879477840882083)
  ·
    refine ⟨49503995576819216761323125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33002663717879477840882083 49503995576819216761323125)
    ·
      refine ⟨4640999585326801571374043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49503995576819216761323125 4640999585326801571374043)
      ·
        refine ⟨6961499377990202357061065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640999585326801571374043 6961499377990202357061065)
        ·
          refine ⟨5221124533492651767795799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6961499377990202357061065 5221124533492651767795799)
          ·
            refine ⟨7831686800238977651693699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221124533492651767795799 7831686800238977651693699)
            ·
              refine ⟨11747530200358466477540549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831686800238977651693699 11747530200358466477540549)
              ·
                refine ⟨2202661912567212464538853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11747530200358466477540549 2202661912567212464538853)
                ·
                  refine ⟨412999108606352337101035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2202661912567212464538853 412999108606352337101035)
                  ·
                    rfl

theorem cell21_1809704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_1809704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809704 prefixEnd_1809704 := by exact prefixLift 1809704
  have htrace : WordTrace (prefixWord ++ tailWord_1809704) baseStart_1809704 baseEnd_1809704 := by
    simpa [prefixWord, tailWord_1809704, baseEnd_1809704] using wordTrace_append hprefix tailTrace_1809704
  have hstable : (prefixWord ++ tailWord_1809704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809704).length < 2 ^ (prefixWord ++ tailWord_1809704).sum := by decide
  have hdescent : baseEnd_1809704 < baseStart_1809704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809763 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_1809763 : Nat := 118140960795 + 1809763 * 2 ^ 59
def prefixEnd_1809763 : Nat := 4983230072969 + 3 ^ 40 * 1809763 * 2
def baseEnd_1809763 : Nat := 413012573210181345617581

theorem tailTrace_1809763 : CollatzResearch.WordTrace tailWord_1809763 prefixEnd_1809763 413012573210181345617581 := by
  unfold tailWord_1809763
  simp only [CollatzResearch.WordTrace]
  refine ⟨66007479342545208758161943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44004986228363472505441295 66007479342545208758161943)
  ·
    refine ⟨99011219013817813137242915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66007479342545208758161943 99011219013817813137242915)
    ·
      refine ⟨148516828520726719705864373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99011219013817813137242915 148516828520726719705864373)
      ·
        refine ⟨13923452673818129972424785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148516828520726719705864373 13923452673818129972424785)
        ·
          refine ⟨10442589505363597479318589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13923452673818129972424785 10442589505363597479318589)
          ·
            refine ⟨3915971064511349054744471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10442589505363597479318589 3915971064511349054744471)
            ·
              refine ⟨5873956596767023582116707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915971064511349054744471 5873956596767023582116707)
              ·
                refine ⟨8810934895150535373175061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873956596767023582116707 8810934895150535373175061)
                ·
                  refine ⟨413012573210181345617581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8810934895150535373175061 413012573210181345617581)
                  ·
                    rfl

theorem cell21_1809763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_1809763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809763 prefixEnd_1809763 := by exact prefixLift 1809763
  have htrace : WordTrace (prefixWord ++ tailWord_1809763) baseStart_1809763 baseEnd_1809763 := by
    simpa [prefixWord, tailWord_1809763, baseEnd_1809763] using wordTrace_append hprefix tailTrace_1809763
  have hstable : (prefixWord ++ tailWord_1809763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809763).length < 2 ^ (prefixWord ++ tailWord_1809763).sum := by decide
  have hdescent : baseEnd_1809763 < baseStart_1809763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809853 : List Nat := [1, 4, 1, 2, 2, 1, 1, 9]
def baseStart_1809853 : Nat := 118140960795 + 1809853 * 2 ^ 59
def prefixEnd_1809853 : Nat := 4983230072969 + 3 ^ 40 * 1809853 * 2
def baseEnd_1809853 : Nat := 137677704145453729705799

theorem tailTrace_1809853 : CollatzResearch.WordTrace tailWord_1809853 prefixEnd_1809853 137677704145453729705799 := by
  unfold tailWord_1809853
  simp only [CollatzResearch.WordTrace]
  refine ⟨66010761912219154128938213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44007174608146102752625475 66010761912219154128938213)
  ·
    refine ⟨12377017858541091399175915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66010761912219154128938213 12377017858541091399175915)
    ·
      refine ⟨18565526787811637098763873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12377017858541091399175915 18565526787811637098763873)
      ·
        refine ⟨13924145090858727824072905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18565526787811637098763873 13924145090858727824072905)
        ·
          refine ⟨10443108818144045868054679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13924145090858727824072905 10443108818144045868054679)
          ·
            refine ⟨15664663227216068802082019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443108818144045868054679 15664663227216068802082019)
            ·
              refine ⟨23496994840824103203123029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15664663227216068802082019 23496994840824103203123029)
              ·
                refine ⟨137677704145453729705799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23496994840824103203123029 137677704145453729705799)
                ·
                  rfl

theorem cell21_1809853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_1809853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809853 prefixEnd_1809853 := by exact prefixLift 1809853
  have htrace : WordTrace (prefixWord ++ tailWord_1809853) baseStart_1809853 baseEnd_1809853 := by
    simpa [prefixWord, tailWord_1809853, baseEnd_1809853] using wordTrace_append hprefix tailTrace_1809853
  have hstable : (prefixWord ++ tailWord_1809853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809853).length < 2 ^ (prefixWord ++ tailWord_1809853).sum := by decide
  have hdescent : baseEnd_1809853 < baseStart_1809853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809876 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1809876 : Nat := 118140960795 + 1809876 * 2 ^ 59
def prefixEnd_1809876 : Nat := 4983230072969 + 3 ^ 40 * 1809876 * 2
def baseEnd_1809876 : Nat := 413038361349718260234017

theorem tailTrace_1809876 : CollatzResearch.WordTrace tailWord_1809876 prefixEnd_1809876 413038361349718260234017 := by
  unfold tailWord_1809876
  simp only [CollatzResearch.WordTrace]
  refine ⟨33005800395567914528512741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44007733860757219371350321 33005800395567914528512741)
  ·
    refine ⟨6188587574168983974096139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33005800395567914528512741 6188587574168983974096139)
    ·
      refine ⟨9282881361253475961144209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188587574168983974096139 9282881361253475961144209)
      ·
        refine ⟨6962161020940106970858157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9282881361253475961144209 6962161020940106970858157)
        ·
          refine ⟨2610810382852540114071809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6962161020940106970858157 2610810382852540114071809)
          ·
            refine ⟨1958107787139405085553857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610810382852540114071809 1958107787139405085553857)
            ·
              refine ⟨1468580840354553814165393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958107787139405085553857 1468580840354553814165393)
              ·
                refine ⟨1101435630265915360624045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468580840354553814165393 1101435630265915360624045)
                ·
                  refine ⟨413038361349718260234017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101435630265915360624045 413038361349718260234017)
                  ·
                    rfl

theorem cell21_1809876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1809876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809876 prefixEnd_1809876 := by exact prefixLift 1809876
  have htrace : WordTrace (prefixWord ++ tailWord_1809876) baseStart_1809876 baseEnd_1809876 := by
    simpa [prefixWord, tailWord_1809876, baseEnd_1809876] using wordTrace_append hprefix tailTrace_1809876
  have hstable : (prefixWord ++ tailWord_1809876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809876).length < 2 ^ (prefixWord ++ tailWord_1809876).sum := by decide
  have hdescent : baseEnd_1809876 < baseStart_1809876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809994 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1809994 : Nat := 118140960795 + 1809994 * 2 ^ 59
def prefixEnd_1809994 : Nat := 4983230072969 + 3 ^ 40 * 1809994 * 2
def baseEnd_1809994 : Nat := 413065290557376277267109

theorem tailTrace_1809994 : CollatzResearch.WordTrace tailWord_1809994 prefixEnd_1809994 413065290557376277267109 := by
  unfold tailWord_1809994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503976151177083802455259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44010603069805556806547357 16503976151177083802455259)
  ·
    refine ⟨24755964226765625703682889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16503976151177083802455259 24755964226765625703682889)
    ·
      refine ⟨18566973170074219277762167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24755964226765625703682889 18566973170074219277762167)
      ·
        refine ⟨27850459755111328916643251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18566973170074219277762167 27850459755111328916643251)
        ·
          refine ⟨41775689632666993374964877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27850459755111328916643251 41775689632666993374964877)
          ·
            refine ⟨15665883612250122515611829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41775689632666993374964877 15665883612250122515611829)
            ·
              refine ⟨1468676588648448985838609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15665883612250122515611829 1468676588648448985838609)
              ·
                refine ⟨1101507441486336739378957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468676588648448985838609 1101507441486336739378957)
                ·
                  refine ⟨413065290557376277267109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101507441486336739378957 413065290557376277267109)
                  ·
                    rfl

theorem cell21_1809994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1809994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1809994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1809994 prefixEnd_1809994 := by exact prefixLift 1809994
  have htrace : WordTrace (prefixWord ++ tailWord_1809994) baseStart_1809994 baseEnd_1809994 := by
    simpa [prefixWord, tailWord_1809994, baseEnd_1809994] using wordTrace_append hprefix tailTrace_1809994
  have hstable : (prefixWord ++ tailWord_1809994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809994).length < 2 ^ (prefixWord ++ tailWord_1809994).sum := by decide
  have hdescent : baseEnd_1809994 < baseStart_1809994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810053 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 3]
def baseStart_1810053 : Nat := 118140960795 + 1810053 * 2 ^ 59
def prefixEnd_1810053 : Nat := 4983230072969 + 3 ^ 40 * 1810053 * 2
def baseEnd_1810053 : Nat := 413078755161205285783655

theorem tailTrace_1810053 : CollatzResearch.WordTrace tailWord_1810053 prefixEnd_1810053 413078755161205285783655 := by
  unfold tailWord_1810053
  simp only [CollatzResearch.WordTrace]
  refine ⟨66018056511494588286218813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44012037674329725524145875 66018056511494588286218813)
  ·
    refine ⟨24756771191810470607332055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66018056511494588286218813 24756771191810470607332055)
    ·
      refine ⟨37135156787715705910998083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24756771191810470607332055 37135156787715705910998083)
      ·
        refine ⟨55702735181573558866497125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37135156787715705910998083 55702735181573558866497125)
        ·
          refine ⟨10444262846545042287468211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55702735181573558866497125 10444262846545042287468211)
          ·
            refine ⟨15666394269817563431202317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444262846545042287468211 15666394269817563431202317)
            ·
              refine ⟨5874897851181586286700869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15666394269817563431202317 5874897851181586286700869)
              ·
                refine ⟨1101543347096547428756413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5874897851181586286700869 1101543347096547428756413)
                ·
                  refine ⟨413078755161205285783655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101543347096547428756413 413078755161205285783655)
                  ·
                    rfl

theorem cell21_1810053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_1810053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810053 prefixEnd_1810053 := by exact prefixLift 1810053
  have htrace : WordTrace (prefixWord ++ tailWord_1810053) baseStart_1810053 baseEnd_1810053 := by
    simpa [prefixWord, tailWord_1810053, baseEnd_1810053] using wordTrace_append hprefix tailTrace_1810053
  have hstable : (prefixWord ++ tailWord_1810053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810053).length < 2 ^ (prefixWord ++ tailWord_1810053).sum := by decide
  have hdescent : baseEnd_1810053 < baseStart_1810053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810056 : List Nat := [2, 1, 3, 5, 2, 1, 1, 6]
def baseStart_1810056 : Nat := 118140960795 + 1810056 * 2 ^ 59
def prefixEnd_1810056 : Nat := 4983230072969 + 3 ^ 40 * 1810056 * 2
def baseEnd_1810056 : Nat := 137693146600692649077883

theorem tailTrace_1810056 : CollatzResearch.WordTrace tailWord_1810056 prefixEnd_1810056 137693146600692649077883 := by
  unfold tailWord_1810056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009082965241859899289011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44012110620322479865718681 33009082965241859899289011)
  ·
    refine ⟨49513624447862789848933517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33009082965241859899289011 49513624447862789848933517)
    ·
      refine ⟨18567609167948546193350069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49513624447862789848933517 18567609167948546193350069)
      ·
        refine ⟨1740713359495176205626569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18567609167948546193350069 1740713359495176205626569)
        ·
          refine ⟨1305535019621382154219927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740713359495176205626569 1305535019621382154219927)
          ·
            refine ⟨1958302529432073231329891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305535019621382154219927 1958302529432073231329891)
            ·
              refine ⟨2937453794148109846994837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958302529432073231329891 2937453794148109846994837)
              ·
                refine ⟨137693146600692649077883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2937453794148109846994837 137693146600692649077883)
                ·
                  rfl

theorem cell21_1810056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_1810056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810056 prefixEnd_1810056 := by exact prefixLift 1810056
  have htrace : WordTrace (prefixWord ++ tailWord_1810056) baseStart_1810056 baseEnd_1810056 := by
    simpa [prefixWord, tailWord_1810056, baseEnd_1810056] using wordTrace_append hprefix tailTrace_1810056
  have hstable : (prefixWord ++ tailWord_1810056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810056).length < 2 ^ (prefixWord ++ tailWord_1810056).sum := by decide
  have hdescent : baseEnd_1810056 < baseStart_1810056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810095 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_1810095 : Nat := 118140960795 + 1810095 * 2 ^ 59
def prefixEnd_1810095 : Nat := 4983230072969 + 3 ^ 40 * 1810095 * 2
def baseEnd_1810095 : Nat := 413088340133422546083569

theorem tailTrace_1810095 : CollatzResearch.WordTrace tailWord_1810095 prefixEnd_1810095 413088340133422546083569 := by
  unfold tailWord_1810095
  simp only [CollatzResearch.WordTrace]
  refine ⟨66019588377342429459247739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44013058918228286306165159 66019588377342429459247739)
  ·
    refine ⟨99029382566013644188871609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66019588377342429459247739 99029382566013644188871609)
    ·
      refine ⟨74272036924510233141653707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99029382566013644188871609 74272036924510233141653707)
      ·
        refine ⟨111408055386765349712480561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74272036924510233141653707 111408055386765349712480561)
        ·
          refine ⟨83556041540074012284360421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111408055386765349712480561 83556041540074012284360421)
          ·
            refine ⟨15666757788763877303317579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83556041540074012284360421 15666757788763877303317579)
            ·
              refine ⟨23500136683145815954976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15666757788763877303317579 23500136683145815954976369)
              ·
                refine ⟨17625102512359361966232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23500136683145815954976369 17625102512359361966232277)
                ·
                  refine ⟨413088340133422546083569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17625102512359361966232277 413088340133422546083569)
                  ·
                    rfl

theorem cell21_1810095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_1810095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810095 prefixEnd_1810095 := by exact prefixLift 1810095
  have htrace : WordTrace (prefixWord ++ tailWord_1810095) baseStart_1810095 baseEnd_1810095 := by
    simpa [prefixWord, tailWord_1810095, baseEnd_1810095] using wordTrace_append hprefix tailTrace_1810095
  have hstable : (prefixWord ++ tailWord_1810095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810095).length < 2 ^ (prefixWord ++ tailWord_1810095).sum := by decide
  have hdescent : baseEnd_1810095 < baseStart_1810095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810101 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1810101 : Nat := 118140960795 + 1810101 * 2 ^ 59
def prefixEnd_1810101 : Nat := 4983230072969 + 3 ^ 40 * 1810101 * 2
def baseEnd_1810101 : Nat := 413089709415167868983557

theorem tailTrace_1810101 : CollatzResearch.WordTrace tailWord_1810101 prefixEnd_1810101 413089709415167868983557 := by
  unfold tailWord_1810101
  simp only [CollatzResearch.WordTrace]
  refine ⟨66019807215320692483966157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44013204810213794989310771 66019807215320692483966157)
  ·
    refine ⟨24757427705745259681487309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66019807215320692483966157 24757427705745259681487309)
    ·
      refine ⟨9284035389654472380557741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24757427705745259681487309 9284035389654472380557741)
      ·
        refine ⟨3481513271120427142709153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9284035389654472380557741 3481513271120427142709153)
        ·
          refine ⟨2611134953340320357031865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3481513271120427142709153 2611134953340320357031865)
          ·
            refine ⟨1958351215005240267773899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611134953340320357031865 1958351215005240267773899)
            ·
              refine ⟨2937526822507860401660849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958351215005240267773899 2937526822507860401660849)
              ·
                refine ⟨2203145116880895301245637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937526822507860401660849 2203145116880895301245637)
                ·
                  refine ⟨413089709415167868983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203145116880895301245637 413089709415167868983557)
                  ·
                    rfl

theorem cell21_1810101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1810101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810101 prefixEnd_1810101 := by exact prefixLift 1810101
  have htrace : WordTrace (prefixWord ++ tailWord_1810101) baseStart_1810101 baseEnd_1810101 := by
    simpa [prefixWord, tailWord_1810101, baseEnd_1810101] using wordTrace_append hprefix tailTrace_1810101
  have hstable : (prefixWord ++ tailWord_1810101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810101).length < 2 ^ (prefixWord ++ tailWord_1810101).sum := by decide
  have hdescent : baseEnd_1810101 < baseStart_1810101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810112 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_1810112 : Nat := 118140960795 + 1810112 * 2 ^ 59
def prefixEnd_1810112 : Nat := 4983230072969 + 3 ^ 40 * 1810112 * 2
def baseEnd_1810112 : Nat := 413092219765034294300201

theorem tailTrace_1810112 : CollatzResearch.WordTrace tailWord_1810112 prefixEnd_1810112 413092219765034294300201 := by
  unfold tailWord_1810112
  simp only [CollatzResearch.WordTrace]
  refine ⟨33010104209140420681308295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44013472278853894241744393 33010104209140420681308295)
  ·
    refine ⟨49515156313710631021962443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33010104209140420681308295 49515156313710631021962443)
    ·
      refine ⟨74272734470565946532943665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49515156313710631021962443 74272734470565946532943665)
      ·
        refine ⟨55704550852924459899707749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74272734470565946532943665 55704550852924459899707749)
        ·
          refine ⟨10444603284923336231195203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55704550852924459899707749 10444603284923336231195203)
          ·
            refine ⟨15666904927385004346792805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444603284923336231195203 15666904927385004346792805)
            ·
              refine ⟨2937544673884688315023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15666904927385004346792805 2937544673884688315023651)
              ·
                refine ⟨4406317010827032472535477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937544673884688315023651 4406317010827032472535477)
                ·
                  refine ⟨413092219765034294300201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406317010827032472535477 413092219765034294300201)
                  ·
                    rfl

theorem cell21_1810112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_1810112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810112 prefixEnd_1810112 := by exact prefixLift 1810112
  have htrace : WordTrace (prefixWord ++ tailWord_1810112) baseStart_1810112 baseEnd_1810112 := by
    simpa [prefixWord, tailWord_1810112, baseEnd_1810112] using wordTrace_append hprefix tailTrace_1810112
  have hstable : (prefixWord ++ tailWord_1810112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810112).length < 2 ^ (prefixWord ++ tailWord_1810112).sum := by decide
  have hdescent : baseEnd_1810112 < baseStart_1810112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810157 : List Nat := [1, 5, 1, 2, 1, 2, 9]
def baseStart_1810157 : Nat := 118140960795 + 1810157 * 2 ^ 59
def prefixEnd_1810157 : Nat := 4983230072969 + 3 ^ 40 * 1810157 * 2
def baseEnd_1810157 : Nat := 45900276597569357338901

theorem tailTrace_1810157 : CollatzResearch.WordTrace tailWord_1810157 prefixEnd_1810157 45900276597569357338901 := by
  unfold tailWord_1810157
  simp only [CollatzResearch.WordTrace]
  refine ⟨66021849703117814048004725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44014566468745209365336483 66021849703117814048004725)
  ·
    refine ⟨6189548409667295067000443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66021849703117814048004725 6189548409667295067000443)
    ·
      refine ⟨9284322614500942600500665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6189548409667295067000443 9284322614500942600500665)
      ·
        refine ⟨6963241960875706950375499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9284322614500942600500665 6963241960875706950375499)
        ·
          refine ⟨10444862941313560425563249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963241960875706950375499 10444862941313560425563249)
          ·
            refine ⟨7833647205985170319172437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10444862941313560425563249 7833647205985170319172437)
            ·
              refine ⟨45900276597569357338901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7833647205985170319172437 45900276597569357338901)
              ·
                rfl

theorem cell21_1810157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 9].length) (baseStart_1810157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810157 prefixEnd_1810157 := by exact prefixLift 1810157
  have htrace : WordTrace (prefixWord ++ tailWord_1810157) baseStart_1810157 baseEnd_1810157 := by
    simpa [prefixWord, tailWord_1810157, baseEnd_1810157] using wordTrace_append hprefix tailTrace_1810157
  have hstable : (prefixWord ++ tailWord_1810157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810157).length < 2 ^ (prefixWord ++ tailWord_1810157).sum := by decide
  have hdescent : baseEnd_1810157 < baseStart_1810157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810171 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_1810171 : Nat := 118140960795 + 1810171 * 2 ^ 59
def prefixEnd_1810171 : Nat := 4983230072969 + 3 ^ 40 * 1810171 * 2
def baseEnd_1810171 : Nat := 413105684368863302816747

theorem tailTrace_1810171 : CollatzResearch.WordTrace tailWord_1810171 prefixEnd_1810171 413105684368863302816747 := by
  unfold tailWord_1810171
  simp only [CollatzResearch.WordTrace]
  refine ⟨66022360325067094439014367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44014906883378062959342911 66022360325067094439014367)
  ·
    refine ⟨99033540487600641658521551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66022360325067094439014367 99033540487600641658521551)
    ·
      refine ⟨148550310731400962487782327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99033540487600641658521551 148550310731400962487782327)
      ·
        refine ⟨222825466097101443731673491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148550310731400962487782327 222825466097101443731673491)
        ·
          refine ⟨334238199145652165597510237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222825466097101443731673491 334238199145652165597510237)
          ·
            refine ⟨125339324679619562099066339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334238199145652165597510237 125339324679619562099066339)
            ·
              refine ⟨188008987019429343148599509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125339324679619562099066339 188008987019429343148599509)
              ·
                refine ⟨4406460633267875230045301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188008987019429343148599509 4406460633267875230045301)
                ·
                  refine ⟨413105684368863302816747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406460633267875230045301 413105684368863302816747)
                  ·
                    rfl

theorem cell21_1810171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_1810171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810171 prefixEnd_1810171 := by exact prefixLift 1810171
  have htrace : WordTrace (prefixWord ++ tailWord_1810171) baseStart_1810171 baseEnd_1810171 := by
    simpa [prefixWord, tailWord_1810171, baseEnd_1810171] using wordTrace_append hprefix tailTrace_1810171
  have hstable : (prefixWord ++ tailWord_1810171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810171).length < 2 ^ (prefixWord ++ tailWord_1810171).sum := by decide
  have hdescent : baseEnd_1810171 < baseStart_1810171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810247 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_1810247 : Nat := 118140960795 + 1810247 * 2 ^ 59
def prefixEnd_1810247 : Nat := 4983230072969 + 3 ^ 40 * 1810247 * 2
def baseEnd_1810247 : Nat := 413123028604304059549925

theorem tailTrace_1810247 : CollatzResearch.WordTrace tailWord_1810247 prefixEnd_1810247 413123028604304059549925 := by
  unfold tailWord_1810247
  simp only [CollatzResearch.WordTrace]
  refine ⟨66025132272791759418780995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44016754848527839612520663 66025132272791759418780995)
  ·
    refine ⟨99037698409187639128171493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66025132272791759418780995 99037698409187639128171493)
    ·
      refine ⟨18569568451722682336532155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99037698409187639128171493 18569568451722682336532155)
      ·
        refine ⟨27854352677584023504798233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18569568451722682336532155 27854352677584023504798233)
        ·
          refine ⟨20890764508188017628598675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27854352677584023504798233 20890764508188017628598675)
          ·
            refine ⟨31336146762282026442898013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20890764508188017628598675 31336146762282026442898013)
            ·
              refine ⟨11751055035855759916086755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31336146762282026442898013 11751055035855759916086755)
              ·
                refine ⟨17626582553783639874130133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751055035855759916086755 17626582553783639874130133)
                ·
                  refine ⟨413123028604304059549925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17626582553783639874130133 413123028604304059549925)
                  ·
                    rfl

theorem cell21_1810247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_1810247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810247 prefixEnd_1810247 := by exact prefixLift 1810247
  have htrace : WordTrace (prefixWord ++ tailWord_1810247) baseStart_1810247 baseEnd_1810247 := by
    simpa [prefixWord, tailWord_1810247, baseEnd_1810247] using wordTrace_append hprefix tailTrace_1810247
  have hstable : (prefixWord ++ tailWord_1810247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810247).length < 2 ^ (prefixWord ++ tailWord_1810247).sum := by decide
  have hdescent : baseEnd_1810247 < baseStart_1810247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810340 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1810340 : Nat := 118140960795 + 1810340 * 2 ^ 59
def prefixEnd_1810340 : Nat := 4983230072969 + 3 ^ 40 * 1810340 * 2
def baseEnd_1810340 : Nat := 413144252471356564499735

theorem tailTrace_1810340 : CollatzResearch.WordTrace tailWord_1810340 prefixEnd_1810340 413144252471356564499735 := by
  unfold tailWord_1810340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33014262130727418150958237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44019016174303224201277649 33014262130727418150958237)
  ·
    refine ⟨12380348299022781806609339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33014262130727418150958237 12380348299022781806609339)
    ·
      refine ⟨18570522448534172709914009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12380348299022781806609339 18570522448534172709914009)
      ·
        refine ⟨13927891836400629532435507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18570522448534172709914009 13927891836400629532435507)
        ·
          refine ⟨20891837754600944298653261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13927891836400629532435507 20891837754600944298653261)
          ·
            refine ⟨7834439157975354111994973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20891837754600944298653261 7834439157975354111994973)
            ·
              refine ⟨2937914684240757791998115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7834439157975354111994973 2937914684240757791998115)
              ·
                refine ⟨4406872026361136687997173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937914684240757791998115 4406872026361136687997173)
                ·
                  refine ⟨413144252471356564499735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406872026361136687997173 413144252471356564499735)
                  ·
                    rfl

theorem cell21_1810340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1810340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810340 prefixEnd_1810340 := by exact prefixLift 1810340
  have htrace : WordTrace (prefixWord ++ tailWord_1810340) baseStart_1810340 baseEnd_1810340 := by
    simpa [prefixWord, tailWord_1810340, baseEnd_1810340] using wordTrace_append hprefix tailTrace_1810340
  have hstable : (prefixWord ++ tailWord_1810340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810340).length < 2 ^ (prefixWord ++ tailWord_1810340).sum := by decide
  have hdescent : baseEnd_1810340 < baseStart_1810340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810368 : List Nat := [2, 1, 1, 2, 3, 2, 1, 9]
def baseStart_1810368 : Nat := 118140960795 + 1810368 * 2 ^ 59
def prefixEnd_1810368 : Nat := 4983230072969 + 3 ^ 40 * 1810368 * 2
def baseEnd_1810368 : Nat := 137716880817611579344337

theorem tailTrace_1810368 : CollatzResearch.WordTrace tailWord_1810368 prefixEnd_1810368 137716880817611579344337 := by
  unfold tailWord_1810368
  simp only [CollatzResearch.WordTrace]
  refine ⟨33014772752676698541967879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44019697003568931389290505 33014772752676698541967879)
  ·
    refine ⟨49522159129015047812951819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33014772752676698541967879 49522159129015047812951819)
    ·
      refine ⟨74283238693522571719427729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49522159129015047812951819 74283238693522571719427729)
      ·
        refine ⟨55712429020141928789570797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74283238693522571719427729 55712429020141928789570797)
        ·
          refine ⟨20892160882553223296089049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55712429020141928789570797 20892160882553223296089049)
          ·
            refine ⟨15669120661914917472066787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20892160882553223296089049 15669120661914917472066787)
            ·
              refine ⟨23503680992872376208100181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15669120661914917472066787 23503680992872376208100181)
              ·
                refine ⟨137716880817611579344337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23503680992872376208100181 137716880817611579344337)
                ·
                  rfl

theorem cell21_1810368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_1810368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810368 prefixEnd_1810368 := by exact prefixLift 1810368
  have htrace : WordTrace (prefixWord ++ tailWord_1810368) baseStart_1810368 baseEnd_1810368 := by
    simpa [prefixWord, tailWord_1810368, baseEnd_1810368] using wordTrace_append hprefix tailTrace_1810368
  have hstable : (prefixWord ++ tailWord_1810368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810368).length < 2 ^ (prefixWord ++ tailWord_1810368).sum := by decide
  have hdescent : baseEnd_1810368 < baseStart_1810368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810433 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 3]
def baseStart_1810433 : Nat := 118140960795 + 1810433 * 2 ^ 59
def prefixEnd_1810433 : Nat := 4983230072969 + 3 ^ 40 * 1810433 * 2
def baseEnd_1810433 : Nat := 413165476338409069449545

theorem tailTrace_1810433 : CollatzResearch.WordTrace tailWord_1810433 prefixEnd_1810433 413165476338409069449545 := by
  unfold tailWord_1810433
  simp only [CollatzResearch.WordTrace]
  refine ⟨66031916250117913185051953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44021277500078608790034635 66031916250117913185051953)
  ·
    refine ⟨49523937187588434888788965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66031916250117913185051953 49523937187588434888788965)
    ·
      refine ⟨9285738222672831541647931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49523937187588434888788965 9285738222672831541647931)
      ·
        refine ⟨13928607334009247312471897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9285738222672831541647931 13928607334009247312471897)
        ·
          refine ⟨10446455500506935484353923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13928607334009247312471897 10446455500506935484353923)
          ·
            refine ⟨15669683250760403226530885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446455500506935484353923 15669683250760403226530885)
            ·
              refine ⟨2938065609517575604974541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15669683250760403226530885 2938065609517575604974541)
              ·
                refine ⟨1101774603569090851865453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938065609517575604974541 1101774603569090851865453)
                ·
                  refine ⟨413165476338409069449545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101774603569090851865453 413165476338409069449545)
                  ·
                    rfl

theorem cell21_1810433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_1810433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810433 prefixEnd_1810433 := by exact prefixLift 1810433
  have htrace : WordTrace (prefixWord ++ tailWord_1810433) baseStart_1810433 baseEnd_1810433 := by
    simpa [prefixWord, tailWord_1810433, baseEnd_1810433] using wordTrace_append hprefix tailTrace_1810433
  have hstable : (prefixWord ++ tailWord_1810433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810433).length < 2 ^ (prefixWord ++ tailWord_1810433).sum := by decide
  have hdescent : baseEnd_1810433 < baseStart_1810433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810444 : List Nat := [2, 2, 1, 2, 3, 1, 10]
def baseStart_1810444 : Nat := 118140960795 + 1810444 * 2 ^ 59
def prefixEnd_1810444 : Nat := 4983230072969 + 3 ^ 40 * 1810444 * 2
def baseEnd_1810444 : Nat := 45907554076475054974021

theorem tailTrace_1810444 : CollatzResearch.WordTrace tailWord_1810444 prefixEnd_1810444 45907554076475054974021 := by
  unfold tailWord_1810444
  simp only [CollatzResearch.WordTrace]
  refine ⟨33016158726539031031851193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44021544968718708042468257 33016158726539031031851193)
  ·
    refine ⟨24762119044904273273888395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33016158726539031031851193 24762119044904273273888395)
    ·
      refine ⟨37143178567356409910832593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24762119044904273273888395 37143178567356409910832593)
      ·
        refine ⟨27857383925517307433124445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37143178567356409910832593 27857383925517307433124445)
        ·
          refine ⟨10446518972068990287421667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27857383925517307433124445 10446518972068990287421667)
          ·
            refine ⟨15669778458103485431132501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446518972068990287421667 15669778458103485431132501)
            ·
              refine ⟨45907554076475054974021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15669778458103485431132501 45907554076475054974021)
              ·
                rfl

theorem cell21_1810444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 10].length) (baseStart_1810444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810444 prefixEnd_1810444 := by exact prefixLift 1810444
  have htrace : WordTrace (prefixWord ++ tailWord_1810444) baseStart_1810444 baseEnd_1810444 := by
    simpa [prefixWord, tailWord_1810444, baseEnd_1810444] using wordTrace_append hprefix tailTrace_1810444
  have hstable : (prefixWord ++ tailWord_1810444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810444).length < 2 ^ (prefixWord ++ tailWord_1810444).sum := by decide
  have hdescent : baseEnd_1810444 < baseStart_1810444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810478 : List Nat := [4, 1, 3, 1, 1, 2, 4, 5]
def baseStart_1810478 : Nat := 118140960795 + 1810478 * 2 ^ 59
def prefixEnd_1810478 : Nat := 4983230072969 + 3 ^ 40 * 1810478 * 2
def baseEnd_1810478 : Nat := 137725248650499663733151

theorem tailTrace_1810478 : CollatzResearch.WordTrace tailWord_1810478 prefixEnd_1810478 137725248650499663733151 := by
  unfold tailWord_1810478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254194691869360733805011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44022371689969923913626725 8254194691869360733805011)
  ·
    refine ⟨12381292037804041100707517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8254194691869360733805011 12381292037804041100707517)
    ·
      refine ⟨4642984514176515412765319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12381292037804041100707517 4642984514176515412765319)
      ·
        refine ⟨6964476771264773119147979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642984514176515412765319 6964476771264773119147979)
        ·
          refine ⟨10446715156897159678721969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964476771264773119147979 10446715156897159678721969)
          ·
            refine ⟨7835036367672869759041477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10446715156897159678721969 7835036367672869759041477)
            ·
              refine ⟨1469069318938663079820277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7835036367672869759041477 1469069318938663079820277)
              ·
                refine ⟨137725248650499663733151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1469069318938663079820277 137725248650499663733151)
                ·
                  rfl

theorem cell21_1810478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_1810478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810478 prefixEnd_1810478 := by exact prefixLift 1810478
  have htrace : WordTrace (prefixWord ++ tailWord_1810478) baseStart_1810478 baseEnd_1810478 := by
    simpa [prefixWord, tailWord_1810478, baseEnd_1810478] using wordTrace_append hprefix tailTrace_1810478
  have hstable : (prefixWord ++ tailWord_1810478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810478).length < 2 ^ (prefixWord ++ tailWord_1810478).sum := by decide
  have hdescent : baseEnd_1810478 < baseStart_1810478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810484 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1810484 : Nat := 118140960795 + 1810484 * 2 ^ 59
def prefixEnd_1810484 : Nat := 4983230072969 + 3 ^ 40 * 1810484 * 2
def baseEnd_1810484 : Nat := 413177115233244314099441

theorem tailTrace_1810484 : CollatzResearch.WordTrace tailWord_1810484 prefixEnd_1810484 413177115233244314099441 := by
  unfold tailWord_1810484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33016888186466574447579253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44022517581955432596772337 33016888186466574447579253)
  ·
    refine ⟨3095333267481241354460555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33016888186466574447579253 3095333267481241354460555)
    ·
      refine ⟨4642999901221862031690833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095333267481241354460555 4642999901221862031690833)
      ·
        refine ⟨3482249925916396523768125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642999901221862031690833 3482249925916396523768125)
        ·
          refine ⟨1305843722218648696413047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3482249925916396523768125 1305843722218648696413047)
          ·
            refine ⟨1958765583327973044619571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305843722218648696413047 1958765583327973044619571)
            ·
              refine ⟨2938148374991959566929357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958765583327973044619571 2938148374991959566929357)
              ·
                refine ⟨1101805640621984837598509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938148374991959566929357 1101805640621984837598509)
                ·
                  refine ⟨413177115233244314099441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101805640621984837598509 413177115233244314099441)
                  ·
                    rfl

theorem cell21_1810484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1810484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810484 prefixEnd_1810484 := by exact prefixLift 1810484
  have htrace : WordTrace (prefixWord ++ tailWord_1810484) baseStart_1810484 baseEnd_1810484 := by
    simpa [prefixWord, tailWord_1810484, baseEnd_1810484] using wordTrace_append hprefix tailTrace_1810484
  have hstable : (prefixWord ++ tailWord_1810484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810484).length < 2 ^ (prefixWord ++ tailWord_1810484).sum := by decide
  have hdescent : baseEnd_1810484 < baseStart_1810484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810506 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1810506 : Nat := 118140960795 + 1810506 * 2 ^ 59
def prefixEnd_1810506 : Nat := 4983230072969 + 3 ^ 40 * 1810506 * 2
def baseEnd_1810506 : Nat := 413182135932977164732729

theorem tailTrace_1810506 : CollatzResearch.WordTrace tailWord_1810506 prefixEnd_1810506 413182135932977164732729 := by
  unfold tailWord_1810506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508644694713361663114843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44023052519235631101639581 16508644694713361663114843)
  ·
    refine ⟨24762967042070042494672265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16508644694713361663114843 24762967042070042494672265)
    ·
      refine ⟨18572225281552531871004199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24762967042070042494672265 18572225281552531871004199)
      ·
        refine ⟨27858337922328797806506299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18572225281552531871004199 27858337922328797806506299)
        ·
          refine ⟨41787506883493196709759449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858337922328797806506299 41787506883493196709759449)
          ·
            refine ⟨31340630162619897532319587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41787506883493196709759449 31340630162619897532319587)
            ·
              refine ⟨47010945243929846298479381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31340630162619897532319587 47010945243929846298479381)
              ·
                refine ⟨2203638058309211545241221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47010945243929846298479381 2203638058309211545241221)
                ·
                  refine ⟨413182135932977164732729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2203638058309211545241221 413182135932977164732729)
                  ·
                    rfl

theorem cell21_1810506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1810506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810506 prefixEnd_1810506 := by exact prefixLift 1810506
  have htrace : WordTrace (prefixWord ++ tailWord_1810506) baseStart_1810506 baseEnd_1810506 := by
    simpa [prefixWord, tailWord_1810506, baseEnd_1810506] using wordTrace_append hprefix tailTrace_1810506
  have hstable : (prefixWord ++ tailWord_1810506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810506).length < 2 ^ (prefixWord ++ tailWord_1810506).sum := by decide
  have hdescent : baseEnd_1810506 < baseStart_1810506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810520 : List Nat := [2, 1, 2, 2, 1, 4, 1, 8]
def baseStart_1810520 : Nat := 118140960795 + 1810520 * 2 ^ 59
def prefixEnd_1810520 : Nat := 4983230072969 + 3 ^ 40 * 1810520 * 2
def baseEnd_1810520 : Nat := 137728443641238750499789

theorem tailTrace_1810520 : CollatzResearch.WordTrace tailWord_1810520 prefixEnd_1810520 137728443641238750499789 := by
  unfold tailWord_1810520
  simp only [CollatzResearch.WordTrace]
  refine ⟨33017544700401363521734507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44023392933868484695646009 33017544700401363521734507)
  ·
    refine ⟨49526317050602045282601761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33017544700401363521734507 49526317050602045282601761)
    ·
      refine ⟨37144737787951533961951321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49526317050602045282601761 37144737787951533961951321)
      ·
        refine ⟨27858553340963650471463491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37144737787951533961951321 27858553340963650471463491)
        ·
          refine ⟨41787830011445475707195237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858553340963650471463491 41787830011445475707195237)
          ·
            refine ⟨7835218127146026695099107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41787830011445475707195237 7835218127146026695099107)
            ·
              refine ⟨11752827190719040042648661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835218127146026695099107 11752827190719040042648661)
              ·
                refine ⟨137728443641238750499789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11752827190719040042648661 137728443641238750499789)
                ·
                  rfl

theorem cell21_1810520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_1810520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810520 prefixEnd_1810520 := by exact prefixLift 1810520
  have htrace : WordTrace (prefixWord ++ tailWord_1810520) baseStart_1810520 baseEnd_1810520 := by
    simpa [prefixWord, tailWord_1810520, baseEnd_1810520] using wordTrace_append hprefix tailTrace_1810520
  have hstable : (prefixWord ++ tailWord_1810520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810520).length < 2 ^ (prefixWord ++ tailWord_1810520).sum := by decide
  have hdescent : baseEnd_1810520 < baseStart_1810520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810661 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 3]
def baseStart_1810661 : Nat := 118140960795 + 1810661 * 2 ^ 59
def prefixEnd_1810661 : Nat := 4983230072969 + 3 ^ 40 * 1810661 * 2
def baseEnd_1810661 : Nat := 413217509044731339649079

theorem tailTrace_1810661 : CollatzResearch.WordTrace tailWord_1810661 prefixEnd_1810661 413217509044731339649079 := by
  unfold tailWord_1810661
  simp only [CollatzResearch.WordTrace]
  refine ⟨66040232093291908124351837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44026821395527938749567891 66040232093291908124351837)
  ·
    refine ⟨24765087034984465546631939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66040232093291908124351837 24765087034984465546631939)
    ·
      refine ⟨37147630552476698319947909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765087034984465546631939 37147630552476698319947909)
      ·
        refine ⟨6965180728589380934990233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37147630552476698319947909 6965180728589380934990233)
        ·
          refine ⟨5223885546442035701242675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6965180728589380934990233 5223885546442035701242675)
          ·
            refine ⟨7835828319663053551864013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223885546442035701242675 7835828319663053551864013)
            ·
              refine ⟨2938435619873645081949005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7835828319663053551864013 2938435619873645081949005)
              ·
                refine ⟨1101913357452616905730877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938435619873645081949005 1101913357452616905730877)
                ·
                  refine ⟨413217509044731339649079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101913357452616905730877 413217509044731339649079)
                  ·
                    rfl

theorem cell21_1810661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_1810661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810661 prefixEnd_1810661 := by exact prefixLift 1810661
  have htrace : WordTrace (prefixWord ++ tailWord_1810661) baseStart_1810661 baseEnd_1810661 := by
    simpa [prefixWord, tailWord_1810661, baseEnd_1810661] using wordTrace_append hprefix tailTrace_1810661
  have hstable : (prefixWord ++ tailWord_1810661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810661).length < 2 ^ (prefixWord ++ tailWord_1810661).sum := by decide
  have hdescent : baseEnd_1810661 < baseStart_1810661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810737 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 3]
def baseStart_1810737 : Nat := 118140960795 + 1810737 * 2 ^ 59
def prefixEnd_1810737 : Nat := 4983230072969 + 3 ^ 40 * 1810737 * 2
def baseEnd_1810737 : Nat := 413234853280172096382257

theorem tailTrace_1810737 : CollatzResearch.WordTrace tailWord_1810737 prefixEnd_1810737 413234853280172096382257 := by
  unfold tailWord_1810737
  simp only [CollatzResearch.WordTrace]
  refine ⟨66043004041016573104118465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44028669360677715402745643 66043004041016573104118465)
  ·
    refine ⟨49532253030762429828088849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66043004041016573104118465 49532253030762429828088849)
    ·
      refine ⟨37149189773071822371066637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49532253030762429828088849 37149189773071822371066637)
      ·
        refine ⟨13930946164901933389149989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37149189773071822371066637 13930946164901933389149989)
        ·
          refine ⟨2612052405919112510465623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13930946164901933389149989 2612052405919112510465623)
          ·
            refine ⟨3918078608878668765698435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612052405919112510465623 3918078608878668765698435)
            ·
              refine ⟨5877117913318003148547653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918078608878668765698435 5877117913318003148547653)
              ·
                refine ⟨1101959608747125590352685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5877117913318003148547653 1101959608747125590352685)
                ·
                  refine ⟨413234853280172096382257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1101959608747125590352685 413234853280172096382257)
                  ·
                    rfl

theorem cell21_1810737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_1810737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810737 prefixEnd_1810737 := by exact prefixLift 1810737
  have htrace : WordTrace (prefixWord ++ tailWord_1810737) baseStart_1810737 baseEnd_1810737 := by
    simpa [prefixWord, tailWord_1810737, baseEnd_1810737] using wordTrace_append hprefix tailTrace_1810737
  have hstable : (prefixWord ++ tailWord_1810737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810737).length < 2 ^ (prefixWord ++ tailWord_1810737).sum := by decide
  have hdescent : baseEnd_1810737 < baseStart_1810737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810793 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_1810793 : Nat := 118140960795 + 1810793 * 2 ^ 59
def prefixEnd_1810793 : Nat := 4983230072969 + 3 ^ 40 * 1810793 * 2
def baseEnd_1810793 : Nat := 413247633243128443448809

theorem tailTrace_1810793 : CollatzResearch.WordTrace tailWord_1810793 prefixEnd_1810793 413247633243128443448809 := by
  unfold tailWord_1810793
  simp only [CollatzResearch.WordTrace]
  refine ⟨66045046528813694668157033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44030031019209129778771355 66045046528813694668157033)
  ·
    refine ⟨49533784896610271001117775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66045046528813694668157033 49533784896610271001117775)
    ·
      refine ⟨74300677344915406501676663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49533784896610271001117775 74300677344915406501676663)
      ·
        refine ⟨111451016017373109752514995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74300677344915406501676663 111451016017373109752514995)
        ·
          refine ⟨167176524026059664628772493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111451016017373109752514995 167176524026059664628772493)
          ·
            refine ⟨62691196509772374235789685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167176524026059664628772493 62691196509772374235789685)
            ·
              refine ⟨5877299672791160084605283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62691196509772374235789685 5877299672791160084605283)
              ·
                refine ⟨8815949509186740126907925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5877299672791160084605283 8815949509186740126907925)
                ·
                  refine ⟨413247633243128443448809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8815949509186740126907925 413247633243128443448809)
                  ·
                    rfl

theorem cell21_1810793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_1810793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810793 prefixEnd_1810793 := by exact prefixLift 1810793
  have htrace : WordTrace (prefixWord ++ tailWord_1810793) baseStart_1810793 baseEnd_1810793 := by
    simpa [prefixWord, tailWord_1810793, baseEnd_1810793] using wordTrace_append hprefix tailTrace_1810793
  have hstable : (prefixWord ++ tailWord_1810793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810793).length < 2 ^ (prefixWord ++ tailWord_1810793).sum := by decide
  have hdescent : baseEnd_1810793 < baseStart_1810793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810796 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_1810796 : Nat := 118140960795 + 1810796 * 2 ^ 59
def prefixEnd_1810796 : Nat := 4983230072969 + 3 ^ 40 * 1810796 * 2
def baseEnd_1810796 : Nat := 413248317884001104898803

theorem tailTrace_1810796 : CollatzResearch.WordTrace tailWord_1810796 prefixEnd_1810796 413248317884001104898803 := by
  unfold tailWord_1810796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33022577973901413090258121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44030103965201884120344161 33022577973901413090258121)
  ·
    refine ⟨24766933480426059817693591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33022577973901413090258121 24766933480426059817693591)
    ·
      refine ⟨37150400220639089726540387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24766933480426059817693591 37150400220639089726540387)
      ·
        refine ⟨55725600330958634589810581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37150400220639089726540387 55725600330958634589810581)
        ·
          refine ⟨2612137515513685996397371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55725600330958634589810581 2612137515513685996397371)
          ·
            refine ⟨3918206273270528994596057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612137515513685996397371 3918206273270528994596057)
            ·
              refine ⟨2938654704952896745947043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918206273270528994596057 2938654704952896745947043)
              ·
                refine ⟨4407982057429345118920565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938654704952896745947043 4407982057429345118920565)
                ·
                  refine ⟨413248317884001104898803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4407982057429345118920565 413248317884001104898803)
                  ·
                    rfl

theorem cell21_1810796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_1810796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810796 prefixEnd_1810796 := by exact prefixLift 1810796
  have htrace : WordTrace (prefixWord ++ tailWord_1810796) baseStart_1810796 baseEnd_1810796 := by
    simpa [prefixWord, tailWord_1810796, baseEnd_1810796] using wordTrace_append hprefix tailTrace_1810796
  have hstable : (prefixWord ++ tailWord_1810796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810796).length < 2 ^ (prefixWord ++ tailWord_1810796).sum := by decide
  have hdescent : baseEnd_1810796 < baseStart_1810796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810824 : List Nat := [2, 1, 3, 3, 1, 1, 3, 7]
def baseStart_1810824 : Nat := 118140960795 + 1810824 * 2 ^ 59
def prefixEnd_1810824 : Nat := 4983230072969 + 3 ^ 40 * 1810824 * 2
def baseEnd_1810824 : Nat := 137751569288493092810693

theorem tailTrace_1810824 : CollatzResearch.WordTrace tailWord_1810824 prefixEnd_1810824 137751569288493092810693 := by
  unfold tailWord_1810824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33023088595850693481267763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44030784794467591308357017 33023088595850693481267763)
  ·
    refine ⟨49534632893776040221901645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33023088595850693481267763 49534632893776040221901645)
    ·
      refine ⟨18575487335166015083213117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49534632893776040221901645 18575487335166015083213117)
      ·
        refine ⟨6965807750687255656204919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18575487335166015083213117 6965807750687255656204919)
        ·
          refine ⟨10448711626030883484307379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965807750687255656204919 10448711626030883484307379)
          ·
            refine ⟨15673067439046325226461069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448711626030883484307379 15673067439046325226461069)
            ·
              refine ⟨5877400289642371959922901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15673067439046325226461069 5877400289642371959922901)
              ·
                refine ⟨137751569288493092810693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5877400289642371959922901 137751569288493092810693)
                ·
                  rfl

theorem cell21_1810824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_1810824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810824 prefixEnd_1810824 := by exact prefixLift 1810824
  have htrace : WordTrace (prefixWord ++ tailWord_1810824) baseStart_1810824 baseEnd_1810824 := by
    simpa [prefixWord, tailWord_1810824, baseEnd_1810824] using wordTrace_append hprefix tailTrace_1810824
  have hstable : (prefixWord ++ tailWord_1810824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810824).length < 2 ^ (prefixWord ++ tailWord_1810824).sum := by decide
  have hdescent : baseEnd_1810824 < baseStart_1810824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810830 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1810830 : Nat := 118140960795 + 1810830 * 2 ^ 59
def prefixEnd_1810830 : Nat := 4983230072969 + 3 ^ 40 * 1810830 * 2
def baseEnd_1810830 : Nat := 413256077147224601332067

theorem tailTrace_1810830 : CollatzResearch.WordTrace tailWord_1810830 prefixEnd_1810830 413256077147224601332067 := by
  unfold tailWord_1810830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255799503709956248406743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44030930686453099991502629 8255799503709956248406743)
  ·
    refine ⟨12383699255564934372610115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8255799503709956248406743 12383699255564934372610115)
    ·
      refine ⟨18575548883347401558915173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383699255564934372610115 18575548883347401558915173)
      ·
        refine ⟨3482915415627637792296595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18575548883347401558915173 3482915415627637792296595)
        ·
          refine ⟨5224373123441456688444893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482915415627637792296595 5224373123441456688444893)
          ·
            refine ⟨1959139921290546258166835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5224373123441456688444893 1959139921290546258166835)
            ·
              refine ⟨2938709881935819387250253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959139921290546258166835 2938709881935819387250253)
              ·
                refine ⟨1102016205725932270218845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938709881935819387250253 1102016205725932270218845)
                ·
                  refine ⟨413256077147224601332067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102016205725932270218845 413256077147224601332067)
                  ·
                    rfl

theorem cell21_1810830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1810830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810830 prefixEnd_1810830 := by exact prefixLift 1810830
  have htrace : WordTrace (prefixWord ++ tailWord_1810830) baseStart_1810830 baseEnd_1810830 := by
    simpa [prefixWord, tailWord_1810830, baseEnd_1810830] using wordTrace_append hprefix tailTrace_1810830
  have hstable : (prefixWord ++ tailWord_1810830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810830).length < 2 ^ (prefixWord ++ tailWord_1810830).sum := by decide
  have hdescent : baseEnd_1810830 < baseStart_1810830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810861 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1810861 : Nat := 118140960795 + 1810861 * 2 ^ 59
def prefixEnd_1810861 : Nat := 4983230072969 + 3 ^ 40 * 1810861 * 2
def baseEnd_1810861 : Nat := 413263151769575436315337

theorem tailTrace_1810861 : CollatzResearch.WordTrace tailWord_1810861 prefixEnd_1810861 413263151769575436315337 := by
  unfold tailWord_1810861
  simp only [CollatzResearch.WordTrace]
  refine ⟨66047526692567342281632437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44031684461711561521088291 66047526692567342281632437)
  ·
    refine ⟨6191955627428188338903041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66047526692567342281632437 6191955627428188338903041)
    ·
      refine ⟨4643966720571141254177281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6191955627428188338903041 4643966720571141254177281)
      ·
        refine ⟨3482975040428355940632961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4643966720571141254177281 3482975040428355940632961)
        ·
          refine ⟨2612231280321266955474721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482975040428355940632961 2612231280321266955474721)
          ·
            refine ⟨1959173460240950216606041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612231280321266955474721 1959173460240950216606041)
            ·
              refine ⟨1469380095180712662454531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959173460240950216606041 1469380095180712662454531)
              ·
                refine ⟨2204070142771068993681797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469380095180712662454531 2204070142771068993681797)
                ·
                  refine ⟨413263151769575436315337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204070142771068993681797 413263151769575436315337)
                  ·
                    rfl

theorem cell21_1810861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1810861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810861 prefixEnd_1810861 := by exact prefixLift 1810861
  have htrace : WordTrace (prefixWord ++ tailWord_1810861) baseStart_1810861 baseEnd_1810861 := by
    simpa [prefixWord, tailWord_1810861, baseEnd_1810861] using wordTrace_append hprefix tailTrace_1810861
  have hstable : (prefixWord ++ tailWord_1810861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810861).length < 2 ^ (prefixWord ++ tailWord_1810861).sum := by decide
  have hdescent : baseEnd_1810861 < baseStart_1810861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810900 : List Nat := [2, 4, 1, 2, 2, 10]
def baseStart_1810900 : Nat := 118140960795 + 1810900 * 2 ^ 59
def prefixEnd_1810900 : Nat := 4983230072969 + 3 ^ 40 * 1810900 * 2
def baseEnd_1810900 : Nat := 15306372300034075376491

theorem tailTrace_1810900 : CollatzResearch.WordTrace tailWord_1810900 prefixEnd_1810900 15306372300034075376491 := by
  unfold tailWord_1810900
  simp only [CollatzResearch.WordTrace]
  refine ⟨33024474569713025971151077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44032632759617367961534769 33024474569713025971151077)
  ·
    refine ⟨6192088981821192369590827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33024474569713025971151077 6192088981821192369590827)
    ·
      refine ⟨9288133472731788554386241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6192088981821192369590827 9288133472731788554386241)
      ·
        refine ⟨6966100104548841415789681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9288133472731788554386241 6966100104548841415789681)
        ·
          refine ⟨5224575078411631061842261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6966100104548841415789681 5224575078411631061842261)
          ·
            refine ⟨15306372300034075376491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5224575078411631061842261 15306372300034075376491)
            ·
              rfl

theorem cell21_1810900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 10].length) (baseStart_1810900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810900 prefixEnd_1810900 := by exact prefixLift 1810900
  have htrace : WordTrace (prefixWord ++ tailWord_1810900) baseStart_1810900 baseEnd_1810900 := by
    simpa [prefixWord, tailWord_1810900, baseEnd_1810900] using wordTrace_append hprefix tailTrace_1810900
  have hstable : (prefixWord ++ tailWord_1810900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810900).length < 2 ^ (prefixWord ++ tailWord_1810900).sum := by decide
  have hdescent : baseEnd_1810900 < baseStart_1810900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810979 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 4]
def baseStart_1810979 : Nat := 118140960795 + 1810979 * 2 ^ 59
def prefixEnd_1810979 : Nat := 4983230072969 + 3 ^ 40 * 1810979 * 2
def baseEnd_1810979 : Nat := 413290080977233453348429

theorem tailTrace_1810979 : CollatzResearch.WordTrace tailWord_1810979 prefixEnd_1810979 413290080977233453348429 := by
  unfold tailWord_1810979
  simp only [CollatzResearch.WordTrace]
  refine ⟨66051830506139848434427991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44034553670759898956285327 66051830506139848434427991)
  ·
    refine ⟨99077745759209772651641987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66051830506139848434427991 99077745759209772651641987)
    ·
      refine ⟨148616618638814658977462981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99077745759209772651641987 148616618638814658977462981)
      ·
        refine ⟨27865615994777748558274309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148616618638814658977462981 27865615994777748558274309)
        ·
          refine ⟨5224802999020827854676433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27865615994777748558274309 5224802999020827854676433)
          ·
            refine ⟨3918602249265620891007325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224802999020827854676433 3918602249265620891007325)
            ·
              refine ⟨1469475843474607834127747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3918602249265620891007325 1469475843474607834127747)
              ·
                refine ⟨2204213765211911751191621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469475843474607834127747 2204213765211911751191621)
                ·
                  refine ⟨413290080977233453348429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204213765211911751191621 413290080977233453348429)
                  ·
                    rfl

theorem cell21_1810979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4].length) (baseStart_1810979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1810979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1810979 prefixEnd_1810979 := by exact prefixLift 1810979
  have htrace : WordTrace (prefixWord ++ tailWord_1810979) baseStart_1810979 baseEnd_1810979 := by
    simpa [prefixWord, tailWord_1810979, baseEnd_1810979] using wordTrace_append hprefix tailTrace_1810979
  have hstable : (prefixWord ++ tailWord_1810979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810979).length < 2 ^ (prefixWord ++ tailWord_1810979).sum := by decide
  have hdescent : baseEnd_1810979 < baseStart_1810979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811097 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_1811097 : Nat := 118140960795 + 1811097 * 2 ^ 59
def prefixEnd_1811097 : Nat := 4983230072969 + 3 ^ 40 * 1811097 * 2
def baseEnd_1811097 : Nat := 413317010184891470381521

theorem tailTrace_1811097 : CollatzResearch.WordTrace tailWord_1811097 prefixEnd_1811097 413317010184891470381521 := by
  unfold tailWord_1811097
  simp only [CollatzResearch.WordTrace]
  refine ⟨66056134319712354587223545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44037422879808236391482363 66056134319712354587223545)
  ·
    refine ⟨49542100739784265940417659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66056134319712354587223545 49542100739784265940417659)
    ·
      refine ⟨74313151109676398910626489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49542100739784265940417659 74313151109676398910626489)
      ·
        refine ⟨55734863332257299182969867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74313151109676398910626489 55734863332257299182969867)
        ·
          refine ⟨83602294998385948774454801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55734863332257299182969867 83602294998385948774454801)
          ·
            refine ⟨62701721248789461580841101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83602294998385948774454801 62701721248789461580841101)
            ·
              refine ⟨23513145468296048092815413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62701721248789461580841101 23513145468296048092815413)
              ·
                refine ⟨2204357387652754508701445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23513145468296048092815413 2204357387652754508701445)
                ·
                  refine ⟨413317010184891470381521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204357387652754508701445 413317010184891470381521)
                  ·
                    rfl

theorem cell21_1811097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_1811097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811097 prefixEnd_1811097 := by exact prefixLift 1811097
  have htrace : WordTrace (prefixWord ++ tailWord_1811097) baseStart_1811097 baseEnd_1811097 := by
    simpa [prefixWord, tailWord_1811097, baseEnd_1811097] using wordTrace_append hprefix tailTrace_1811097
  have hstable : (prefixWord ++ tailWord_1811097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811097).length < 2 ^ (prefixWord ++ tailWord_1811097).sum := by decide
  have hdescent : baseEnd_1811097 < baseStart_1811097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811117 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1811117 : Nat := 118140960795 + 1811117 * 2 ^ 59
def prefixEnd_1811117 : Nat := 4983230072969 + 3 ^ 40 * 1811117 * 2
def baseEnd_1811117 : Nat := 413321574457375880048147

theorem tailTrace_1811117 : CollatzResearch.WordTrace tailWord_1811117 prefixEnd_1811117 413321574457375880048147 := by
  unfold tailWord_1811117
  simp only [CollatzResearch.WordTrace]
  refine ⟨66056863779639898002951605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44037909186426598668634403 66056863779639898002951605)
  ·
    refine ⟨6192830979341240437776713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66056863779639898002951605 6192830979341240437776713)
    ·
      refine ⟨4644623234505930328332535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6192830979341240437776713 4644623234505930328332535)
      ·
        refine ⟨6966934851758895492498803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644623234505930328332535 6966934851758895492498803)
        ·
          refine ⟨10450402277638343238748205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966934851758895492498803 10450402277638343238748205)
          ·
            refine ⟨3918900854114378714530577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10450402277638343238748205 3918900854114378714530577)
            ·
              refine ⟨2939175640585784035897933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918900854114378714530577 2939175640585784035897933)
              ·
                refine ⟨1102190865219669013461725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2939175640585784035897933 1102190865219669013461725)
                ·
                  refine ⟨413321574457375880048147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102190865219669013461725 413321574457375880048147)
                  ·
                    rfl

theorem cell21_1811117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1811117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811117 prefixEnd_1811117 := by exact prefixLift 1811117
  have htrace : WordTrace (prefixWord ++ tailWord_1811117) baseStart_1811117 baseEnd_1811117 := by
    simpa [prefixWord, tailWord_1811117, baseEnd_1811117] using wordTrace_append hprefix tailTrace_1811117
  have hstable : (prefixWord ++ tailWord_1811117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811117).length < 2 ^ (prefixWord ++ tailWord_1811117).sum := by decide
  have hdescent : baseEnd_1811117 < baseStart_1811117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811173 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_1811173 : Nat := 118140960795 + 1811173 * 2 ^ 59
def prefixEnd_1811173 : Nat := 4983230072969 + 3 ^ 40 * 1811173 * 2
def baseEnd_1811173 : Nat := 413334354420332227114699

theorem tailTrace_1811173 : CollatzResearch.WordTrace tailWord_1811173 prefixEnd_1811173 413334354420332227114699 := by
  unfold tailWord_1811173
  simp only [CollatzResearch.WordTrace]
  refine ⟨66058906267437019566990173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44039270844958013044660115 66058906267437019566990173)
  ·
    refine ⟨24772089850288882337621315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66058906267437019566990173 24772089850288882337621315)
    ·
      refine ⟨37158134775433323506431973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24772089850288882337621315 37158134775433323506431973)
      ·
        refine ⟨6967150270393748157455995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37158134775433323506431973 6967150270393748157455995)
        ·
          refine ⟨10450725405590622236183993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967150270393748157455995 10450725405590622236183993)
          ·
            refine ⟨7838044054192966677137995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450725405590622236183993 7838044054192966677137995)
            ·
              refine ⟨11757066081289450015706993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838044054192966677137995 11757066081289450015706993)
              ·
                refine ⟨8817799560967087511780245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11757066081289450015706993 8817799560967087511780245)
                ·
                  refine ⟨413334354420332227114699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8817799560967087511780245 413334354420332227114699)
                  ·
                    rfl

theorem cell21_1811173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_1811173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811173 prefixEnd_1811173 := by exact prefixLift 1811173
  have htrace : WordTrace (prefixWord ++ tailWord_1811173) baseStart_1811173 baseEnd_1811173 := by
    simpa [prefixWord, tailWord_1811173, baseEnd_1811173] using wordTrace_append hprefix tailTrace_1811173
  have hstable : (prefixWord ++ tailWord_1811173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811173).length < 2 ^ (prefixWord ++ tailWord_1811173).sum := by decide
  have hdescent : baseEnd_1811173 < baseStart_1811173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811190 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1811190 : Nat := 118140960795 + 1811190 * 2 ^ 59
def prefixEnd_1811190 : Nat := 4983230072969 + 3 ^ 40 * 1811190 * 2
def baseEnd_1811190 : Nat := 413338234051943975331331

theorem tailTrace_1811190 : CollatzResearch.WordTrace tailWord_1811190 prefixEnd_1811190 413338234051943975331331 := by
  unfold tailWord_1811190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128720394273464466897439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44039684205583620980239349 4128720394273464466897439)
  ·
    refine ⟨6193080591410196700346159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128720394273464466897439 6193080591410196700346159)
    ·
      refine ⟨9289620887115295050519239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193080591410196700346159 9289620887115295050519239)
      ·
        refine ⟨13934431330672942575778859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289620887115295050519239 13934431330672942575778859)
        ·
          refine ⟨20901646996009413863668289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934431330672942575778859 20901646996009413863668289)
          ·
            refine ⟨15676235247007060397751217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901646996009413863668289 15676235247007060397751217)
            ·
              refine ⟨11757176435255295298313413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15676235247007060397751217 11757176435255295298313413)
              ·
                refine ⟨2204470581610367868433765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11757176435255295298313413 2204470581610367868433765)
                ·
                  refine ⟨413338234051943975331331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204470581610367868433765 413338234051943975331331)
                  ·
                    rfl

theorem cell21_1811190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1811190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811190 prefixEnd_1811190 := by exact prefixLift 1811190
  have htrace : WordTrace (prefixWord ++ tailWord_1811190) baseStart_1811190 baseEnd_1811190 := by
    simpa [prefixWord, tailWord_1811190, baseEnd_1811190] using wordTrace_append hprefix tailTrace_1811190
  have hstable : (prefixWord ++ tailWord_1811190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811190).length < 2 ^ (prefixWord ++ tailWord_1811190).sum := by decide
  have hdescent : baseEnd_1811190 < baseStart_1811190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811204 : List Nat := [2, 3, 2, 2, 1, 1, 4, 6]
def baseStart_1811204 : Nat := 118140960795 + 1811204 * 2 ^ 59
def prefixEnd_1811204 : Nat := 4983230072969 + 3 ^ 40 * 1811204 * 2
def baseEnd_1811204 : Nat := 137780476347561020699323

theorem tailTrace_1811204 : CollatzResearch.WordTrace tailWord_1811204 prefixEnd_1811204 137780476347561020699323 := by
  unfold tailWord_1811204
  simp only [CollatzResearch.WordTrace]
  refine ⟨33030018465162355930684333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44040024620216474574245777 33030018465162355930684333)
  ·
    refine ⟨12386256924435883474006625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33030018465162355930684333 12386256924435883474006625)
    ·
      refine ⟨9289692693326912605504969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12386256924435883474006625 9289692693326912605504969)
      ·
        refine ⟨6967269519995184454128727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9289692693326912605504969 6967269519995184454128727)
        ·
          refine ⟨10450904279992776681193091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967269519995184454128727 10450904279992776681193091)
          ·
            refine ⟨15676356419989165021789637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10450904279992776681193091 15676356419989165021789637)
            ·
              refine ⟨2939316828747968441585557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15676356419989165021789637 2939316828747968441585557)
              ·
                refine ⟨137780476347561020699323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2939316828747968441585557 137780476347561020699323)
                ·
                  rfl

theorem cell21_1811204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_1811204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811204 prefixEnd_1811204 := by exact prefixLift 1811204
  have htrace : WordTrace (prefixWord ++ tailWord_1811204) baseStart_1811204 baseEnd_1811204 := by
    simpa [prefixWord, tailWord_1811204, baseEnd_1811204] using wordTrace_append hprefix tailTrace_1811204
  have hstable : (prefixWord ++ tailWord_1811204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811204).length < 2 ^ (prefixWord ++ tailWord_1811204).sum := by decide
  have hdescent : baseEnd_1811204 < baseStart_1811204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811207 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 4]
def baseStart_1811207 : Nat := 118140960795 + 1811207 * 2 ^ 59
def prefixEnd_1811207 : Nat := 4983230072969 + 3 ^ 40 * 1811207 * 2
def baseEnd_1811207 : Nat := 413342113683555723547963

theorem tailTrace_1811207 : CollatzResearch.WordTrace tailWord_1811207 prefixEnd_1811207 413342113683555723547963 := by
  unfold tailWord_1811207
  simp only [CollatzResearch.WordTrace]
  refine ⟨66060146349313843373727875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44040097566209228915818583 66060146349313843373727875)
  ·
    refine ⟨99090219523970765060591813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66060146349313843373727875 99090219523970765060591813)
    ·
      refine ⟨18579416160744518448860965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99090219523970765060591813 18579416160744518448860965)
      ·
        refine ⟨3483640530139597209161431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18579416160744518448860965 3483640530139597209161431)
        ·
          refine ⟨5225460795209395813742147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483640530139597209161431 5225460795209395813742147)
          ·
            refine ⟨7838191192814093720613221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225460795209395813742147 7838191192814093720613221)
            ·
              refine ⟨1469660848652642572614979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7838191192814093720613221 1469660848652642572614979)
              ·
                refine ⟨2204491272978963858922469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469660848652642572614979 2204491272978963858922469)
                ·
                  refine ⟨413342113683555723547963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204491272978963858922469 413342113683555723547963)
                  ·
                    rfl

theorem cell21_1811207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4].length) (baseStart_1811207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811207 prefixEnd_1811207 := by exact prefixLift 1811207
  have htrace : WordTrace (prefixWord ++ tailWord_1811207) baseStart_1811207 baseEnd_1811207 := by
    simpa [prefixWord, tailWord_1811207, baseEnd_1811207] using wordTrace_append hprefix tailTrace_1811207
  have hstable : (prefixWord ++ tailWord_1811207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811207).length < 2 ^ (prefixWord ++ tailWord_1811207).sum := by decide
  have hdescent : baseEnd_1811207 < baseStart_1811207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811235 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 3]
def baseStart_1811235 : Nat := 118140960795 + 1811235 * 2 ^ 59
def prefixEnd_1811235 : Nat := 4983230072969 + 3 ^ 40 * 1811235 * 2
def baseEnd_1811235 : Nat := 413348503665033897081239

theorem tailTrace_1811235 : CollatzResearch.WordTrace tailWord_1811235 prefixEnd_1811235 413348503665033897081239 := by
  unfold tailWord_1811235
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061167593212404155747159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44040778395474936103831439 66061167593212404155747159)
  ·
    refine ⟨99091751389818606233620739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66061167593212404155747159 99091751389818606233620739)
    ·
      refine ⟨148637627084727909350431109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99091751389818606233620739 148637627084727909350431109)
      ·
        refine ⟨27869555078386483003205833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148637627084727909350431109 27869555078386483003205833)
        ·
          refine ⟨20902166308789862252404375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27869555078386483003205833 20902166308789862252404375)
          ·
            refine ⟨31353249463184793378606563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20902166308789862252404375 31353249463184793378606563)
            ·
              refine ⟨47029874194777190067909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31353249463184793378606563 47029874194777190067909845)
              ·
                refine ⟨1102262676440090392216637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47029874194777190067909845 1102262676440090392216637)
                ·
                  refine ⟨413348503665033897081239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102262676440090392216637 413348503665033897081239)
                  ·
                    rfl

theorem cell21_1811235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3].length) (baseStart_1811235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811235 prefixEnd_1811235 := by exact prefixLift 1811235
  have htrace : WordTrace (prefixWord ++ tailWord_1811235) baseStart_1811235 baseEnd_1811235 := by
    simpa [prefixWord, tailWord_1811235, baseEnd_1811235] using wordTrace_append hprefix tailTrace_1811235
  have hstable : (prefixWord ++ tailWord_1811235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811235).length < 2 ^ (prefixWord ++ tailWord_1811235).sum := by decide
  have hdescent : baseEnd_1811235 < baseStart_1811235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811325 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1811325 : Nat := 118140960795 + 1811325 * 2 ^ 59
def prefixEnd_1811325 : Nat := 4983230072969 + 3 ^ 40 * 1811325 * 2
def baseEnd_1811325 : Nat := 413369042891213740581055

theorem tailTrace_1811325 : CollatzResearch.WordTrace tailWord_1811325 prefixEnd_1811325 413369042891213740581055 := by
  unfold tailWord_1811325
  simp only [CollatzResearch.WordTrace]
  refine ⟨66064450162886349526523429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44042966775257566351015619 66064450162886349526523429)
  ·
    refine ⟨12387084405541190536223143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66064450162886349526523429 12387084405541190536223143)
    ·
      refine ⟨18580626608311785804334715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12387084405541190536223143 18580626608311785804334715)
      ·
        refine ⟨27870939912467678706502073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18580626608311785804334715 27870939912467678706502073)
        ·
          refine ⟨20903204934350759029876555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27870939912467678706502073 20903204934350759029876555)
          ·
            refine ⟨31354807401526138544814833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20903204934350759029876555 31354807401526138544814833)
            ·
              refine ⟨23516105551144603908611125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31354807401526138544814833 23516105551144603908611125)
              ·
                refine ⟨2204634895419806616432293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23516105551144603908611125 2204634895419806616432293)
                ·
                  refine ⟨413369042891213740581055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204634895419806616432293 413369042891213740581055)
                  ·
                    rfl

theorem cell21_1811325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1811325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811325 prefixEnd_1811325 := by exact prefixLift 1811325
  have htrace : WordTrace (prefixWord ++ tailWord_1811325) baseStart_1811325 baseEnd_1811325 := by
    simpa [prefixWord, tailWord_1811325, baseEnd_1811325] using wordTrace_append hprefix tailTrace_1811325
  have hstable : (prefixWord ++ tailWord_1811325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811325).length < 2 ^ (prefixWord ++ tailWord_1811325).sum := by decide
  have hdescent : baseEnd_1811325 < baseStart_1811325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811418 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1811418 : Nat := 118140960795 + 1811418 * 2 ^ 59
def prefixEnd_1811418 : Nat := 4983230072969 + 3 ^ 40 * 1811418 * 2
def baseEnd_1811418 : Nat := 413390266758266245530865

theorem tailTrace_1811418 : CollatzResearch.WordTrace tailWord_1811418 prefixEnd_1811418 413390266758266245530865 := by
  unfold tailWord_1811418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516960537887356602414727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44045228101032950939772605 16516960537887356602414727)
  ·
    refine ⟨24775440806831034903622091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16516960537887356602414727 24775440806831034903622091)
    ·
      refine ⟨37163161210246552355433137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24775440806831034903622091 37163161210246552355433137)
      ·
        refine ⟨27872370907684914266574853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37163161210246552355433137 27872370907684914266574853)
        ·
          refine ⟨5226069545190921424982785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27872370907684914266574853 5226069545190921424982785)
          ·
            refine ⟨3919552158893191068737089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5226069545190921424982785 3919552158893191068737089)
            ·
              refine ⟨2939664119169893301552817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919552158893191068737089 2939664119169893301552817)
              ·
                refine ⟨2204748089377419976164613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939664119169893301552817 2204748089377419976164613)
                ·
                  refine ⟨413390266758266245530865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204748089377419976164613 413390266758266245530865)
                  ·
                    rfl

theorem cell21_1811418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1811418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811418 prefixEnd_1811418 := by exact prefixLift 1811418
  have htrace : WordTrace (prefixWord ++ tailWord_1811418) baseStart_1811418 baseEnd_1811418 := by
    simpa [prefixWord, tailWord_1811418, baseEnd_1811418] using wordTrace_append hprefix tailTrace_1811418
  have hstable : (prefixWord ++ tailWord_1811418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811418).length < 2 ^ (prefixWord ++ tailWord_1811418).sum := by decide
  have hdescent : baseEnd_1811418 < baseStart_1811418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811421 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1811421 : Nat := 118140960795 + 1811421 * 2 ^ 59
def prefixEnd_1811421 : Nat := 4983230072969 + 3 ^ 40 * 1811421 * 2
def baseEnd_1811421 : Nat := 413390951399138906980859

theorem tailTrace_1811421 : CollatzResearch.WordTrace tailWord_1811421 prefixEnd_1811421 413390951399138906980859 := by
  unfold tailWord_1811421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66067951570538557922018117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44045301047025705281345411 66067951570538557922018117)
  ·
    refine ⟨12387740919475979610378397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66067951570538557922018117 12387740919475979610378397)
    ·
      refine ⟨4645402844803492353891899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12387740919475979610378397 4645402844803492353891899)
      ·
        refine ⟨6968104267205238530837849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645402844803492353891899 6968104267205238530837849)
        ·
          refine ⟨5226078200403928898128387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968104267205238530837849 5226078200403928898128387)
          ·
            refine ⟨7839117300605893347192581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226078200403928898128387 7839117300605893347192581)
            ·
              refine ⟨1469834493863605002598609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7839117300605893347192581 1469834493863605002598609)
              ·
                refine ⟨1102375870397703751948957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469834493863605002598609 1102375870397703751948957)
                ·
                  refine ⟨413390951399138906980859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102375870397703751948957 413390951399138906980859)
                  ·
                    rfl

theorem cell21_1811421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1811421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811421 prefixEnd_1811421 := by exact prefixLift 1811421
  have htrace : WordTrace (prefixWord ++ tailWord_1811421) baseStart_1811421 baseEnd_1811421 := by
    simpa [prefixWord, tailWord_1811421, baseEnd_1811421] using wordTrace_append hprefix tailTrace_1811421
  have hstable : (prefixWord ++ tailWord_1811421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811421).length < 2 ^ (prefixWord ++ tailWord_1811421).sum := by decide
  have hdescent : baseEnd_1811421 < baseStart_1811421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811477 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1811477 : Nat := 118140960795 + 1811477 * 2 ^ 59
def prefixEnd_1811477 : Nat := 4983230072969 + 3 ^ 40 * 1811477 * 2
def baseEnd_1811477 : Nat := 413403731362095254047411

theorem tailTrace_1811477 : CollatzResearch.WordTrace tailWord_1811477 prefixEnd_1811477 413403731362095254047411 := by
  unfold tailWord_1811477
  simp only [CollatzResearch.WordTrace]
  refine ⟨66069994058335679486056685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44046662705557119657371123 66069994058335679486056685)
  ·
    refine ⟨24776247771875879807271257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66069994058335679486056685 24776247771875879807271257)
    ·
      refine ⟨18582185828906909855453443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24776247771875879807271257 18582185828906909855453443)
      ·
        refine ⟨27873278743360364783180165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582185828906909855453443 27873278743360364783180165)
        ·
          refine ⟨5226239764380068396846281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27873278743360364783180165 5226239764380068396846281)
          ·
            refine ⟨3919679823285051297634711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5226239764380068396846281 3919679823285051297634711)
            ·
              refine ⟨5879519734927576946452067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919679823285051297634711 5879519734927576946452067)
              ·
                refine ⟨8819279602391365419678101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879519734927576946452067 8819279602391365419678101)
                ·
                  refine ⟨413403731362095254047411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8819279602391365419678101 413403731362095254047411)
                  ·
                    rfl

theorem cell21_1811477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1811477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811477 prefixEnd_1811477 := by exact prefixLift 1811477
  have htrace : WordTrace (prefixWord ++ tailWord_1811477) baseStart_1811477 baseEnd_1811477 := by
    simpa [prefixWord, tailWord_1811477, baseEnd_1811477] using wordTrace_append hprefix tailTrace_1811477
  have hstable : (prefixWord ++ tailWord_1811477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811477).length < 2 ^ (prefixWord ++ tailWord_1811477).sum := by decide
  have hdescent : baseEnd_1811477 < baseStart_1811477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811542 : List Nat := [5, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1811542 : Nat := 118140960795 + 1811542 * 2 ^ 59
def prefixEnd_1811542 : Nat := 4983230072969 + 3 ^ 40 * 1811542 * 2
def baseEnd_1811542 : Nat := 137806188415889861821315

theorem tailTrace_1811542 : CollatzResearch.WordTrace tailWord_1811542 prefixEnd_1811542 137806188415889861821315 := by
  unfold tailWord_1811542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129522800193762224198305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44048243202066797058115253 4129522800193762224198305)
  ·
    refine ⟨3097142100145321668148729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4129522800193762224198305 3097142100145321668148729)
    ·
      refine ⟨2322856575108991251111547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3097142100145321668148729 2322856575108991251111547)
      ·
        refine ⟨3484284862663486876667321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322856575108991251111547 3484284862663486876667321)
        ·
          refine ⟨2613213646997615157500491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484284862663486876667321 2613213646997615157500491)
          ·
            refine ⟨3919820470496422736250737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613213646997615157500491 3919820470496422736250737)
            ·
              refine ⟨2939865352872317052188053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919820470496422736250737 2939865352872317052188053)
              ·
                refine ⟨137806188415889861821315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2939865352872317052188053 137806188415889861821315)
                ·
                  rfl

theorem cell21_1811542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1811542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811542 prefixEnd_1811542 := by exact prefixLift 1811542
  have htrace : WordTrace (prefixWord ++ tailWord_1811542) baseStart_1811542 baseEnd_1811542 := by
    simpa [prefixWord, tailWord_1811542, baseEnd_1811542] using wordTrace_append hprefix tailTrace_1811542
  have hstable : (prefixWord ++ tailWord_1811542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811542).length < 2 ^ (prefixWord ++ tailWord_1811542).sum := by decide
  have hdescent : baseEnd_1811542 < baseStart_1811542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811615 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_1811615 : Nat := 118140960795 + 1811615 * 2 ^ 59
def prefixEnd_1811615 : Nat := 4983230072969 + 3 ^ 40 * 1811615 * 2
def baseEnd_1811615 : Nat := 413435224842237680747129

theorem tailTrace_1811615 : CollatzResearch.WordTrace tailWord_1811615 prefixEnd_1811615 413435224842237680747129 := by
  unfold tailWord_1811615
  simp only [CollatzResearch.WordTrace]
  refine ⟨66075027331835729054580299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44050018221223819369720199 66075027331835729054580299)
  ·
    refine ⟨99112540997753593581870449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66075027331835729054580299 99112540997753593581870449)
    ·
      refine ⟨74334405748315195186402837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99112540997753593581870449 74334405748315195186402837)
      ·
        refine ⟨3484425269452274774362633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74334405748315195186402837 3484425269452274774362633)
        ·
          refine ⟨2613318952089206080771975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484425269452274774362633 2613318952089206080771975)
          ·
            refine ⟨3919978428133809121157963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613318952089206080771975 3919978428133809121157963)
            ·
              refine ⟨5879967642200713681736945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919978428133809121157963 5879967642200713681736945)
              ·
                refine ⟨4409975731650535261302709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5879967642200713681736945 4409975731650535261302709)
                ·
                  refine ⟨413435224842237680747129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4409975731650535261302709 413435224842237680747129)
                  ·
                    rfl

theorem cell21_1811615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_1811615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811615 prefixEnd_1811615 := by exact prefixLift 1811615
  have htrace : WordTrace (prefixWord ++ tailWord_1811615) baseStart_1811615 baseEnd_1811615 := by
    simpa [prefixWord, tailWord_1811615, baseEnd_1811615] using wordTrace_append hprefix tailTrace_1811615
  have hstable : (prefixWord ++ tailWord_1811615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811615).length < 2 ^ (prefixWord ++ tailWord_1811615).sum := by decide
  have hdescent : baseEnd_1811615 < baseStart_1811615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811646 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1811646 : Nat := 118140960795 + 1811646 * 2 ^ 59
def prefixEnd_1811646 : Nat := 4983230072969 + 3 ^ 40 * 1811646 * 2
def baseEnd_1811646 : Nat := 413442299464588515730399

theorem tailTrace_1811646 : CollatzResearch.WordTrace tailWord_1811646 prefixEnd_1811646 413442299464588515730399 := by
  unfold tailWord_1811646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259519749340427668619849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44050771996482280899305861 8259519749340427668619849)
  ·
    refine ⟨6194639812005320751464887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8259519749340427668619849 6194639812005320751464887)
    ·
      refine ⟨9291959718007981127197331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194639812005320751464887 9291959718007981127197331)
      ·
        refine ⟨13937939577011971690795997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9291959718007981127197331 13937939577011971690795997)
        ·
          refine ⟨5226727341379489384048499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13937939577011971690795997 5226727341379489384048499)
          ·
            refine ⟨7840091012069234076072749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226727341379489384048499 7840091012069234076072749)
            ·
              refine ⟨2940034129525962778527281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7840091012069234076072749 2940034129525962778527281)
              ·
                refine ⟨2205025597144472083895461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940034129525962778527281 2205025597144472083895461)
                ·
                  refine ⟨413442299464588515730399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205025597144472083895461 413442299464588515730399)
                  ·
                    rfl

theorem cell21_1811646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1811646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811646 prefixEnd_1811646 := by exact prefixLift 1811646
  have htrace : WordTrace (prefixWord ++ tailWord_1811646) baseStart_1811646 baseEnd_1811646 := by
    simpa [prefixWord, tailWord_1811646, baseEnd_1811646] using wordTrace_append hprefix tailTrace_1811646
  have hstable : (prefixWord ++ tailWord_1811646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811646).length < 2 ^ (prefixWord ++ tailWord_1811646).sum := by decide
  have hdescent : baseEnd_1811646 < baseStart_1811646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811688 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_1811688 : Nat := 118140960795 + 1811688 * 2 ^ 59
def prefixEnd_1811688 : Nat := 4983230072969 + 3 ^ 40 * 1811688 * 2
def baseEnd_1811688 : Nat := 413451884436805776030313

theorem tailTrace_1811688 : CollatzResearch.WordTrace tailWord_1811688 prefixEnd_1811688 413451884436805776030313 := by
  unfold tailWord_1811688
  simp only [CollatzResearch.WordTrace]
  refine ⟨33038844930285631260993859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44051793240380841681325145 33038844930285631260993859)
  ·
    refine ⟨49558267395428446891490789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33038844930285631260993859 49558267395428446891490789)
    ·
      refine ⟨9292175136642833792154523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49558267395428446891490789 9292175136642833792154523)
      ·
        refine ⟨13938262704964250688231785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292175136642833792154523 13938262704964250688231785)
        ·
          refine ⟨10453697028723188016173839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13938262704964250688231785 10453697028723188016173839)
          ·
            refine ⟨15680545543084782024260759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453697028723188016173839 15680545543084782024260759)
            ·
              refine ⟨23520818314627173036391139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680545543084782024260759 23520818314627173036391139)
              ·
                refine ⟨35281227471940759554586709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23520818314627173036391139 35281227471940759554586709)
                ·
                  refine ⟨413451884436805776030313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35281227471940759554586709 413451884436805776030313)
                  ·
                    rfl

theorem cell21_1811688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_1811688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811688 prefixEnd_1811688 := by exact prefixLift 1811688
  have htrace : WordTrace (prefixWord ++ tailWord_1811688) baseStart_1811688 baseEnd_1811688 := by
    simpa [prefixWord, tailWord_1811688, baseEnd_1811688] using wordTrace_append hprefix tailTrace_1811688
  have hstable : (prefixWord ++ tailWord_1811688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811688).length < 2 ^ (prefixWord ++ tailWord_1811688).sum := by decide
  have hdescent : baseEnd_1811688 < baseStart_1811688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811691 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 3]
def baseStart_1811691 : Nat := 118140960795 + 1811691 * 2 ^ 59
def prefixEnd_1811691 : Nat := 4983230072969 + 3 ^ 40 * 1811691 * 2
def baseEnd_1811691 : Nat := 413452569077678437480307

theorem tailTrace_1811691 : CollatzResearch.WordTrace tailWord_1811691 prefixEnd_1811691 413452569077678437480307 := by
  unfold tailWord_1811691
  simp only [CollatzResearch.WordTrace]
  refine ⟨66077799279560394034346927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44051866186373596022897951 66077799279560394034346927)
  ·
    refine ⟨99116698919340591051520391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66077799279560394034346927 99116698919340591051520391)
    ·
      refine ⟨148675048379010886577280587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99116698919340591051520391 148675048379010886577280587)
      ·
        refine ⟨223012572568516329865920881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148675048379010886577280587 223012572568516329865920881)
        ·
          refine ⟨167259429426387247399440661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223012572568516329865920881 167259429426387247399440661)
          ·
            refine ⟨7840285754361902221848781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167259429426387247399440661 7840285754361902221848781)
            ·
              refine ⟨2940107157885713333193293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7840285754361902221848781 2940107157885713333193293)
              ·
                refine ⟨1102540184207142499947485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2940107157885713333193293 1102540184207142499947485)
                ·
                  refine ⟨413452569077678437480307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102540184207142499947485 413452569077678437480307)
                  ·
                    rfl

theorem cell21_1811691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 3].length) (baseStart_1811691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811691 prefixEnd_1811691 := by exact prefixLift 1811691
  have htrace : WordTrace (prefixWord ++ tailWord_1811691) baseStart_1811691 baseEnd_1811691 := by
    simpa [prefixWord, tailWord_1811691, baseEnd_1811691] using wordTrace_append hprefix tailTrace_1811691
  have hstable : (prefixWord ++ tailWord_1811691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811691).length < 2 ^ (prefixWord ++ tailWord_1811691).sum := by decide
  have hdescent : baseEnd_1811691 < baseStart_1811691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811708 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_1811708 : Nat := 118140960795 + 1811708 * 2 ^ 59
def prefixEnd_1811708 : Nat := 4983230072969 + 3 ^ 40 * 1811708 * 2
def baseEnd_1811708 : Nat := 413456448709290185696939

theorem tailTrace_1811708 : CollatzResearch.WordTrace tailWord_1811708 prefixEnd_1811708 413456448709290185696939 := by
  unfold tailWord_1811708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33039209660249402968857889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44052279546999203958477185 33039209660249402968857889)
  ·
    refine ⟨24779407245187052226643417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33039209660249402968857889 24779407245187052226643417)
    ·
      refine ⟨18584555433890289169982563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24779407245187052226643417 18584555433890289169982563)
      ·
        refine ⟨27876833150835433754973845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584555433890289169982563 27876833150835433754973845)
        ·
          refine ⟨1306726553945410957264399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27876833150835433754973845 1306726553945410957264399)
          ·
            refine ⟨1960089830918116435896599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306726553945410957264399 1960089830918116435896599)
            ·
              refine ⟨2940134746377174653844899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960089830918116435896599 2940134746377174653844899)
              ·
                refine ⟨4410202119565761980767349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940134746377174653844899 4410202119565761980767349)
                ·
                  refine ⟨413456448709290185696939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4410202119565761980767349 413456448709290185696939)
                  ·
                    rfl

theorem cell21_1811708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_1811708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811708 prefixEnd_1811708 := by exact prefixLift 1811708
  have htrace : WordTrace (prefixWord ++ tailWord_1811708) baseStart_1811708 baseEnd_1811708 := by
    simpa [prefixWord, tailWord_1811708, baseEnd_1811708] using wordTrace_append hprefix tailTrace_1811708
  have hstable : (prefixWord ++ tailWord_1811708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811708).length < 2 ^ (prefixWord ++ tailWord_1811708).sum := by decide
  have hdescent : baseEnd_1811708 < baseStart_1811708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811733 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_1811733 : Nat := 118140960795 + 1811733 * 2 ^ 59
def prefixEnd_1811733 : Nat := 4983230072969 + 3 ^ 40 * 1811733 * 2
def baseEnd_1811733 : Nat := 413462154049895697780221

theorem tailTrace_1811733 : CollatzResearch.WordTrace tailWord_1811733 prefixEnd_1811733 413462154049895697780221 := by
  unfold tailWord_1811733
  simp only [CollatzResearch.WordTrace]
  refine ⟨66079331145408235207375853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44052887430272156804917235 66079331145408235207375853)
  ·
    refine ⟨24779749179528088202765945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66079331145408235207375853 24779749179528088202765945)
    ·
      refine ⟨18584811884646066152074459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24779749179528088202765945 18584811884646066152074459)
      ·
        refine ⟨27877217826969099228111689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584811884646066152074459 27877217826969099228111689)
        ·
          refine ⟨20907913370226824421083767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27877217826969099228111689 20907913370226824421083767)
          ·
            refine ⟨31361870055340236631625651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20907913370226824421083767 31361870055340236631625651)
            ·
              refine ⟨47042805083010354947438477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31361870055340236631625651 47042805083010354947438477)
              ·
                refine ⟨17641051906128883105289429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47042805083010354947438477 17641051906128883105289429)
                ·
                  refine ⟨413462154049895697780221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17641051906128883105289429 413462154049895697780221)
                  ·
                    rfl

theorem cell21_1811733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_1811733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811733 prefixEnd_1811733 := by exact prefixLift 1811733
  have htrace : WordTrace (prefixWord ++ tailWord_1811733) baseStart_1811733 baseEnd_1811733 := by
    simpa [prefixWord, tailWord_1811733, baseEnd_1811733] using wordTrace_append hprefix tailTrace_1811733
  have hstable : (prefixWord ++ tailWord_1811733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811733).length < 2 ^ (prefixWord ++ tailWord_1811733).sum := by decide
  have hdescent : baseEnd_1811733 < baseStart_1811733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811795 : List Nat := [1, 1, 1, 2, 1, 1, 9, 5]
def baseStart_1811795 : Nat := 118140960795 + 1811795 * 2 ^ 59
def prefixEnd_1811795 : Nat := 4983230072969 + 3 ^ 40 * 1811795 * 2
def baseEnd_1811795 : Nat := 137825434431532455915587

theorem tailTrace_1811795 : CollatzResearch.WordTrace tailWord_1811795 prefixEnd_1811795 137825434431532455915587 := by
  unfold tailWord_1811795
  simp only [CollatzResearch.WordTrace]
  refine ⟨66081592471183619796132839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44054394980789079864088559 66081592471183619796132839)
  ·
    refine ⟨99122388706775429694199259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66081592471183619796132839 99122388706775429694199259)
    ·
      refine ⟨148683583060163144541298889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99122388706775429694199259 148683583060163144541298889)
      ·
        refine ⟨111512687295122358405974167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148683583060163144541298889 111512687295122358405974167)
        ·
          refine ⟨167269030942683537608961251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111512687295122358405974167 167269030942683537608961251)
          ·
            refine ⟨250903546414025306413441877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167269030942683537608961251 250903546414025306413441877)
            ·
              refine ⟨1470137967269679529766261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 250903546414025306413441877 1470137967269679529766261)
              ·
                refine ⟨137825434431532455915587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1470137967269679529766261 137825434431532455915587)
                ·
                  rfl

theorem cell21_1811795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 5].length) (baseStart_1811795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811795 prefixEnd_1811795 := by exact prefixLift 1811795
  have htrace : WordTrace (prefixWord ++ tailWord_1811795) baseStart_1811795 baseEnd_1811795 := by
    simpa [prefixWord, tailWord_1811795, baseEnd_1811795] using wordTrace_append hprefix tailTrace_1811795
  have hstable : (prefixWord ++ tailWord_1811795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811795).length < 2 ^ (prefixWord ++ tailWord_1811795).sum := by decide
  have hdescent : baseEnd_1811795 < baseStart_1811795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811815 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 4]
def baseStart_1811815 : Nat := 118140960795 + 1811815 * 2 ^ 59
def prefixEnd_1811815 : Nat := 4983230072969 + 3 ^ 40 * 1811815 * 2
def baseEnd_1811815 : Nat := 413480867567081777413387

theorem tailTrace_1811815 : CollatzResearch.WordTrace tailWord_1811815 prefixEnd_1811815 413480867567081777413387 := by
  unfold tailWord_1811815
  simp only [CollatzResearch.WordTrace]
  refine ⟨66082321931111163211860899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44054881287407442141240599 66082321931111163211860899)
  ·
    refine ⟨99123482896666744817791349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66082321931111163211860899 99123482896666744817791349)
    ·
      refine ⟨9292826521562507326667939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99123482896666744817791349 9292826521562507326667939)
      ·
        refine ⟨13939239782343760990001909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292826521562507326667939 13939239782343760990001909)
        ·
          refine ⟨1306803729594727592812679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13939239782343760990001909 1306803729594727592812679)
          ·
            refine ⟨1960205594392091389219019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306803729594727592812679 1960205594392091389219019)
            ·
              refine ⟨2940308391588137083828529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960205594392091389219019 2940308391588137083828529)
              ·
                refine ⟨2205231293691102812871397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940308391588137083828529 2205231293691102812871397)
                ·
                  refine ⟨413480867567081777413387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205231293691102812871397 413480867567081777413387)
                  ·
                    rfl

theorem cell21_1811815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4].length) (baseStart_1811815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811815 prefixEnd_1811815 := by exact prefixLift 1811815
  have htrace : WordTrace (prefixWord ++ tailWord_1811815) baseStart_1811815 baseEnd_1811815 := by
    simpa [prefixWord, tailWord_1811815, baseEnd_1811815] using wordTrace_append hprefix tailTrace_1811815
  have hstable : (prefixWord ++ tailWord_1811815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811815).length < 2 ^ (prefixWord ++ tailWord_1811815).sum := by decide
  have hdescent : baseEnd_1811815 < baseStart_1811815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811826 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1811826 : Nat := 118140960795 + 1811826 * 2 ^ 59
def prefixEnd_1811826 : Nat := 4983230072969 + 3 ^ 40 * 1811826 * 2
def baseEnd_1811826 : Nat := 413483377916948202730031

theorem tailTrace_1811826 : CollatzResearch.WordTrace tailWord_1811826 prefixEnd_1811826 413483377916948202730031 := by
  unfold tailWord_1811826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520680783517828022627833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44055148756047541393674221 16520680783517828022627833)
  ·
    refine ⟨12390510587638371016970875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16520680783517828022627833 12390510587638371016970875)
    ·
      refine ⟨18585765881457556525456313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390510587638371016970875 18585765881457556525456313)
      ·
        refine ⟨13939324411093167394092235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18585765881457556525456313 13939324411093167394092235)
        ·
          refine ⟨20908986616639751091138353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13939324411093167394092235 20908986616639751091138353)
          ·
            refine ⟨15681739962479813318353765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20908986616639751091138353 15681739962479813318353765)
            ·
              refine ⟨2940326242964964997191331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15681739962479813318353765 2940326242964964997191331)
              ·
                refine ⟨4410489364447447495786997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940326242964964997191331 4410489364447447495786997)
                ·
                  refine ⟨413483377916948202730031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4410489364447447495786997 413483377916948202730031)
                  ·
                    rfl

theorem cell21_1811826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1811826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811826 prefixEnd_1811826 := by exact prefixLift 1811826
  have htrace : WordTrace (prefixWord ++ tailWord_1811826) baseStart_1811826 baseEnd_1811826 := by
    simpa [prefixWord, tailWord_1811826, baseEnd_1811826] using wordTrace_append hprefix tailTrace_1811826
  have hstable : (prefixWord ++ tailWord_1811826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811826).length < 2 ^ (prefixWord ++ tailWord_1811826).sum := by decide
  have hdescent : baseEnd_1811826 < baseStart_1811826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811840 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_1811840 : Nat := 118140960795 + 1811840 * 2 ^ 59
def prefixEnd_1811840 : Nat := 4983230072969 + 3 ^ 40 * 1811840 * 2
def baseEnd_1811840 : Nat := 413486572907687289496669

theorem tailTrace_1811840 : CollatzResearch.WordTrace tailWord_1811840 prefixEnd_1811840 413486572907687289496669 := by
  unfold tailWord_1811840
  simp only [CollatzResearch.WordTrace]
  refine ⟨33041616878010296240760487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44055489170680394987680649 33041616878010296240760487)
  ·
    refine ⟨49562425317015444361140731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33041616878010296240760487 49562425317015444361140731)
    ·
      refine ⟨74343637975523166541711097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49562425317015444361140731 74343637975523166541711097)
      ·
        refine ⟨55757728481642374906283323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74343637975523166541711097 55757728481642374906283323)
        ·
          refine ⟨83636592722463562359424985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55757728481642374906283323 83636592722463562359424985)
          ·
            refine ⟨62727444541847671769568739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83636592722463562359424985 62727444541847671769568739)
            ·
              refine ⟨94091166812771507654353109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62727444541847671769568739 94091166812771507654353109)
              ·
                refine ⟨2205261722174332210648901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94091166812771507654353109 2205261722174332210648901)
                ·
                  refine ⟨413486572907687289496669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205261722174332210648901 413486572907687289496669)
                  ·
                    rfl

theorem cell21_1811840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_1811840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811840 prefixEnd_1811840 := by exact prefixLift 1811840
  have htrace : WordTrace (prefixWord ++ tailWord_1811840) baseStart_1811840 baseEnd_1811840 := by
    simpa [prefixWord, tailWord_1811840, baseEnd_1811840] using wordTrace_append hprefix tailTrace_1811840
  have hstable : (prefixWord ++ tailWord_1811840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811840).length < 2 ^ (prefixWord ++ tailWord_1811840).sum := by decide
  have hdescent : baseEnd_1811840 < baseStart_1811840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811860 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1811860 : Nat := 118140960795 + 1811860 * 2 ^ 59
def prefixEnd_1811860 : Nat := 4983230072969 + 3 ^ 40 * 1811860 * 2
def baseEnd_1811860 : Nat := 413491137180171699163295

theorem tailTrace_1811860 : CollatzResearch.WordTrace tailWord_1811860 prefixEnd_1811860 413491137180171699163295 := by
  unfold tailWord_1811860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33041981607974067948624517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44055975477298757264832689 33041981607974067948624517)
  ·
    refine ⟨6195371551495137740367097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33041981607974067948624517 6195371551495137740367097)
    ·
      refine ⟨4646528663621353305275323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6195371551495137740367097 4646528663621353305275323)
      ·
        refine ⟨6969792995432029957912985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646528663621353305275323 6969792995432029957912985)
        ·
          refine ⟨5227344746574022468434739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6969792995432029957912985 5227344746574022468434739)
          ·
            refine ⟨7841017119861033702652109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227344746574022468434739 7841017119861033702652109)
            ·
              refine ⟨2940381419947887638494541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7841017119861033702652109 2940381419947887638494541)
              ·
                refine ⟨1102643032480457864435453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2940381419947887638494541 1102643032480457864435453)
                ·
                  refine ⟨413491137180171699163295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102643032480457864435453 413491137180171699163295)
                  ·
                    rfl

theorem cell21_1811860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1811860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811860 prefixEnd_1811860 := by exact prefixLift 1811860
  have htrace : WordTrace (prefixWord ++ tailWord_1811860) baseStart_1811860 baseEnd_1811860 := by
    simpa [prefixWord, tailWord_1811860, baseEnd_1811860] using wordTrace_append hprefix tailTrace_1811860
  have hstable : (prefixWord ++ tailWord_1811860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811860).length < 2 ^ (prefixWord ++ tailWord_1811860).sum := by decide
  have hdescent : baseEnd_1811860 < baseStart_1811860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811871 : List Nat := [1, 1, 2, 5, 1, 4, 7]
def baseStart_1811871 : Nat := 118140960795 + 1811871 * 2 ^ 59
def prefixEnd_1811871 : Nat := 4983230072969 + 3 ^ 40 * 1811871 * 2
def baseEnd_1811871 : Nat := 45943738614448680497771

theorem tailTrace_1811871 : CollatzResearch.WordTrace tailWord_1811871 prefixEnd_1811871 45943738614448680497771 := by
  unfold tailWord_1811871
  simp only [CollatzResearch.WordTrace]
  refine ⟨66084364418908284775899467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44056242945938856517266311 66084364418908284775899467)
  ·
    refine ⟨99126546628362427163849201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66084364418908284775899467 99126546628362427163849201)
    ·
      refine ⟨74344909971271820372886901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99126546628362427163849201 74344909971271820372886901)
      ·
        refine ⟨6969835309806733159958147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74344909971271820372886901 6969835309806733159958147)
        ·
          refine ⟨10454752964710099739937221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969835309806733159958147 10454752964710099739937221)
          ·
            refine ⟨1960266180883143701238229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10454752964710099739937221 1960266180883143701238229)
            ·
              refine ⟨45943738614448680497771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1960266180883143701238229 45943738614448680497771)
              ·
                rfl

theorem cell21_1811871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 7].length) (baseStart_1811871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811871 prefixEnd_1811871 := by exact prefixLift 1811871
  have htrace : WordTrace (prefixWord ++ tailWord_1811871) baseStart_1811871 baseEnd_1811871 := by
    simpa [prefixWord, tailWord_1811871, baseEnd_1811871] using wordTrace_append hprefix tailTrace_1811871
  have hstable : (prefixWord ++ tailWord_1811871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811871).length < 2 ^ (prefixWord ++ tailWord_1811871).sum := by decide
  have hdescent : baseEnd_1811871 < baseStart_1811871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811930 : List Nat := [3, 1, 1, 2, 3, 11]
def baseStart_1811930 : Nat := 118140960795 + 1811930 * 2 ^ 59
def prefixEnd_1811930 : Nat := 4983230072969 + 3 ^ 40 * 1811930 * 2
def baseEnd_1811930 : Nat := 15315078227180264185055

theorem tailTrace_1811930 : CollatzResearch.WordTrace tailWord_1811930 prefixEnd_1811930 15315078227180264185055 := by
  unfold tailWord_1811930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521629081423634463074311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44057677550463025234864829 16521629081423634463074311)
  ·
    refine ⟨24782443622135451694611467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16521629081423634463074311 24782443622135451694611467)
    ·
      refine ⟨37173665433203177541917201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24782443622135451694611467 37173665433203177541917201)
      ·
        refine ⟨27880249074902383156437901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37173665433203177541917201 27880249074902383156437901)
        ·
          refine ⟨10455093403088393683664213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27880249074902383156437901 10455093403088393683664213)
          ·
            refine ⟨15315078227180264185055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10455093403088393683664213 15315078227180264185055)
            ·
              rfl

theorem cell21_1811930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 11].length) (baseStart_1811930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811930 prefixEnd_1811930 := by exact prefixLift 1811930
  have htrace : WordTrace (prefixWord ++ tailWord_1811930) baseStart_1811930 baseEnd_1811930 := by
    simpa [prefixWord, tailWord_1811930, baseEnd_1811930] using wordTrace_append hprefix tailTrace_1811930
  have hstable : (prefixWord ++ tailWord_1811930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811930).length < 2 ^ (prefixWord ++ tailWord_1811930).sum := by decide
  have hdescent : baseEnd_1811930 < baseStart_1811930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811933 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1811933 : Nat := 118140960795 + 1811933 * 2 ^ 59
def prefixEnd_1811933 : Nat := 4983230072969 + 3 ^ 40 * 1811933 * 2
def baseEnd_1811933 : Nat := 413507796774739794446479

theorem tailTrace_1811933 : CollatzResearch.WordTrace tailWord_1811933 prefixEnd_1811933 413507796774739794446479 := by
  unfold tailWord_1811933
  simp only [CollatzResearch.WordTrace]
  refine ⟨66086625744683669364656453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44057750496455779576437635 66086625744683669364656453)
  ·
    refine ⟨12391242327128188005873085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66086625744683669364656453 12391242327128188005873085)
    ·
      refine ⟨4646715872673070502202407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12391242327128188005873085 4646715872673070502202407)
      ·
        refine ⟨6970073809009605753303611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646715872673070502202407 6970073809009605753303611)
        ·
          refine ⟨10455110713514408629955417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6970073809009605753303611 10455110713514408629955417)
          ·
            refine ⟨7841333035135806472466563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10455110713514408629955417 7841333035135806472466563)
            ·
              refine ⟨11761999552703709708699845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841333035135806472466563 11761999552703709708699845)
              ·
                refine ⟨2205374916131945570381221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11761999552703709708699845 2205374916131945570381221)
                ·
                  refine ⟨413507796774739794446479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205374916131945570381221 413507796774739794446479)
                  ·
                    rfl

theorem cell21_1811933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1811933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811933 prefixEnd_1811933 := by exact prefixLift 1811933
  have htrace : WordTrace (prefixWord ++ tailWord_1811933) baseStart_1811933 baseEnd_1811933 := by
    simpa [prefixWord, tailWord_1811933, baseEnd_1811933] using wordTrace_append hprefix tailTrace_1811933
  have hstable : (prefixWord ++ tailWord_1811933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811933).length < 2 ^ (prefixWord ++ tailWord_1811933).sum := by decide
  have hdescent : baseEnd_1811933 < baseStart_1811933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811981 : List Nat := [1, 7, 1, 1, 2, 1, 8]
def baseStart_1811981 : Nat := 118140960795 + 1811981 * 2 ^ 59
def prefixEnd_1811981 : Nat := 4983230072969 + 3 ^ 40 * 1811981 * 2
def baseEnd_1811981 : Nat := 45946527892078041960709

theorem tailTrace_1811981 : CollatzResearch.WordTrace tailWord_1811981 prefixEnd_1811981 45946527892078041960709 := by
  unfold tailWord_1811981
  simp only [CollatzResearch.WordTrace]
  refine ⟨66088376448509773562403797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44058917632339849041602531 66088376448509773562403797)
  ·
    refine ⟨1548946323011947817868839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66088376448509773562403797 1548946323011947817868839)
    ·
      refine ⟨2323419484517921726803259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548946323011947817868839 2323419484517921726803259)
      ·
        refine ⟨3485129226776882590204889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323419484517921726803259 3485129226776882590204889)
        ·
          refine ⟨2613846920082661942653667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485129226776882590204889 2613846920082661942653667)
          ·
            refine ⟨3920770380123992913980501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613846920082661942653667 3920770380123992913980501)
            ·
              refine ⟨45946527892078041960709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3920770380123992913980501 45946527892078041960709)
              ·
                rfl

theorem cell21_1811981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 8].length) (baseStart_1811981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1811981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1811981 prefixEnd_1811981 := by exact prefixLift 1811981
  have htrace : WordTrace (prefixWord ++ tailWord_1811981) baseStart_1811981 baseEnd_1811981 := by
    simpa [prefixWord, tailWord_1811981, baseEnd_1811981] using wordTrace_append hprefix tailTrace_1811981
  have hstable : (prefixWord ++ tailWord_1811981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811981).length < 2 ^ (prefixWord ++ tailWord_1811981).sum := by decide
  have hdescent : baseEnd_1811981 < baseStart_1811981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812023 : List Nat := [1, 1, 3, 1, 2, 4, 4, 5]
def baseStart_1812023 : Nat := 118140960795 + 1812023 * 2 ^ 59
def prefixEnd_1812023 : Nat := 4983230072969 + 3 ^ 40 * 1812023 * 2
def baseEnd_1812023 : Nat := 137842778666973212648765

theorem tailTrace_1812023 : CollatzResearch.WordTrace tailWord_1812023 prefixEnd_1812023 137842778666973212648765 := by
  unfold tailWord_1812023
  simp only [CollatzResearch.WordTrace]
  refine ⟨66089908314357614735432723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44059938876238409823621815 66089908314357614735432723)
  ·
    refine ⟨99134862471536422103149085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66089908314357614735432723 99134862471536422103149085)
    ·
      refine ⟨37175573426826158288680907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99134862471536422103149085 37175573426826158288680907)
      ·
        refine ⟨55763360140239237433021361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37175573426826158288680907 55763360140239237433021361)
        ·
          refine ⟨41822520105179428074766021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55763360140239237433021361 41822520105179428074766021)
          ·
            refine ⟨7841722519721142764018629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41822520105179428074766021 7841722519721142764018629)
            ·
              refine ⟨1470322972447714268253493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7841722519721142764018629 1470322972447714268253493)
              ·
                refine ⟨137842778666973212648765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1470322972447714268253493 137842778666973212648765)
                ·
                  rfl

theorem cell21_1812023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 5].length) (baseStart_1812023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812023 prefixEnd_1812023 := by exact prefixLift 1812023
  have htrace : WordTrace (prefixWord ++ tailWord_1812023) baseStart_1812023 baseEnd_1812023 := by
    simpa [prefixWord, tailWord_1812023, baseEnd_1812023] using wordTrace_append hprefix tailTrace_1812023
  have hstable : (prefixWord ++ tailWord_1812023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812023).length < 2 ^ (prefixWord ++ tailWord_1812023).sum := by decide
  have hdescent : baseEnd_1812023 < baseStart_1812023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812029 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1812029 : Nat := 118140960795 + 1812029 * 2 ^ 59
def prefixEnd_1812029 : Nat := 4983230072969 + 3 ^ 40 * 1812029 * 2
def baseEnd_1812029 : Nat := 413529705282664960846283

theorem tailTrace_1812029 : CollatzResearch.WordTrace tailWord_1812029 prefixEnd_1812029 413529705282664960846283 := by
  unfold tailWord_1812029
  simp only [CollatzResearch.WordTrace]
  refine ⟨66090127152335877760151141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44060084768223918506767427 66090127152335877760151141)
  ·
    refine ⟨12391898841062977080028339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66090127152335877760151141 12391898841062977080028339)
    ·
      refine ⟨18587848261594465620042509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391898841062977080028339 18587848261594465620042509)
      ·
        refine ⟨6970443098097924607515941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18587848261594465620042509 6970443098097924607515941)
        ·
          refine ⟨1306958080893360863909239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6970443098097924607515941 1306958080893360863909239)
          ·
            refine ⟨1960437121340041295863859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306958080893360863909239 1960437121340041295863859)
            ·
              refine ⟨2940655682010061943795789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960437121340041295863859 2940655682010061943795789)
              ·
                refine ⟨1102745880753773228923421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2940655682010061943795789 1102745880753773228923421)
                ·
                  refine ⟨413529705282664960846283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102745880753773228923421 413529705282664960846283)
                  ·
                    rfl

theorem cell21_1812029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1812029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812029 prefixEnd_1812029 := by exact prefixLift 1812029
  have htrace : WordTrace (prefixWord ++ tailWord_1812029) baseStart_1812029 baseEnd_1812029 := by
    simpa [prefixWord, tailWord_1812029, baseEnd_1812029] using wordTrace_append hprefix tailTrace_1812029
  have hstable : (prefixWord ++ tailWord_1812029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812029).length < 2 ^ (prefixWord ++ tailWord_1812029).sum := by decide
  have hdescent : baseEnd_1812029 < baseStart_1812029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812178 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1812178 : Nat := 118140960795 + 1812178 * 2 ^ 59
def prefixEnd_1812178 : Nat := 4983230072969 + 3 ^ 40 * 1812178 * 2
def baseEnd_1812178 : Nat := 413563709112673812862645

theorem tailTrace_1812178 : CollatzResearch.WordTrace tailWord_1812178 prefixEnd_1812178 413563709112673812862645 := by
  unfold tailWord_1812178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16523890407199019051831297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44063707752530717471550125 16523890407199019051831297)
  ·
    refine ⟨12392917805399264288873473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16523890407199019051831297 12392917805399264288873473)
    ·
      refine ⟨9294688354049448216655105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12392917805399264288873473 9294688354049448216655105)
      ·
        refine ⟨6971016265537086162491329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9294688354049448216655105 6971016265537086162491329)
        ·
          refine ⟨5228262199152814621868497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6971016265537086162491329 5228262199152814621868497)
          ·
            refine ⟨3921196649364610966401373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5228262199152814621868497 3921196649364610966401373)
            ·
              refine ⟨1470448743511729112400515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3921196649364610966401373 1470448743511729112400515)
              ·
                refine ⟨2205673115267593668600773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470448743511729112400515 2205673115267593668600773)
                ·
                  refine ⟨413563709112673812862645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205673115267593668600773 413563709112673812862645)
                  ·
                    rfl

theorem cell21_1812178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1812178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812178 prefixEnd_1812178 := by exact prefixLift 1812178
  have htrace : WordTrace (prefixWord ++ tailWord_1812178) baseStart_1812178 baseEnd_1812178 := by
    simpa [prefixWord, tailWord_1812178, baseEnd_1812178] using wordTrace_append hprefix tailTrace_1812178
  have hstable : (prefixWord ++ tailWord_1812178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812178).length < 2 ^ (prefixWord ++ tailWord_1812178).sum := by decide
  have hdescent : baseEnd_1812178 < baseStart_1812178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812203 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_1812203 : Nat := 118140960795 + 1812203 * 2 ^ 59
def prefixEnd_1812203 : Nat := 4983230072969 + 3 ^ 40 * 1812203 * 2
def baseEnd_1812203 : Nat := 413569414453279324945927

theorem tailTrace_1812203 : CollatzResearch.WordTrace tailWord_1812203 prefixEnd_1812203 413569414453279324945927 := by
  unfold tailWord_1812203
  simp only [CollatzResearch.WordTrace]
  refine ⟨66096473453705505476985263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44064315635803670317990175 66096473453705505476985263)
  ·
    refine ⟨99144710180558258215477895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66096473453705505476985263 99144710180558258215477895)
    ·
      refine ⟨148717065270837387323216843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99144710180558258215477895 148717065270837387323216843)
      ·
        refine ⟨223075597906256080984825265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148717065270837387323216843 223075597906256080984825265)
        ·
          refine ⟨167306698429692060738618949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223075597906256080984825265 167306698429692060738618949)
          ·
            refine ⟨31370005955567261388491053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167306698429692060738618949 31370005955567261388491053)
            ·
              refine ⟨11763752233337723020684145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31370005955567261388491053 11763752233337723020684145)
              ·
                refine ⟨8822814175003292265513109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763752233337723020684145 8822814175003292265513109)
                ·
                  refine ⟨413569414453279324945927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8822814175003292265513109 413569414453279324945927)
                  ·
                    rfl

theorem cell21_1812203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_1812203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812203 prefixEnd_1812203 := by exact prefixLift 1812203
  have htrace : WordTrace (prefixWord ++ tailWord_1812203) baseStart_1812203 baseEnd_1812203 := by
    simpa [prefixWord, tailWord_1812203, baseEnd_1812203] using wordTrace_append hprefix tailTrace_1812203
  have hstable : (prefixWord ++ tailWord_1812203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812203).length < 2 ^ (prefixWord ++ tailWord_1812203).sum := by decide
  have hdescent : baseEnd_1812203 < baseStart_1812203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812220 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_1812220 : Nat := 118140960795 + 1812220 * 2 ^ 59
def prefixEnd_1812220 : Nat := 4983230072969 + 3 ^ 40 * 1812220 * 2
def baseEnd_1812220 : Nat := 413573294084891073162559

theorem tailTrace_1812220 : CollatzResearch.WordTrace tailWord_1812220 prefixEnd_1812220 413573294084891073162559 := by
  unfold tailWord_1812220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048546747321958690177057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44064728996429278253569409 33048546747321958690177057)
  ·
    refine ⟨24786410060491469017632793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33048546747321958690177057 24786410060491469017632793)
    ·
      refine ⟨18589807545368601763224595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24786410060491469017632793 18589807545368601763224595)
      ·
        refine ⟨27884711318052902644836893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18589807545368601763224595 27884711318052902644836893)
        ·
          refine ⟨10456766744269838491813835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27884711318052902644836893 10456766744269838491813835)
          ·
            refine ⟨15685150116404757737720753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10456766744269838491813835 15685150116404757737720753)
            ·
              refine ⟨11763862587303568303290565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15685150116404757737720753 11763862587303568303290565)
              ·
                refine ⟨2205724235119419056866981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11763862587303568303290565 2205724235119419056866981)
                ·
                  refine ⟨413573294084891073162559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205724235119419056866981 413573294084891073162559)
                  ·
                    rfl

theorem cell21_1812220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_1812220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812220 prefixEnd_1812220 := by exact prefixLift 1812220
  have htrace : WordTrace (prefixWord ++ tailWord_1812220) baseStart_1812220 baseEnd_1812220 := by
    simpa [prefixWord, tailWord_1812220, baseEnd_1812220] using wordTrace_append hprefix tailTrace_1812220
  have hstable : (prefixWord ++ tailWord_1812220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812220).length < 2 ^ (prefixWord ++ tailWord_1812220).sum := by decide
  have hdescent : baseEnd_1812220 < baseStart_1812220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812234 : List Nat := [3, 1, 2, 2, 1, 3, 1, 8]
def baseStart_1812234 : Nat := 118140960795 + 1812234 * 2 ^ 59
def prefixEnd_1812234 : Nat := 4983230072969 + 3 ^ 40 * 1812234 * 2
def baseEnd_1812234 : Nat := 137858829691876719976399

theorem tailTrace_1812234 : CollatzResearch.WordTrace tailWord_1812234 prefixEnd_1812234 137858829691876719976399 := by
  unfold tailWord_1812234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524401029148299442840939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44065069411062131847575837 16524401029148299442840939)
  ·
    refine ⟨24786601543722449164261409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16524401029148299442840939 24786601543722449164261409)
    ·
      refine ⟨18589951157791836873196057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24786601543722449164261409 18589951157791836873196057)
      ·
        refine ⟨13942463368343877654897043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18589951157791836873196057 13942463368343877654897043)
        ·
          refine ⟨20913695052515816482345565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942463368343877654897043 20913695052515816482345565)
          ·
            refine ⟨7842635644693431180879587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20913695052515816482345565 7842635644693431180879587)
            ·
              refine ⟨11763953467040146771319381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842635644693431180879587 11763953467040146771319381)
              ·
                refine ⟨137858829691876719976399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11763953467040146771319381 137858829691876719976399)
                ·
                  rfl

theorem cell21_1812234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_1812234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812234 prefixEnd_1812234 := by exact prefixLift 1812234
  have htrace : WordTrace (prefixWord ++ tailWord_1812234) baseStart_1812234 baseEnd_1812234 := by
    simpa [prefixWord, tailWord_1812234, baseEnd_1812234] using wordTrace_append hprefix tailTrace_1812234
  have hstable : (prefixWord ++ tailWord_1812234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812234).length < 2 ^ (prefixWord ++ tailWord_1812234).sum := by decide
  have hdescent : baseEnd_1812234 < baseStart_1812234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812296 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_1812296 : Nat := 118140960795 + 1812296 * 2 ^ 59
def prefixEnd_1812296 : Nat := 4983230072969 + 3 ^ 40 * 1812296 * 2
def baseEnd_1812296 : Nat := 413590638320331829895737

theorem tailTrace_1812296 : CollatzResearch.WordTrace tailWord_1812296 prefixEnd_1812296 413590638320331829895737 := by
  unfold tailWord_1812296
  simp only [CollatzResearch.WordTrace]
  refine ⟨33049932721184291180060371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44066576961579054906747161 33049932721184291180060371)
  ·
    refine ⟨49574899081776436770090557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33049932721184291180060371 49574899081776436770090557)
    ·
      refine ⟨18590587155666163788783959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49574899081776436770090557 18590587155666163788783959)
      ·
        refine ⟨27885880733499245683175939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18590587155666163788783959 27885880733499245683175939)
        ·
          refine ⟨41828821100248868524763909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27885880733499245683175939 41828821100248868524763909)
          ·
            refine ⟨7842903956296662848393233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41828821100248868524763909 7842903956296662848393233)
            ·
              refine ⟨5882177967222497136294925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7842903956296662848393233 5882177967222497136294925)
              ·
                refine ⟨2205816737708436426110597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5882177967222497136294925 2205816737708436426110597)
                ·
                  refine ⟨413590638320331829895737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205816737708436426110597 413590638320331829895737)
                  ·
                    rfl

theorem cell21_1812296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_1812296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812296 prefixEnd_1812296 := by exact prefixLift 1812296
  have htrace : WordTrace (prefixWord ++ tailWord_1812296) baseStart_1812296 baseEnd_1812296 := by
    simpa [prefixWord, tailWord_1812296, baseEnd_1812296] using wordTrace_append hprefix tailTrace_1812296
  have hstable : (prefixWord ++ tailWord_1812296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812296).length < 2 ^ (prefixWord ++ tailWord_1812296).sum := by decide
  have hdescent : baseEnd_1812296 < baseStart_1812296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812316 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_1812316 : Nat := 118140960795 + 1812316 * 2 ^ 59
def prefixEnd_1812316 : Nat := 4983230072969 + 3 ^ 40 * 1812316 * 2
def baseEnd_1812316 : Nat := 413595202592816239562363

theorem tailTrace_1812316 : CollatzResearch.WordTrace tailWord_1812316 prefixEnd_1812316 413595202592816239562363 := by
  unfold tailWord_1812316
  simp only [CollatzResearch.WordTrace]
  refine ⟨33050297451148062887924401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44067063268197417183899201 33050297451148062887924401)
  ·
    refine ⟨24787723088361047165943301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33050297451148062887924401 24787723088361047165943301)
    ·
      refine ⟨4647698079067696343614369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24787723088361047165943301 4647698079067696343614369)
      ·
        refine ⟨3485773559300772257710777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4647698079067696343614369 3485773559300772257710777)
        ·
          refine ⟨2614330169475579193283083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485773559300772257710777 2614330169475579193283083)
          ·
            refine ⟨3921495254213368789924625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614330169475579193283083 3921495254213368789924625)
            ·
              refine ⟨2941121440660026592443469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921495254213368789924625 2941121440660026592443469)
              ·
                refine ⟨1102920540247509972166301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2941121440660026592443469 1102920540247509972166301)
                ·
                  refine ⟨413595202592816239562363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102920540247509972166301 413595202592816239562363)
                  ·
                    rfl

theorem cell21_1812316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_1812316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812316 prefixEnd_1812316 := by exact prefixLift 1812316
  have htrace : WordTrace (prefixWord ++ tailWord_1812316) baseStart_1812316 baseEnd_1812316 := by
    simpa [prefixWord, tailWord_1812316, baseEnd_1812316] using wordTrace_append hprefix tailTrace_1812316
  have hstable : (prefixWord ++ tailWord_1812316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812316).length < 2 ^ (prefixWord ++ tailWord_1812316).sum := by decide
  have hdescent : baseEnd_1812316 < baseStart_1812316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812372 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1812372 : Nat := 118140960795 + 1812372 * 2 ^ 59
def prefixEnd_1812372 : Nat := 4983230072969 + 3 ^ 40 * 1812372 * 2
def baseEnd_1812372 : Nat := 413607982555772586628915

theorem tailTrace_1812372 : CollatzResearch.WordTrace tailWord_1812372 prefixEnd_1812372 413607982555772586628915 := by
  unfold tailWord_1812372
  simp only [CollatzResearch.WordTrace]
  refine ⟨33051318695046623669943685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44068424926728831559924913 33051318695046623669943685)
  ·
    refine ⟨6197122255321241938114441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33051318695046623669943685 6197122255321241938114441)
    ·
      refine ⟨4647841691490931453585831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6197122255321241938114441 4647841691490931453585831)
      ·
        refine ⟨6971762537236397180378747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647841691490931453585831 6971762537236397180378747)
        ·
          refine ⟨10457643805854595770568121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971762537236397180378747 10457643805854595770568121)
          ·
            refine ⟨7843232854390946827926091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457643805854595770568121 7843232854390946827926091)
            ·
              refine ⟨11764849281586420241889137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843232854390946827926091 11764849281586420241889137)
              ·
                refine ⟨8823636961189815181416853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11764849281586420241889137 8823636961189815181416853)
                ·
                  refine ⟨413607982555772586628915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8823636961189815181416853 413607982555772586628915)
                  ·
                    rfl

theorem cell21_1812372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1812372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812372 prefixEnd_1812372 := by exact prefixLift 1812372
  have htrace : WordTrace (prefixWord ++ tailWord_1812372) baseStart_1812372 baseEnd_1812372 := by
    simpa [prefixWord, tailWord_1812372, baseEnd_1812372] using wordTrace_append hprefix tailTrace_1812372
  have hstable : (prefixWord ++ tailWord_1812372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812372).length < 2 ^ (prefixWord ++ tailWord_1812372).sum := by decide
  have hdescent : baseEnd_1812372 < baseStart_1812372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812375 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 3]
def baseStart_1812375 : Nat := 118140960795 + 1812375 * 2 ^ 59
def prefixEnd_1812375 : Nat := 4983230072969 + 3 ^ 40 * 1812375 * 2
def baseEnd_1812375 : Nat := 413608667196645248078909

theorem tailTrace_1812375 : CollatzResearch.WordTrace tailWord_1812375 prefixEnd_1812375 413608667196645248078909 := by
  unfold tailWord_1812375
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102746809082378852246579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44068497872721585901497719 66102746809082378852246579)
  ·
    refine ⟨99154120213623568278369869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66102746809082378852246579 99154120213623568278369869)
    ·
      refine ⟨37182795080108838104388701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99154120213623568278369869 37182795080108838104388701)
      ·
        refine ⟨13943548155040814289145763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37182795080108838104388701 13943548155040814289145763)
        ·
          refine ⟨20915322232561221433718645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13943548155040814289145763 20915322232561221433718645)
          ·
            refine ⟨1960811459302614509411123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20915322232561221433718645 1960811459302614509411123)
            ·
              refine ⟨2941217188953921764116685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960811459302614509411123 2941217188953921764116685)
              ·
                refine ⟨1102956445857720661543757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2941217188953921764116685 1102956445857720661543757)
                ·
                  refine ⟨413608667196645248078909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102956445857720661543757 413608667196645248078909)
                  ·
                    rfl

theorem cell21_1812375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 3].length) (baseStart_1812375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812375 prefixEnd_1812375 := by exact prefixLift 1812375
  have htrace : WordTrace (prefixWord ++ tailWord_1812375) baseStart_1812375 baseEnd_1812375 := by
    simpa [prefixWord, tailWord_1812375, baseEnd_1812375] using wordTrace_append hprefix tailTrace_1812375
  have hstable : (prefixWord ++ tailWord_1812375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812375).length < 2 ^ (prefixWord ++ tailWord_1812375).sum := by decide
  have hdescent : baseEnd_1812375 < baseStart_1812375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812392 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_1812392 : Nat := 118140960795 + 1812392 * 2 ^ 59
def prefixEnd_1812392 : Nat := 4983230072969 + 3 ^ 40 * 1812392 * 2
def baseEnd_1812392 : Nat := 413612546828256996295541

theorem tailTrace_1812392 : CollatzResearch.WordTrace tailWord_1812392 prefixEnd_1812392 413612546828256996295541 := by
  unfold tailWord_1812392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33051683425010395377807715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44068911233347193837076953 33051683425010395377807715)
  ·
    refine ⟨49577525137515593066711573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33051683425010395377807715 49577525137515593066711573)
    ·
      refine ⟨2323946490821043425002105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49577525137515593066711573 2323946490821043425002105)
      ·
        refine ⟨1742959868115782568751579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2323946490821043425002105 1742959868115782568751579)
        ·
          refine ⟨2614439802173673853127369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742959868115782568751579 2614439802173673853127369)
          ·
            refine ⟨1960829851630255389845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614439802173673853127369 1960829851630255389845527)
            ·
              refine ⟨2941244777445383084768291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960829851630255389845527 2941244777445383084768291)
              ·
                refine ⟨4411867166168074627152437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941244777445383084768291 4411867166168074627152437)
                ·
                  refine ⟨413612546828256996295541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4411867166168074627152437 413612546828256996295541)
                  ·
                    rfl

theorem cell21_1812392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_1812392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812392 prefixEnd_1812392 := by exact prefixLift 1812392
  have htrace : WordTrace (prefixWord ++ tailWord_1812392) baseStart_1812392 baseEnd_1812392 := by
    simpa [prefixWord, tailWord_1812392, baseEnd_1812392] using wordTrace_append hprefix tailTrace_1812392
  have hstable : (prefixWord ++ tailWord_1812392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812392).length < 2 ^ (prefixWord ++ tailWord_1812392).sum := by decide
  have hdescent : baseEnd_1812392 < baseStart_1812392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812451 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 3]
def baseStart_1812451 : Nat := 118140960795 + 1812451 * 2 ^ 59
def prefixEnd_1812451 : Nat := 4983230072969 + 3 ^ 40 * 1812451 * 2
def baseEnd_1812451 : Nat := 413626011432086004812087

theorem tailTrace_1812451 : CollatzResearch.WordTrace tailWord_1812451 prefixEnd_1812451 413626011432086004812087 := by
  unfold tailWord_1812451
  simp only [CollatzResearch.WordTrace]
  refine ⟨66105518756807043832013207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44070345837871362554675471 66105518756807043832013207)
  ·
    refine ⟨99158278135210565748019811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66105518756807043832013207 99158278135210565748019811)
    ·
      refine ⟨148737417202815848622029717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99158278135210565748019811 148737417202815848622029717)
      ·
        refine ⟨6972066431381992904157643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148737417202815848622029717 6972066431381992904157643)
        ·
          refine ⟨10458099647072989356236465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972066431381992904157643 10458099647072989356236465)
          ·
            refine ⟨7843574735304742017177349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10458099647072989356236465 7843574735304742017177349)
            ·
              refine ⟨1470670262869639128220753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7843574735304742017177349 1470670262869639128220753)
              ·
                refine ⟨1103002697152229346165565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470670262869639128220753 1103002697152229346165565)
                ·
                  refine ⟨413626011432086004812087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103002697152229346165565 413626011432086004812087)
                  ·
                    rfl

theorem cell21_1812451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3].length) (baseStart_1812451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812451 prefixEnd_1812451 := by exact prefixLift 1812451
  have htrace : WordTrace (prefixWord ++ tailWord_1812451) baseStart_1812451 baseEnd_1812451 := by
    simpa [prefixWord, tailWord_1812451, baseEnd_1812451] using wordTrace_append hprefix tailTrace_1812451
  have hstable : (prefixWord ++ tailWord_1812451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812451).length < 2 ^ (prefixWord ++ tailWord_1812451).sum := by decide
  have hdescent : baseEnd_1812451 < baseStart_1812451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812507 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_1812507 : Nat := 118140960795 + 1812507 * 2 ^ 59
def prefixEnd_1812507 : Nat := 4983230072969 + 3 ^ 40 * 1812507 * 2
def baseEnd_1812507 : Nat := 413638791395042351878639

theorem tailTrace_1812507 : CollatzResearch.WordTrace tailWord_1812507 prefixEnd_1812507 413638791395042351878639 := by
  unfold tailWord_1812507
  simp only [CollatzResearch.WordTrace]
  refine ⟨66107561244604165396051775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44071707496402776930701183 66107561244604165396051775)
  ·
    refine ⟨99161341866906248094077663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66107561244604165396051775 99161341866906248094077663)
    ·
      refine ⟨148742012800359372141116495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99161341866906248094077663 148742012800359372141116495)
      ·
        refine ⟨223113019200539058211674743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148742012800359372141116495 223113019200539058211674743)
        ·
          refine ⟨334669528800808587317512115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223113019200539058211674743 334669528800808587317512115)
          ·
            refine ⟨502004293201212880976268173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334669528800808587317512115 502004293201212880976268173)
            ·
              refine ⟨188251609950454830366100565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502004293201212880976268173 188251609950454830366100565)
              ·
                refine ⟨2206073554106892543352741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 188251609950454830366100565 2206073554106892543352741)
                ·
                  refine ⟨413638791395042351878639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206073554106892543352741 413638791395042351878639)
                  ·
                    rfl

theorem cell21_1812507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_1812507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812507 prefixEnd_1812507 := by exact prefixLift 1812507
  have htrace : WordTrace (prefixWord ++ tailWord_1812507) baseStart_1812507 baseEnd_1812507 := by
    simpa [prefixWord, tailWord_1812507, baseEnd_1812507] using wordTrace_append hprefix tailTrace_1812507
  have hstable : (prefixWord ++ tailWord_1812507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812507).length < 2 ^ (prefixWord ++ tailWord_1812507).sum := by decide
  have hdescent : baseEnd_1812507 < baseStart_1812507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812631 : List Nat := [1, 1, 3, 3, 4, 2, 1, 6]
def baseStart_1812631 : Nat := 118140960795 + 1812631 * 2 ^ 59
def prefixEnd_1812631 : Nat := 4983230072969 + 3 ^ 40 * 1812631 * 2
def baseEnd_1812631 : Nat := 137889029961481897270573

theorem tailTrace_1812631 : CollatzResearch.WordTrace tailWord_1812631 prefixEnd_1812631 137889029961481897270573 := by
  unfold tailWord_1812631
  simp only [CollatzResearch.WordTrace]
  refine ⟨66112083896154934573565747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44074722597436623049043831 66112083896154934573565747)
  ·
    refine ⟨99168125844232401860348621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66112083896154934573565747 99168125844232401860348621)
    ·
      refine ⟨37188047191587150697630733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99168125844232401860348621 37188047191587150697630733)
      ·
        refine ⟨13945517696845181511611525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37188047191587150697630733 13945517696845181511611525)
        ·
          refine ⟨2614784568158471533427161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13945517696845181511611525 2614784568158471533427161)
          ·
            refine ⟨1961088426118853650070371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614784568158471533427161 1961088426118853650070371)
            ·
              refine ⟨2941632639178280475105557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961088426118853650070371 2941632639178280475105557)
              ·
                refine ⟨137889029961481897270573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2941632639178280475105557 137889029961481897270573)
                ·
                  rfl

theorem cell21_1812631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 6].length) (baseStart_1812631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812631 prefixEnd_1812631 := by exact prefixLift 1812631
  have htrace : WordTrace (prefixWord ++ tailWord_1812631) baseStart_1812631 baseEnd_1812631 := by
    simpa [prefixWord, tailWord_1812631, baseEnd_1812631] using wordTrace_append hprefix tailTrace_1812631
  have hstable : (prefixWord ++ tailWord_1812631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812631).length < 2 ^ (prefixWord ++ tailWord_1812631).sum := by decide
  have hdescent : baseEnd_1812631 < baseStart_1812631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812676 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1812676 : Nat := 118140960795 + 1812676 * 2 ^ 59
def prefixEnd_1812676 : Nat := 4983230072969 + 3 ^ 40 * 1812676 * 2
def baseEnd_1812676 : Nat := 413677359497535613561627

theorem tailTrace_1812676 : CollatzResearch.WordTrace tailWord_1812676 prefixEnd_1812676 413677359497535613561627 := by
  unfold tailWord_1812676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33056862590495953629476941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44075816787327938172635921 33056862590495953629476941)
  ·
    refine ⟨12396323471435982611053853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33056862590495953629476941 12396323471435982611053853)
    ·
      refine ⟨4648621301788493479145195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12396323471435982611053853 4648621301788493479145195)
      ·
        refine ⟨6972931952682740218717793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648621301788493479145195 6972931952682740218717793)
        ·
          refine ⟨5229698964512055164038345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972931952682740218717793 5229698964512055164038345)
          ·
            refine ⟨3922274223384041373028759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229698964512055164038345 3922274223384041373028759)
            ·
              refine ⟨5883411335076062059543139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922274223384041373028759 5883411335076062059543139)
              ·
                refine ⟨8825117002614093089314709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883411335076062059543139 8825117002614093089314709)
                ·
                  refine ⟨413677359497535613561627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8825117002614093089314709 413677359497535613561627)
                  ·
                    rfl

theorem cell21_1812676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1812676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812676 prefixEnd_1812676 := by exact prefixLift 1812676
  have htrace : WordTrace (prefixWord ++ tailWord_1812676) baseStart_1812676 baseEnd_1812676 := by
    simpa [prefixWord, tailWord_1812676, baseEnd_1812676] using wordTrace_append hprefix tailTrace_1812676
  have hstable : (prefixWord ++ tailWord_1812676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812676).length < 2 ^ (prefixWord ++ tailWord_1812676).sum := by decide
  have hdescent : baseEnd_1812676 < baseStart_1812676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812704 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_1812704 : Nat := 118140960795 + 1812704 * 2 ^ 59
def prefixEnd_1812704 : Nat := 4983230072969 + 3 ^ 40 * 1812704 * 2
def baseEnd_1812704 : Nat := 413683749479013787094903

theorem tailTrace_1812704 : CollatzResearch.WordTrace tailWord_1812704 prefixEnd_1812704 413683749479013787094903 := by
  unfold tailWord_1812704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057373212445234020486583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44076497616593645360648777 33057373212445234020486583)
  ·
    refine ⟨49586059818667851030729875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33057373212445234020486583 49586059818667851030729875)
    ·
      refine ⟨74379089728001776546094813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49586059818667851030729875 74379089728001776546094813)
      ·
        refine ⟨27892158648000666204785555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74379089728001776546094813 27892158648000666204785555)
        ·
          refine ⟨41838237972000999307178333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27892158648000666204785555 41838237972000999307178333)
          ·
            refine ⟨15689339239500374740191875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41838237972000999307178333 15689339239500374740191875)
            ·
              refine ⟨23534008859250562110287813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15689339239500374740191875 23534008859250562110287813)
              ·
                refine ⟨4412626661109480395678965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23534008859250562110287813 4412626661109480395678965)
                ·
                  refine ⟨413683749479013787094903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412626661109480395678965 413683749479013787094903)
                  ·
                    rfl

theorem cell21_1812704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_1812704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812704 prefixEnd_1812704 := by exact prefixLift 1812704
  have htrace : WordTrace (prefixWord ++ tailWord_1812704) baseStart_1812704 baseEnd_1812704 := by
    simpa [prefixWord, tailWord_1812704, baseEnd_1812704] using wordTrace_append hprefix tailTrace_1812704
  have hstable : (prefixWord ++ tailWord_1812704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812704).length < 2 ^ (prefixWord ++ tailWord_1812704).sum := by decide
  have hdescent : baseEnd_1812704 < baseStart_1812704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812707 : List Nat := [1, 1, 1, 8, 1, 1, 1, 7]
def baseStart_1812707 : Nat := 118140960795 + 1812707 * 2 ^ 59
def prefixEnd_1812707 : Nat := 4983230072969 + 3 ^ 40 * 1812707 * 2
def baseEnd_1812707 : Nat := 137894811373295482848299

theorem tailTrace_1812707 : CollatzResearch.WordTrace tailWord_1812707 prefixEnd_1812707 137894811373295482848299 := by
  unfold tailWord_1812707
  simp only [CollatzResearch.WordTrace]
  refine ⟨66114855843879599553332375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44076570562586399702221583 66114855843879599553332375)
  ·
    refine ⟨99172283765819399329998563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66114855843879599553332375 99172283765819399329998563)
    ·
      refine ⟨148758425648729098994997845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99172283765819399329998563 148758425648729098994997845)
      ·
        refine ⟨1743262800571044128847631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 148758425648729098994997845 1743262800571044128847631)
        ·
          refine ⟨2614894200856566193271447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743262800571044128847631 2614894200856566193271447)
          ·
            refine ⟨3922341301284849289907171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614894200856566193271447 3922341301284849289907171)
            ·
              refine ⟨5883511951927273934860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922341301284849289907171 5883511951927273934860757)
              ·
                refine ⟨137894811373295482848299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5883511951927273934860757 137894811373295482848299)
                ·
                  rfl

theorem cell21_1812707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 7].length) (baseStart_1812707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812707 prefixEnd_1812707 := by exact prefixLift 1812707
  have htrace : WordTrace (prefixWord ++ tailWord_1812707) baseStart_1812707 baseEnd_1812707 := by
    simpa [prefixWord, tailWord_1812707, baseEnd_1812707] using wordTrace_append hprefix tailTrace_1812707
  have hstable : (prefixWord ++ tailWord_1812707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812707).length < 2 ^ (prefixWord ++ tailWord_1812707).sum := by decide
  have hdescent : baseEnd_1812707 < baseStart_1812707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812735 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_1812735 : Nat := 118140960795 + 1812735 * 2 ^ 59
def prefixEnd_1812735 : Nat := 4983230072969 + 3 ^ 40 * 1812735 * 2
def baseEnd_1812735 : Nat := 413690824101364622078173

theorem tailTrace_1812735 : CollatzResearch.WordTrace tailWord_1812735 prefixEnd_1812735 413690824101364622078173 := by
  unfold tailWord_1812735
  simp only [CollatzResearch.WordTrace]
  refine ⟨66115877087778160335351659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44077251391852106890234439 66115877087778160335351659)
  ·
    refine ⟨99173815631667240503027489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66115877087778160335351659 99173815631667240503027489)
    ·
      refine ⟨74380361723750430377270617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99173815631667240503027489 74380361723750430377270617)
      ·
        refine ⟨55785271292812822782952963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74380361723750430377270617 55785271292812822782952963)
        ·
          refine ⟨83677906939219234174429445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55785271292812822782952963 83677906939219234174429445)
          ·
            refine ⟨15689607551103606407705521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83677906939219234174429445 15689607551103606407705521)
            ·
              refine ⟨11767205663327704805779141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15689607551103606407705521 11767205663327704805779141)
              ·
                refine ⟨2206351061873944651083589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11767205663327704805779141 2206351061873944651083589)
                ·
                  refine ⟨413690824101364622078173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206351061873944651083589 413690824101364622078173)
                  ·
                    rfl

theorem cell21_1812735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_1812735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812735 prefixEnd_1812735 := by exact prefixLift 1812735
  have htrace : WordTrace (prefixWord ++ tailWord_1812735) baseStart_1812735 baseEnd_1812735 := by
    simpa [prefixWord, tailWord_1812735, baseEnd_1812735] using wordTrace_append hprefix tailTrace_1812735
  have hstable : (prefixWord ++ tailWord_1812735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812735).length < 2 ^ (prefixWord ++ tailWord_1812735).sum := by decide
  have hdescent : baseEnd_1812735 < baseStart_1812735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812738 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1812738 : Nat := 118140960795 + 1812738 * 2 ^ 59
def prefixEnd_1812738 : Nat := 4983230072969 + 3 ^ 40 * 1812738 * 2
def baseEnd_1812738 : Nat := 413691508742237283528167

theorem tailTrace_1812738 : CollatzResearch.WordTrace tailWord_1812738 prefixEnd_1812738 413691508742237283528167 := by
  unfold tailWord_1812738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528996626691822961927717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44077324337844861231807245 16528996626691822961927717)
  ·
    refine ⟨3099186867504716805361447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16528996626691822961927717 3099186867504716805361447)
    ·
      refine ⟨4648780301257075208042171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099186867504716805361447 4648780301257075208042171)
      ·
        refine ⟨6973170451885612812063257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648780301257075208042171 6973170451885612812063257)
        ·
          refine ⟨5229877838914209609047443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973170451885612812063257 5229877838914209609047443)
          ·
            refine ⟨7844816758371314413571165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229877838914209609047443 7844816758371314413571165)
            ·
              refine ⟨2941806284389242905089187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7844816758371314413571165 2941806284389242905089187)
              ·
                refine ⟨4412709426583864357633781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941806284389242905089187 4412709426583864357633781)
                ·
                  refine ⟨413691508742237283528167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412709426583864357633781 413691508742237283528167)
                  ·
                    rfl

theorem cell21_1812738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1812738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812738 prefixEnd_1812738 := by exact prefixLift 1812738
  have htrace : WordTrace (prefixWord ++ tailWord_1812738) baseStart_1812738 baseEnd_1812738 := by
    simpa [prefixWord, tailWord_1812738, baseEnd_1812738] using wordTrace_append hprefix tailTrace_1812738
  have hstable : (prefixWord ++ tailWord_1812738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812738).length < 2 ^ (prefixWord ++ tailWord_1812738).sum := by decide
  have hdescent : baseEnd_1812738 < baseStart_1812738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812842 : List Nat := [3, 1, 3, 3, 1, 2, 8]
def baseStart_1812842 : Nat := 118140960795 + 1812842 * 2 ^ 59
def prefixEnd_1812842 : Nat := 4983230072969 + 3 ^ 40 * 1812842 * 2
def baseEnd_1812842 : Nat := 45968360328795134866069

theorem tailTrace_1812842 : CollatzResearch.WordTrace tailWord_1812842 prefixEnd_1812842 45968360328795134866069 := by
  unfold tailWord_1812842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529944924597629402374195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44079853132260345072997853 16529944924597629402374195)
  ·
    refine ⟨24794917386896444103561293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16529944924597629402374195 24794917386896444103561293)
    ·
      refine ⟨9298094020086166538835485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24794917386896444103561293 9298094020086166538835485)
      ·
        refine ⟨3486785257532312452063307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9298094020086166538835485 3486785257532312452063307)
        ·
          refine ⟨5230177886298468678094961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486785257532312452063307 5230177886298468678094961)
          ·
            refine ⟨3922633414723851508571221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230177886298468678094961 3922633414723851508571221)
            ·
              refine ⟨45968360328795134866069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3922633414723851508571221 45968360328795134866069)
              ·
                rfl

theorem cell21_1812842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 8].length) (baseStart_1812842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812842 prefixEnd_1812842 := by exact prefixLift 1812842
  have htrace : WordTrace (prefixWord ++ tailWord_1812842) baseStart_1812842 baseEnd_1812842 := by
    simpa [prefixWord, tailWord_1812842, baseEnd_1812842] using wordTrace_append hprefix tailTrace_1812842
  have hstable : (prefixWord ++ tailWord_1812842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812842).length < 2 ^ (prefixWord ++ tailWord_1812842).sum := by decide
  have hdescent : baseEnd_1812842 < baseStart_1812842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812890 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_1812890 : Nat := 118140960795 + 1812890 * 2 ^ 59
def prefixEnd_1812890 : Nat := 4983230072969 + 3 ^ 40 * 1812890 * 2
def baseEnd_1812890 : Nat := 413726197213118796994523

theorem tailTrace_1812890 : CollatzResearch.WordTrace tailWord_1812890 prefixEnd_1812890 413726197213118796994523 := by
  unfold tailWord_1812890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530382600554155451811031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44081020268144414538162749 16530382600554155451811031)
  ·
    refine ⟨24795573900831233177716547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16530382600554155451811031 24795573900831233177716547)
    ·
      refine ⟨37193360851246849766574821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24795573900831233177716547 37193360851246849766574821)
      ·
        refine ⟨6973755159608784331232779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37193360851246849766574821 6973755159608784331232779)
        ·
          refine ⟨10460632739413176496849169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6973755159608784331232779 10460632739413176496849169)
          ·
            refine ⟨7845474554559882372636877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460632739413176496849169 7845474554559882372636877)
            ·
              refine ⟨2942052957959955889738829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7845474554559882372636877 2942052957959955889738829)
              ·
                refine ⟨1103269859234983458652061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2942052957959955889738829 1103269859234983458652061)
                ·
                  refine ⟨413726197213118796994523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103269859234983458652061 413726197213118796994523)
                  ·
                    rfl

theorem cell21_1812890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_1812890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812890 prefixEnd_1812890 := by exact prefixLift 1812890
  have htrace : WordTrace (prefixWord ++ tailWord_1812890) baseStart_1812890 baseEnd_1812890 := by
    simpa [prefixWord, tailWord_1812890, baseEnd_1812890] using wordTrace_append hprefix tailTrace_1812890
  have hstable : (prefixWord ++ tailWord_1812890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812890).length < 2 ^ (prefixWord ++ tailWord_1812890).sum := by decide
  have hdescent : baseEnd_1812890 < baseStart_1812890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812904 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_1812904 : Nat := 118140960795 + 1812904 * 2 ^ 59
def prefixEnd_1812904 : Nat := 4983230072969 + 3 ^ 40 * 1812904 * 2
def baseEnd_1812904 : Nat := 413729392203857883761161

theorem tailTrace_1812904 : CollatzResearch.WordTrace tailWord_1812904 prefixEnd_1812904 413729392203857883761161 := by
  unfold tailWord_1812904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33061020512082951099126883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44081360682777268132169177 33061020512082951099126883)
  ·
    refine ⟨49591530768124426648690325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33061020512082951099126883 49591530768124426648690325)
    ·
      refine ⟨2324603004755832499157359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49591530768124426648690325 2324603004755832499157359)
      ·
        refine ⟨3486904507133748748736039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324603004755832499157359 3486904507133748748736039)
        ·
          refine ⟨5230356760700623123104059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486904507133748748736039 5230356760700623123104059)
          ·
            refine ⟨7845535141050934684656089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230356760700623123104059 7845535141050934684656089)
            ·
              refine ⟨5884151355788201013492067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845535141050934684656089 5884151355788201013492067)
              ·
                refine ⟨8826227033682301520238101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884151355788201013492067 8826227033682301520238101)
                ·
                  refine ⟨413729392203857883761161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8826227033682301520238101 413729392203857883761161)
                  ·
                    rfl

theorem cell21_1812904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_1812904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812904 prefixEnd_1812904 := by exact prefixLift 1812904
  have htrace : WordTrace (prefixWord ++ tailWord_1812904) baseStart_1812904 baseEnd_1812904 := by
    simpa [prefixWord, tailWord_1812904, baseEnd_1812904] using wordTrace_append hprefix tailTrace_1812904
  have hstable : (prefixWord ++ tailWord_1812904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812904).length < 2 ^ (prefixWord ++ tailWord_1812904).sum := by decide
  have hdescent : baseEnd_1812904 < baseStart_1812904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812921 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 4]
def baseStart_1812921 : Nat := 118140960795 + 1812921 * 2 ^ 59
def prefixEnd_1812921 : Nat := 4983230072969 + 3 ^ 40 * 1812921 * 2
def baseEnd_1812921 : Nat := 413733271835469631977793

theorem tailTrace_1812921 : CollatzResearch.WordTrace tailWord_1812921 prefixEnd_1812921 413733271835469631977793 := by
  unfold tailWord_1812921
  simp only [CollatzResearch.WordTrace]
  refine ⟨66122661065104314101622617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44081774043402876067748411 66122661065104314101622617)
  ·
    refine ⟨49591995798828235576216963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66122661065104314101622617 49591995798828235576216963)
    ·
      refine ⟨74387993698242353364325445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49591995798828235576216963 74387993698242353364325445)
      ·
        refine ⟨13947748818420441255811021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74387993698242353364325445 13947748818420441255811021)
        ·
          refine ⟨5230405806907665470929133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13947748818420441255811021 5230405806907665470929133)
          ·
            refine ⟨1961402177590374551598425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5230405806907665470929133 1961402177590374551598425)
            ·
              refine ⟨1471051633192780913698819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961402177590374551598425 1471051633192780913698819)
              ·
                refine ⟨2206577449789171370548229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471051633192780913698819 2206577449789171370548229)
                ·
                  refine ⟨413733271835469631977793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206577449789171370548229 413733271835469631977793)
                  ·
                    rfl

theorem cell21_1812921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_1812921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1812921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1812921 prefixEnd_1812921 := by exact prefixLift 1812921
  have htrace : WordTrace (prefixWord ++ tailWord_1812921) baseStart_1812921 baseEnd_1812921 := by
    simpa [prefixWord, tailWord_1812921, baseEnd_1812921] using wordTrace_append hprefix tailTrace_1812921
  have hstable : (prefixWord ++ tailWord_1812921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812921).length < 2 ^ (prefixWord ++ tailWord_1812921).sum := by decide
  have hdescent : baseEnd_1812921 < baseStart_1812921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813025 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 3]
def baseStart_1813025 : Nat := 118140960795 + 1813025 * 2 ^ 59
def prefixEnd_1813025 : Nat := 4983230072969 + 3 ^ 40 * 1813025 * 2
def baseEnd_1813025 : Nat := 413757006052388562244247

theorem tailTrace_1813025 : CollatzResearch.WordTrace tailWord_1813025 prefixEnd_1813025 413757006052388562244247 := by
  unfold tailWord_1813025
  simp only [CollatzResearch.WordTrace]
  refine ⟨66126454256727539863408529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44084302837818359908939019 66126454256727539863408529)
  ·
    refine ⟨49594840692545654897556397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66126454256727539863408529 49594840692545654897556397)
    ·
      refine ⟨18598065259704620586583649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49594840692545654897556397 18598065259704620586583649)
      ·
        refine ⟨13948548944778465439937737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18598065259704620586583649 13948548944778465439937737)
        ·
          refine ⟨10461411708583849079953303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13948548944778465439937737 10461411708583849079953303)
          ·
            refine ⟨15692117562875773619929955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461411708583849079953303 15692117562875773619929955)
            ·
              refine ⟨23538176344313660429894933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692117562875773619929955 23538176344313660429894933)
              ·
                refine ⟨1103352016139702832651325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23538176344313660429894933 1103352016139702832651325)
                ·
                  refine ⟨413757006052388562244247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103352016139702832651325 413757006052388562244247)
                  ·
                    rfl

theorem cell21_1813025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_1813025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813025 prefixEnd_1813025 := by exact prefixLift 1813025
  have htrace : WordTrace (prefixWord ++ tailWord_1813025) baseStart_1813025 baseEnd_1813025 := by
    simpa [prefixWord, tailWord_1813025, baseEnd_1813025] using wordTrace_append hprefix tailTrace_1813025
  have hstable : (prefixWord ++ tailWord_1813025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813025).length < 2 ^ (prefixWord ++ tailWord_1813025).sum := by decide
  have hdescent : baseEnd_1813025 < baseStart_1813025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813067 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_1813067 : Nat := 118140960795 + 1813067 * 2 ^ 59
def prefixEnd_1813067 : Nat := 4983230072969 + 3 ^ 40 * 1813067 * 2
def baseEnd_1813067 : Nat := 413766591024605822544161

theorem tailTrace_1813067 : CollatzResearch.WordTrace tailWord_1813067 prefixEnd_1813067 413766591024605822544161 := by
  unfold tailWord_1813067
  simp only [CollatzResearch.WordTrace]
  refine ⟨66127986122575381036437455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44085324081716920690958303 66127986122575381036437455)
  ·
    refine ⟨99191979183863071554656183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66127986122575381036437455 99191979183863071554656183)
    ·
      refine ⟨148787968775794607331984275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99191979183863071554656183 148787968775794607331984275)
      ·
        refine ⟨223181953163691910997976413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148787968775794607331984275 223181953163691910997976413)
        ·
          refine ⟨83693232436384466624241155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223181953163691910997976413 83693232436384466624241155)
          ·
            refine ⟨125539848654576699936361733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83693232436384466624241155 125539848654576699936361733)
            ·
              refine ⟨23538721622733131238067825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125539848654576699936361733 23538721622733131238067825)
              ·
                refine ⟨17654041217049848428550869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23538721622733131238067825 17654041217049848428550869)
                ·
                  refine ⟨413766591024605822544161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17654041217049848428550869 413766591024605822544161)
                  ·
                    rfl

theorem cell21_1813067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_1813067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813067 prefixEnd_1813067 := by exact prefixLift 1813067
  have htrace : WordTrace (prefixWord ++ tailWord_1813067) baseStart_1813067 baseEnd_1813067 := by
    simpa [prefixWord, tailWord_1813067, baseEnd_1813067] using wordTrace_append hprefix tailTrace_1813067
  have hstable : (prefixWord ++ tailWord_1813067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813067).length < 2 ^ (prefixWord ++ tailWord_1813067).sum := by decide
  have hdescent : baseEnd_1813067 < baseStart_1813067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813208 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_1813208 : Nat := 118140960795 + 1813208 * 2 ^ 59
def prefixEnd_1813208 : Nat := 4983230072969 + 3 ^ 40 * 1813208 * 2
def baseEnd_1813208 : Nat := 413798769145620910693873

theorem tailTrace_1813208 : CollatzResearch.WordTrace tailWord_1813208 prefixEnd_1813208 413798769145620910693873 := by
  unfold tailWord_1813208
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066564407532281058660139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44088752543376374744880185 33066564407532281058660139)
  ·
    refine ⟨49599846611298421587990209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33066564407532281058660139 49599846611298421587990209)
    ·
      refine ⟨37199884958473816190992657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49599846611298421587990209 37199884958473816190992657)
      ·
        refine ⟨27899913718855362143244493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37199884958473816190992657 27899913718855362143244493)
        ·
          refine ⟨10462467644570760803716685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27899913718855362143244493 10462467644570760803716685)
          ·
            refine ⟨3923425366714035301393757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10462467644570760803716685 3923425366714035301393757)
            ·
              refine ⟨1471284512517763238022659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3923425366714035301393757 1471284512517763238022659)
              ·
                refine ⟨2206926768776644857033989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471284512517763238022659 2206926768776644857033989)
                ·
                  refine ⟨413798769145620910693873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206926768776644857033989 413798769145620910693873)
                  ·
                    rfl

theorem cell21_1813208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_1813208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813208 prefixEnd_1813208 := by exact prefixLift 1813208
  have htrace : WordTrace (prefixWord ++ tailWord_1813208) baseStart_1813208 baseEnd_1813208 := by
    simpa [prefixWord, tailWord_1813208, baseEnd_1813208] using wordTrace_append hprefix tailTrace_1813208
  have hstable : (prefixWord ++ tailWord_1813208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813208).length < 2 ^ (prefixWord ++ tailWord_1813208).sum := by decide
  have hdescent : baseEnd_1813208 < baseStart_1813208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813371 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_1813371 : Nat := 118140960795 + 1813371 * 2 ^ 59
def prefixEnd_1813371 : Nat := 4983230072969 + 3 ^ 40 * 1813371 * 2
def baseEnd_1813371 : Nat := 413835967966368849476873

theorem tailTrace_1813371 : CollatzResearch.WordTrace tailWord_1813371 prefixEnd_1813371 413835967966368849476873 := by
  unfold tailWord_1813371
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139073913474040955503967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44092715942316027303669311 66139073913474040955503967)
  ·
    refine ⟨99208610870211061433255951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66139073913474040955503967 99208610870211061433255951)
    ·
      refine ⟨148812916305316592149883927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99208610870211061433255951 148812916305316592149883927)
      ·
        refine ⟨223219374457974888224825891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148812916305316592149883927 223219374457974888224825891)
        ·
          refine ⟨334829061686962332337238837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223219374457974888224825891 334829061686962332337238837)
          ·
            refine ⟨31390224533152718656616141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334829061686962332337238837 31390224533152718656616141)
            ·
              refine ⟨11771334199932269496231053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31390224533152718656616141 11771334199932269496231053)
              ·
                refine ⟨4414250324974601061086645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11771334199932269496231053 4414250324974601061086645)
                ·
                  refine ⟨413835967966368849476873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414250324974601061086645 413835967966368849476873)
                  ·
                    rfl

theorem cell21_1813371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_1813371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813371 prefixEnd_1813371 := by exact prefixLift 1813371
  have htrace : WordTrace (prefixWord ++ tailWord_1813371) baseStart_1813371 baseEnd_1813371 := by
    simpa [prefixWord, tailWord_1813371, baseEnd_1813371] using wordTrace_append hprefix tailTrace_1813371
  have hstable : (prefixWord ++ tailWord_1813371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813371).length < 2 ^ (prefixWord ++ tailWord_1813371).sum := by decide
  have hdescent : baseEnd_1813371 < baseStart_1813371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813433 : List Nat := [1, 2, 1, 4, 2, 3, 2, 6]
def baseStart_1813433 : Nat := 118140960795 + 1813433 * 2 ^ 59
def prefixEnd_1813433 : Nat := 4983230072969 + 3 ^ 40 * 1813433 * 2
def baseEnd_1813433 : Nat := 137950039070356839814471

theorem tailTrace_1813433 : CollatzResearch.WordTrace tailWord_1813433 prefixEnd_1813433 137950039070356839814471 := by
  unfold tailWord_1813433
  simp only [CollatzResearch.WordTrace]
  refine ⟨66141335239249425544260953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44094223492832950362840635 66141335239249425544260953)
  ·
    refine ⟨49606001429437069158195715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66141335239249425544260953 49606001429437069158195715)
    ·
      refine ⟨74409002144155603737293573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49606001429437069158195715 74409002144155603737293573)
      ·
        refine ⟨13951687902029175700742545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74409002144155603737293573 13951687902029175700742545)
        ·
          refine ⟨10463765926521881775556909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13951687902029175700742545 10463765926521881775556909)
          ·
            refine ⟨3923912222445705665833841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10463765926521881775556909 3923912222445705665833841)
            ·
              refine ⟨2942934166834279249375381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3923912222445705665833841 2942934166834279249375381)
              ·
                refine ⟨137950039070356839814471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2942934166834279249375381 137950039070356839814471)
                ·
                  rfl

theorem cell21_1813433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_1813433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813433 prefixEnd_1813433 := by exact prefixLift 1813433
  have htrace : WordTrace (prefixWord ++ tailWord_1813433) baseStart_1813433 baseEnd_1813433 := by
    simpa [prefixWord, tailWord_1813433, baseEnd_1813433] using wordTrace_append hprefix tailTrace_1813433
  have hstable : (prefixWord ++ tailWord_1813433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813433).length < 2 ^ (prefixWord ++ tailWord_1813433).sum := by decide
  have hdescent : baseEnd_1813433 < baseStart_1813433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813447 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_1813447 : Nat := 118140960795 + 1813447 * 2 ^ 59
def prefixEnd_1813447 : Nat := 4983230072969 + 3 ^ 40 * 1813447 * 2
def baseEnd_1813447 : Nat := 413853312201809606210051

theorem tailTrace_1813447 : CollatzResearch.WordTrace tailWord_1813447 prefixEnd_1813447 413853312201809606210051 := by
  unfold tailWord_1813447
  simp only [CollatzResearch.WordTrace]
  refine ⟨66141845861198705935270595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44094563907465803956847063 66141845861198705935270595)
  ·
    refine ⟨99212768791798058902905893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66141845861198705935270595 99212768791798058902905893)
    ·
      refine ⟨18602394148462136044294855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99212768791798058902905893 18602394148462136044294855)
      ·
        refine ⟨27903591222693204066442283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18602394148462136044294855 27903591222693204066442283)
        ·
          refine ⟨41855386834039806099663425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27903591222693204066442283 41855386834039806099663425)
          ·
            refine ⟨31391540125529854574747569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41855386834039806099663425 31391540125529854574747569)
            ·
              refine ⟨23543655094147390931060677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31391540125529854574747569 23543655094147390931060677)
              ·
                refine ⟨4414435330152635799573877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23543655094147390931060677 4414435330152635799573877)
                ·
                  refine ⟨413853312201809606210051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414435330152635799573877 413853312201809606210051)
                  ·
                    rfl

theorem cell21_1813447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_1813447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813447 prefixEnd_1813447 := by exact prefixLift 1813447
  have htrace : WordTrace (prefixWord ++ tailWord_1813447) baseStart_1813447 baseEnd_1813447 := by
    simpa [prefixWord, tailWord_1813447, baseEnd_1813447] using wordTrace_append hprefix tailTrace_1813447
  have hstable : (prefixWord ++ tailWord_1813447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813447).length < 2 ^ (prefixWord ++ tailWord_1813447).sum := by decide
  have hdescent : baseEnd_1813447 < baseStart_1813447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813509 : List Nat := [1, 3, 1, 1, 2, 3, 5, 5]
def baseStart_1813509 : Nat := 118140960795 + 1813509 * 2 ^ 59
def prefixEnd_1813509 : Nat := 4983230072969 + 3 ^ 40 * 1813509 * 2
def baseEnd_1813509 : Nat := 137955820482170425392197

theorem tailTrace_1813509 : CollatzResearch.WordTrace tailWord_1813509 prefixEnd_1813509 137955820482170425392197 := by
  unfold tailWord_1813509
  simp only [CollatzResearch.WordTrace]
  refine ⟨66144107186974090524027581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44096071457982727016018387 66144107186974090524027581)
  ·
    refine ⟨24804040195115283946510343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66144107186974090524027581 24804040195115283946510343)
    ·
      refine ⟨37206060292672925919765515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24804040195115283946510343 37206060292672925919765515)
      ·
        refine ⟨55809090439009388879648273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37206060292672925919765515 55809090439009388879648273)
        ·
          refine ⟨41856817829257041659736205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55809090439009388879648273 41856817829257041659736205)
          ·
            refine ⟨15696306685971390622401077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41856817829257041659736205 15696306685971390622401077)
            ·
              refine ⟨1471528751809817870850101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15696306685971390622401077 1471528751809817870850101)
              ·
                refine ⟨137955820482170425392197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1471528751809817870850101 137955820482170425392197)
                ·
                  rfl

theorem cell21_1813509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 5].length) (baseStart_1813509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813509 prefixEnd_1813509 := by exact prefixLift 1813509
  have htrace : WordTrace (prefixWord ++ tailWord_1813509) baseStart_1813509 baseEnd_1813509 := by
    simpa [prefixWord, tailWord_1813509, baseEnd_1813509] using wordTrace_append hprefix tailTrace_1813509
  have hstable : (prefixWord ++ tailWord_1813509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813509).length < 2 ^ (prefixWord ++ tailWord_1813509).sum := by decide
  have hdescent : baseEnd_1813509 < baseStart_1813509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813540 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1813540 : Nat := 118140960795 + 1813540 * 2 ^ 59
def prefixEnd_1813540 : Nat := 4983230072969 + 3 ^ 40 * 1813540 * 2
def baseEnd_1813540 : Nat := 413874536068862111159861

theorem tailTrace_1813540 : CollatzResearch.WordTrace tailWord_1813540 prefixEnd_1813540 413874536068862111159861 := by
  unfold tailWord_1813540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33072618924930891409203037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44096825233241188545604049 33072618924930891409203037)
  ·
    refine ⟨12402232096849084278451139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33072618924930891409203037 12402232096849084278451139)
    ·
      refine ⟨18603348145273626417676709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12402232096849084278451139 18603348145273626417676709)
      ·
        refine ⟨3488127777238804953314383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18603348145273626417676709 3488127777238804953314383)
        ·
          refine ⟨5232191665858207429971575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488127777238804953314383 5232191665858207429971575)
          ·
            refine ⟨7848287498787311144957363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232191665858207429971575 7848287498787311144957363)
            ·
              refine ⟨11772431248180966717436045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848287498787311144957363 11772431248180966717436045)
              ·
                refine ⟨4414661718067862519038517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11772431248180966717436045 4414661718067862519038517)
                ·
                  refine ⟨413874536068862111159861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414661718067862519038517 413874536068862111159861)
                  ·
                    rfl

theorem cell21_1813540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1813540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813540 prefixEnd_1813540 := by exact prefixLift 1813540
  have htrace : WordTrace (prefixWord ++ tailWord_1813540) baseStart_1813540 baseEnd_1813540 := by
    simpa [prefixWord, tailWord_1813540, baseEnd_1813540] using wordTrace_append hprefix tailTrace_1813540
  have hstable : (prefixWord ++ tailWord_1813540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813540).length < 2 ^ (prefixWord ++ tailWord_1813540).sum := by decide
  have hdescent : baseEnd_1813540 < baseStart_1813540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813568 : List Nat := [2, 1, 1, 2, 2, 3, 3, 7]
def baseStart_1813568 : Nat := 118140960795 + 1813568 * 2 ^ 59
def prefixEnd_1813568 : Nat := 4983230072969 + 3 ^ 40 * 1813568 * 2
def baseEnd_1813568 : Nat := 137960308683446761564379

theorem tailTrace_1813568 : CollatzResearch.WordTrace tailWord_1813568 prefixEnd_1813568 137960308683446761564379 := by
  unfold tailWord_1813568
  simp only [CollatzResearch.WordTrace]
  refine ⟨33073129546880171800212679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44097506062506895733616905 33073129546880171800212679)
  ·
    refine ⟨49609694320320257700319019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33073129546880171800212679 49609694320320257700319019)
    ·
      refine ⟨74414541480480386550478529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49609694320320257700319019 74414541480480386550478529)
      ·
        refine ⟨55810906110360289912858897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74414541480480386550478529 55810906110360289912858897)
        ·
          refine ⟨41858179582770217434644173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55810906110360289912858897 41858179582770217434644173)
          ·
            refine ⟨15696817343538831537991565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41858179582770217434644173 15696817343538831537991565)
            ·
              refine ⟨5886306503827061826746837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15696817343538831537991565 5886306503827061826746837)
              ·
                refine ⟨137960308683446761564379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5886306503827061826746837 137960308683446761564379)
                ·
                  rfl

theorem cell21_1813568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_1813568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813568 prefixEnd_1813568 := by exact prefixLift 1813568
  have htrace : WordTrace (prefixWord ++ tailWord_1813568) baseStart_1813568 baseEnd_1813568 := by
    simpa [prefixWord, tailWord_1813568, baseEnd_1813568] using wordTrace_append hprefix tailTrace_1813568
  have hstable : (prefixWord ++ tailWord_1813568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813568).length < 2 ^ (prefixWord ++ tailWord_1813568).sum := by decide
  have hdescent : baseEnd_1813568 < baseStart_1813568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813602 : List Nat := [3, 3, 2, 2, 1, 2, 2, 6]
def baseStart_1813602 : Nat := 118140960795 + 1813602 * 2 ^ 59
def prefixEnd_1813602 : Nat := 4983230072969 + 3 ^ 40 * 1813602 * 2
def baseEnd_1813602 : Nat := 137962895104521260375467

theorem tailTrace_1813602 : CollatzResearch.WordTrace tailWord_1813602 prefixEnd_1813602 137962895104521260375467 := by
  unfold tailWord_1813602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16536874793909291851790765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44098332783758111604775373 16536874793909291851790765)
  ·
    refine ⟨6201328047715984444421537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16536874793909291851790765 6201328047715984444421537)
    ·
      refine ⟨4650996035786988333316153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6201328047715984444421537 4650996035786988333316153)
      ·
        refine ⟨3488247026840241249987115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4650996035786988333316153 3488247026840241249987115)
        ·
          refine ⟨5232370540260361874980673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488247026840241249987115 5232370540260361874980673)
          ·
            refine ⟨3924277905195271406235505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232370540260361874980673 3924277905195271406235505)
            ·
              refine ⟨2943208428896453554676629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924277905195271406235505 2943208428896453554676629)
              ·
                refine ⟨137962895104521260375467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2943208428896453554676629 137962895104521260375467)
                ·
                  rfl

theorem cell21_1813602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_1813602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813602 prefixEnd_1813602 := by exact prefixLift 1813602
  have htrace : WordTrace (prefixWord ++ tailWord_1813602) baseStart_1813602 baseEnd_1813602 := by
    simpa [prefixWord, tailWord_1813602, baseEnd_1813602] using wordTrace_append hprefix tailTrace_1813602
  have hstable : (prefixWord ++ tailWord_1813602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813602).length < 2 ^ (prefixWord ++ tailWord_1813602).sum := by decide
  have hdescent : baseEnd_1813602 < baseStart_1813602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813650 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1813650 : Nat := 118140960795 + 1813650 * 2 ^ 59
def prefixEnd_1813650 : Nat := 4983230072969 + 3 ^ 40 * 1813650 * 2
def baseEnd_1813650 : Nat := 413899639567526364326303

theorem tailTrace_1813650 : CollatzResearch.WordTrace tailWord_1813650 prefixEnd_1813650 413899639567526364326303 := by
  unfold tailWord_1813650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537312469865817901227601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44099499919642181069940269 16537312469865817901227601)
  ·
    refine ⟨12402984352399363425920701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16537312469865817901227601 12402984352399363425920701)
    ·
      refine ⟨4651119132149761284720263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12402984352399363425920701 4651119132149761284720263)
      ·
        refine ⟨6976678698224641927080395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651119132149761284720263 6976678698224641927080395)
        ·
          refine ⟨10465018047336962890620593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976678698224641927080395 10465018047336962890620593)
          ·
            refine ⟨7848763535502722167965445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465018047336962890620593 7848763535502722167965445)
            ·
              refine ⟨1471643162906760406493521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7848763535502722167965445 1471643162906760406493521)
              ·
                refine ⟨1103732372180070304870141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471643162906760406493521 1103732372180070304870141)
                ·
                  refine ⟨413899639567526364326303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103732372180070304870141 413899639567526364326303)
                  ·
                    rfl

theorem cell21_1813650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1813650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813650 prefixEnd_1813650 := by exact prefixLift 1813650
  have htrace : WordTrace (prefixWord ++ tailWord_1813650) baseStart_1813650 baseEnd_1813650 := by
    simpa [prefixWord, tailWord_1813650, baseEnd_1813650] using wordTrace_append hprefix tailTrace_1813650
  have hstable : (prefixWord ++ tailWord_1813650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813650).length < 2 ^ (prefixWord ++ tailWord_1813650).sum := by decide
  have hdescent : baseEnd_1813650 < baseStart_1813650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813698 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1813698 : Nat := 118140960795 + 1813698 * 2 ^ 59
def prefixEnd_1813698 : Nat := 4983230072969 + 3 ^ 40 * 1813698 * 2
def baseEnd_1813698 : Nat := 413910593821488947526205

theorem tailTrace_1813698 : CollatzResearch.WordTrace tailWord_1813698 prefixEnd_1813698 413910593821488947526205 := by
  unfold tailWord_1813698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537750145822343950664437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44100667055526250535105165 16537750145822343950664437)
  ·
    refine ⟨1550414076170844745374791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16537750145822343950664437 1550414076170844745374791)
    ·
      refine ⟨2325621114256267118062187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550414076170844745374791 2325621114256267118062187)
      ·
        refine ⟨3488431671384400677093281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325621114256267118062187 3488431671384400677093281)
        ·
          refine ⟨2616323753538300507819961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488431671384400677093281 2616323753538300507819961)
          ·
            refine ⟨1962242815153725380864971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616323753538300507819961 1962242815153725380864971)
            ·
              refine ⟨2943364222730588071297457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962242815153725380864971 2943364222730588071297457)
              ·
                refine ⟨2207523167047941053473093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943364222730588071297457 2207523167047941053473093)
                ·
                  refine ⟨413910593821488947526205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207523167047941053473093 413910593821488947526205)
                  ·
                    rfl

theorem cell21_1813698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1813698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813698 prefixEnd_1813698 := by exact prefixLift 1813698
  have htrace : WordTrace (prefixWord ++ tailWord_1813698) baseStart_1813698 baseEnd_1813698 := by
    simpa [prefixWord, tailWord_1813698, baseEnd_1813698] using wordTrace_append hprefix tailTrace_1813698
  have hstable : (prefixWord ++ tailWord_1813698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813698).length < 2 ^ (prefixWord ++ tailWord_1813698).sum := by decide
  have hdescent : baseEnd_1813698 < baseStart_1813698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813706 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_1813706 : Nat := 118140960795 + 1813706 * 2 ^ 59
def prefixEnd_1813706 : Nat := 4983230072969 + 3 ^ 40 * 1813706 * 2
def baseEnd_1813706 : Nat := 413912419530482711392855

theorem tailTrace_1813706 : CollatzResearch.WordTrace tailWord_1813706 prefixEnd_1813706 413912419530482711392855 := by
  unfold tailWord_1813706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537823091815098292237243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44100861578173595445965981 16537823091815098292237243)
  ·
    refine ⟨24806734637722647438355865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16537823091815098292237243 24806734637722647438355865)
    ·
      refine ⟨18605050978291985578766899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24806734637722647438355865 18605050978291985578766899)
      ·
        refine ⟨27907576467437978368150349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18605050978291985578766899 27907576467437978368150349)
        ·
          refine ⟨10465341175289241888056381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27907576467437978368150349 10465341175289241888056381)
          ·
            refine ⟨3924502940733465708021143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10465341175289241888056381 3924502940733465708021143)
            ·
              refine ⟨5886754411100198562031715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924502940733465708021143 5886754411100198562031715)
              ·
                refine ⟨8830131616650297843047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886754411100198562031715 8830131616650297843047573)
                ·
                  refine ⟨413912419530482711392855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8830131616650297843047573 413912419530482711392855)
                  ·
                    rfl

theorem cell21_1813706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_1813706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813706 prefixEnd_1813706 := by exact prefixLift 1813706
  have htrace : WordTrace (prefixWord ++ tailWord_1813706) baseStart_1813706 baseEnd_1813706 := by
    simpa [prefixWord, tailWord_1813706, baseEnd_1813706] using wordTrace_append hprefix tailTrace_1813706
  have hstable : (prefixWord ++ tailWord_1813706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813706).length < 2 ^ (prefixWord ++ tailWord_1813706).sum := by decide
  have hdescent : baseEnd_1813706 < baseStart_1813706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813765 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_1813765 : Nat := 118140960795 + 1813765 * 2 ^ 59
def prefixEnd_1813765 : Nat := 4983230072969 + 3 ^ 40 * 1813765 * 2
def baseEnd_1813765 : Nat := 413925884134311719909401

theorem tailTrace_1813765 : CollatzResearch.WordTrace tailWord_1813765 prefixEnd_1813765 413925884134311719909401 := by
  unfold tailWord_1813765
  simp only [CollatzResearch.WordTrace]
  refine ⟨66153444274046646245346749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44102296182697764163564499 66153444274046646245346749)
  ·
    refine ⟨24807541602767492342005031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66153444274046646245346749 24807541602767492342005031)
    ·
      refine ⟨37211312404151238513007547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24807541602767492342005031 37211312404151238513007547)
      ·
        refine ⟨55816968606226857769511321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37211312404151238513007547 55816968606226857769511321)
        ·
          refine ⟨41862726454670143327133491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55816968606226857769511321 41862726454670143327133491)
          ·
            refine ⟨62794089682005214990700237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41862726454670143327133491 62794089682005214990700237)
            ·
              refine ⟨23547783630751955621512589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62794089682005214990700237 23547783630751955621512589)
              ·
                refine ⟨8830418861531983358067221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23547783630751955621512589 8830418861531983358067221)
                ·
                  refine ⟨413925884134311719909401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8830418861531983358067221 413925884134311719909401)
                  ·
                    rfl

theorem cell21_1813765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_1813765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813765 prefixEnd_1813765 := by exact prefixLift 1813765
  have htrace : WordTrace (prefixWord ++ tailWord_1813765) baseStart_1813765 baseEnd_1813765 := by
    simpa [prefixWord, tailWord_1813765, baseEnd_1813765] using wordTrace_append hprefix tailTrace_1813765
  have hstable : (prefixWord ++ tailWord_1813765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813765).length < 2 ^ (prefixWord ++ tailWord_1813765).sum := by decide
  have hdescent : baseEnd_1813765 < baseStart_1813765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813796 : List Nat := [2, 3, 1, 3, 1, 1, 1, 9]
def baseStart_1813796 : Nat := 118140960795 + 1813796 * 2 ^ 59
def prefixEnd_1813796 : Nat := 4983230072969 + 3 ^ 40 * 1813796 * 2
def baseEnd_1813796 : Nat := 137977652918887518297557

theorem tailTrace_1813796 : CollatzResearch.WordTrace tailWord_1813796 prefixEnd_1813796 137977652918887518297557 := by
  unfold tailWord_1813796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077287468467169269862621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44103049957956225693150161 33077287468467169269862621)
  ·
    refine ⟨12403982800675188476198483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33077287468467169269862621 12403982800675188476198483)
    ·
      refine ⟨18605974201012782714297725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12403982800675188476198483 18605974201012782714297725)
      ·
        refine ⟨6977240325379793517861647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18605974201012782714297725 6977240325379793517861647)
        ·
          refine ⟨10465860488069690276792471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977240325379793517861647 10465860488069690276792471)
          ·
            refine ⟨15698790732104535415188707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465860488069690276792471 15698790732104535415188707)
            ·
              refine ⟨23548186098156803122783061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15698790732104535415188707 23548186098156803122783061)
              ·
                refine ⟨137977652918887518297557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23548186098156803122783061 137977652918887518297557)
                ·
                  rfl

theorem cell21_1813796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_1813796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813796 prefixEnd_1813796 := by exact prefixLift 1813796
  have htrace : WordTrace (prefixWord ++ tailWord_1813796) baseStart_1813796 baseEnd_1813796 := by
    simpa [prefixWord, tailWord_1813796, baseEnd_1813796] using wordTrace_append hprefix tailTrace_1813796
  have hstable : (prefixWord ++ tailWord_1813796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813796).length < 2 ^ (prefixWord ++ tailWord_1813796).sum := by decide
  have hdescent : baseEnd_1813796 < baseStart_1813796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813858 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1813858 : Nat := 118140960795 + 1813858 * 2 ^ 59
def prefixEnd_1813858 : Nat := 4983230072969 + 3 ^ 40 * 1813858 * 2
def baseEnd_1813858 : Nat := 413947108001364224859211

theorem tailTrace_1813858 : CollatzResearch.WordTrace tailWord_1813858 prefixEnd_1813858 413947108001364224859211 := by
  unfold tailWord_1813858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539209065677430782120557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44104557508473148752321485 16539209065677430782120557)
  ·
    refine ⟨6202203399629036543295209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16539209065677430782120557 6202203399629036543295209)
    ·
      refine ⟨4651652549721777407471407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6202203399629036543295209 4651652549721777407471407)
      ·
        refine ⟨6977478824582666111207111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651652549721777407471407 6977478824582666111207111)
        ·
          refine ⟨10466218236873999166810667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977478824582666111207111 10466218236873999166810667)
          ·
            refine ⟨15699327355310998750216001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10466218236873999166810667 15699327355310998750216001)
            ·
              refine ⟨11774495516483249062662001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15699327355310998750216001 11774495516483249062662001)
              ·
                refine ⟨8830871637362436796996501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774495516483249062662001 8830871637362436796996501)
                ·
                  refine ⟨413947108001364224859211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8830871637362436796996501 413947108001364224859211)
                  ·
                    rfl

theorem cell21_1813858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1813858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813858 prefixEnd_1813858 := by exact prefixLift 1813858
  have htrace : WordTrace (prefixWord ++ tailWord_1813858) baseStart_1813858 baseEnd_1813858 := by
    simpa [prefixWord, tailWord_1813858, baseEnd_1813858] using wordTrace_append hprefix tailTrace_1813858
  have hstable : (prefixWord ++ tailWord_1813858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813858).length < 2 ^ (prefixWord ++ tailWord_1813858).sum := by decide
  have hdescent : baseEnd_1813858 < baseStart_1813858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813906 : List Nat := [3, 2, 3, 3, 1, 1, 1, 7]
def baseStart_1813906 : Nat := 118140960795 + 1813906 * 2 ^ 59
def prefixEnd_1813906 : Nat := 4983230072969 + 3 ^ 40 * 1813906 * 2
def baseEnd_1813906 : Nat := 137986020751775602686371

theorem tailTrace_1813906 : CollatzResearch.WordTrace tailWord_1813906 prefixEnd_1813906 137986020751775602686371 := by
  unfold tailWord_1813906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539646741633956831557393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44105724644357218217486381 16539646741633956831557393)
  ·
    refine ⟨12404735056225467623668045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16539646741633956831557393 12404735056225467623668045)
    ·
      refine ⟨4651775646084550358875517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12404735056225467623668045 4651775646084550358875517)
      ·
        refine ⟨1744415867281706384578319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4651775646084550358875517 1744415867281706384578319)
        ·
          refine ⟨2616623800922559576867479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744415867281706384578319 2616623800922559576867479)
          ·
            refine ⟨3924935701383839365301219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616623800922559576867479 3924935701383839365301219)
            ·
              refine ⟨5887403552075759047951829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924935701383839365301219 5887403552075759047951829)
              ·
                refine ⟨137986020751775602686371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5887403552075759047951829 137986020751775602686371)
                ·
                  rfl

theorem cell21_1813906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_1813906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813906 prefixEnd_1813906 := by exact prefixLift 1813906
  have htrace : WordTrace (prefixWord ++ tailWord_1813906) baseStart_1813906 baseEnd_1813906 := by
    simpa [prefixWord, tailWord_1813906, baseEnd_1813906] using wordTrace_append hprefix tailTrace_1813906
  have hstable : (prefixWord ++ tailWord_1813906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813906).length < 2 ^ (prefixWord ++ tailWord_1813906).sum := by decide
  have hdescent : baseEnd_1813906 < baseStart_1813906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813937 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 3]
def baseStart_1813937 : Nat := 118140960795 + 1813937 * 2 ^ 59
def prefixEnd_1813937 : Nat := 4983230072969 + 3 ^ 40 * 1813937 * 2
def baseEnd_1813937 : Nat := 413965136877677643042383

theorem tailTrace_1813937 : CollatzResearch.WordTrace tailWord_1813937 prefixEnd_1813937 413965136877677643042383 := by
  unfold tailWord_1813937
  simp only [CollatzResearch.WordTrace]
  refine ⟨66159717629423519620608065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44106478419615679747072043 66159717629423519620608065)
  ·
    refine ⟨49619788222067639715456049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66159717629423519620608065 49619788222067639715456049)
    ·
      refine ⟨37214841166550729786592037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49619788222067639715456049 37214841166550729786592037)
      ·
        refine ⟨6977782718728261834986007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37214841166550729786592037 6977782718728261834986007)
        ·
          refine ⟨10466674078092392752479011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977782718728261834986007 10466674078092392752479011)
          ·
            refine ⟨15700011117138589128718517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10466674078092392752479011 15700011117138589128718517)
            ·
              refine ⟨1471876042231742730817361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15700011117138589128718517 1471876042231742730817361)
              ·
                refine ⟨1103907031673807048113021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471876042231742730817361 1103907031673807048113021)
                ·
                  refine ⟨413965136877677643042383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103907031673807048113021 413965136877677643042383)
                  ·
                    rfl

theorem cell21_1813937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_1813937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1813937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1813937 prefixEnd_1813937 := by exact prefixLift 1813937
  have htrace : WordTrace (prefixWord ++ tailWord_1813937) baseStart_1813937 baseEnd_1813937 := by
    simpa [prefixWord, tailWord_1813937, baseEnd_1813937] using wordTrace_append hprefix tailTrace_1813937
  have hstable : (prefixWord ++ tailWord_1813937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813937).length < 2 ^ (prefixWord ++ tailWord_1813937).sum := by decide
  have hdescent : baseEnd_1813937 < baseStart_1813937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814007 : List Nat := [1, 1, 3, 1, 1, 1, 1, 12]
def baseStart_1814007 : Nat := 118140960795 + 1814007 * 2 ^ 59
def prefixEnd_1814007 : Nat := 4983230072969 + 3 ^ 40 * 1814007 * 2
def baseEnd_1814007 : Nat := 137993703943791025625191

theorem tailTrace_1814007 : CollatzResearch.WordTrace tailWord_1814007 prefixEnd_1814007 137993703943791025625191 := by
  unfold tailWord_1814007
  simp only [CollatzResearch.WordTrace]
  refine ⟨66162270739169921575656275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44108180492779947717104183 66162270739169921575656275)
  ·
    refine ⟨99243406108754882363484413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66162270739169921575656275 99243406108754882363484413)
    ·
      refine ⟨37216277290783080886306655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99243406108754882363484413 37216277290783080886306655)
      ·
        refine ⟨55824415936174621329459983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37216277290783080886306655 55824415936174621329459983)
        ·
          refine ⟨83736623904261931994189975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55824415936174621329459983 83736623904261931994189975)
          ·
            refine ⟨125604935856392897991284963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83736623904261931994189975 125604935856392897991284963)
            ·
              refine ⟨188407403784589346986927445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125604935856392897991284963 188407403784589346986927445)
              ·
                refine ⟨137993703943791025625191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 188407403784589346986927445 137993703943791025625191)
                ·
                  rfl

theorem cell21_1814007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_1814007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814007 prefixEnd_1814007 := by exact prefixLift 1814007
  have htrace : WordTrace (prefixWord ++ tailWord_1814007) baseStart_1814007 baseEnd_1814007 := by
    simpa [prefixWord, tailWord_1814007, baseEnd_1814007] using wordTrace_append hprefix tailTrace_1814007
  have hstable : (prefixWord ++ tailWord_1814007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814007).length < 2 ^ (prefixWord ++ tailWord_1814007).sum := by decide
  have hdescent : baseEnd_1814007 < baseStart_1814007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814120 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_1814120 : Nat := 118140960795 + 1814120 * 2 ^ 59
def prefixEnd_1814120 : Nat := 4983230072969 + 3 ^ 40 * 1814120 * 2
def baseEnd_1814120 : Nat := 414006899970909991492009

theorem tailTrace_1814120 : CollatzResearch.WordTrace tailWord_1814120 prefixEnd_1814120 414006899970909991492009 := by
  unfold tailWord_1814120
  simp only [CollatzResearch.WordTrace]
  refine ⟨33083196093880270937259907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44110928125173694583013209 33083196093880270937259907)
  ·
    refine ⟨49624794140820406405889861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33083196093880270937259907 49624794140820406405889861)
    ·
      refine ⟨9304648901403826201104349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49624794140820406405889861 9304648901403826201104349)
      ·
        refine ⟨3489243338026434825414131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9304648901403826201104349 3489243338026434825414131)
        ·
          refine ⟨5233865007039652238121197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489243338026434825414131 5233865007039652238121197)
          ·
            refine ⟨1962699377639869589295449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5233865007039652238121197 1962699377639869589295449)
            ·
              refine ⟨1472024533229902191971587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962699377639869589295449 1472024533229902191971587)
              ·
                refine ⟨2208036799844853287957381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472024533229902191971587 2208036799844853287957381)
                ·
                  refine ⟨414006899970909991492009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208036799844853287957381 414006899970909991492009)
                  ·
                    rfl

theorem cell21_1814120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_1814120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814120 prefixEnd_1814120 := by exact prefixLift 1814120
  have htrace : WordTrace (prefixWord ++ tailWord_1814120) baseStart_1814120 baseEnd_1814120 := by
    simpa [prefixWord, tailWord_1814120, baseEnd_1814120] using wordTrace_append hprefix tailTrace_1814120
  have hstable : (prefixWord ++ tailWord_1814120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814120).length < 2 ^ (prefixWord ++ tailWord_1814120).sum := by decide
  have hdescent : baseEnd_1814120 < baseStart_1814120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814176 : List Nat := [2, 1, 1, 4, 3, 1, 3, 6]
def baseStart_1814176 : Nat := 118140960795 + 1814176 * 2 ^ 59
def prefixEnd_1814176 : Nat := 4983230072969 + 3 ^ 40 * 1814176 * 2
def baseEnd_1814176 : Nat := 138006559977955446186187

theorem tailTrace_1814176 : CollatzResearch.WordTrace tailWord_1814176 prefixEnd_1814176 138006559977955446186187 := by
  unfold tailWord_1814176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084217337778831719279191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44112289783705108959038921 33084217337778831719279191)
  ·
    refine ⟨49626326006668247578918787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33084217337778831719279191 49626326006668247578918787)
    ·
      refine ⟨74439489010002371368378181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49626326006668247578918787 74439489010002371368378181)
      ·
        refine ⟨13957404189375444631570909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74439489010002371368378181 13957404189375444631570909)
        ·
          refine ⟨5234026571015791736839091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13957404189375444631570909 5234026571015791736839091)
          ·
            refine ⟨7851039856523687605258637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234026571015791736839091 7851039856523687605258637)
            ·
              refine ⟨2944139946196382851971989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7851039856523687605258637 2944139946196382851971989)
              ·
                refine ⟨138006559977955446186187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2944139946196382851971989 138006559977955446186187)
                ·
                  rfl

theorem cell21_1814176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_1814176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814176 prefixEnd_1814176 := by exact prefixLift 1814176
  have htrace : WordTrace (prefixWord ++ tailWord_1814176) baseStart_1814176 baseEnd_1814176 := by
    simpa [prefixWord, tailWord_1814176, baseEnd_1814176] using wordTrace_append hprefix tailTrace_1814176
  have hstable : (prefixWord ++ tailWord_1814176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814176).length < 2 ^ (prefixWord ++ tailWord_1814176).sum := by decide
  have hdescent : baseEnd_1814176 < baseStart_1814176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814252 : List Nat := [2, 2, 1, 1, 2, 2, 6, 5]
def baseStart_1814252 : Nat := 118140960795 + 1814252 * 2 ^ 59
def prefixEnd_1814252 : Nat := 4983230072969 + 3 ^ 40 * 1814252 * 2
def baseEnd_1814252 : Nat := 138012341389769031763913

theorem tailTrace_1814252 : CollatzResearch.WordTrace tailWord_1814252 prefixEnd_1814252 138012341389769031763913 := by
  unfold tailWord_1814252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33085603311641164209162505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44114137748854885612216673 33085603311641164209162505)
  ·
    refine ⟨24814202483730873156871879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33085603311641164209162505 24814202483730873156871879)
    ·
      refine ⟨37221303725596309735307819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24814202483730873156871879 37221303725596309735307819)
      ·
        refine ⟨55831955588394464602961729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37221303725596309735307819 55831955588394464602961729)
        ·
          refine ⟨41873966691295848452221297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55831955588394464602961729 41873966691295848452221297)
          ·
            refine ⟨31405475018471886339165973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41873966691295848452221297 31405475018471886339165973)
            ·
              refine ⟨1472131641490869672148405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31405475018471886339165973 1472131641490869672148405)
              ·
                refine ⟨138012341389769031763913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1472131641490869672148405 138012341389769031763913)
                ·
                  rfl

theorem cell21_1814252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_1814252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814252 prefixEnd_1814252 := by exact prefixLift 1814252
  have htrace : WordTrace (prefixWord ++ tailWord_1814252) baseStart_1814252 baseEnd_1814252 := by
    simpa [prefixWord, tailWord_1814252, baseEnd_1814252] using wordTrace_append hprefix tailTrace_1814252
  have hstable : (prefixWord ++ tailWord_1814252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814252).length < 2 ^ (prefixWord ++ tailWord_1814252).sum := by decide
  have hdescent : baseEnd_1814252 < baseStart_1814252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814283 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 3]
def baseStart_1814283 : Nat := 118140960795 + 1814283 * 2 ^ 59
def prefixEnd_1814283 : Nat := 4983230072969 + 3 ^ 40 * 1814283 * 2
def baseEnd_1814283 : Nat := 414044098791657930275009

theorem tailTrace_1814283 : CollatzResearch.WordTrace tailWord_1814283 prefixEnd_1814283 414044098791657930275009 := by
  unfold tailWord_1814283
  simp only [CollatzResearch.WordTrace]
  refine ⟨66172337286170020712703503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44114891524113347141802335 66172337286170020712703503)
  ·
    refine ⟨99258505929255031069055255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66172337286170020712703503 99258505929255031069055255)
    ·
      refine ⟨148887758893882546603582883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99258505929255031069055255 148887758893882546603582883)
      ·
        refine ⟨223331638340823819905374325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148887758893882546603582883 223331638340823819905374325)
        ·
          refine ⟨20937341094452233116128843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223331638340823819905374325 20937341094452233116128843)
          ·
            refine ⟨31406011641678349674193265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20937341094452233116128843 31406011641678349674193265)
            ·
              refine ⟨23554508731258762255644949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31406011641678349674193265 23554508731258762255644949)
              ·
                refine ⟨1104117596777754480733357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23554508731258762255644949 1104117596777754480733357)
                ·
                  refine ⟨414044098791657930275009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104117596777754480733357 414044098791657930275009)
                  ·
                    rfl

theorem cell21_1814283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 3].length) (baseStart_1814283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814283 prefixEnd_1814283 := by exact prefixLift 1814283
  have htrace : WordTrace (prefixWord ++ tailWord_1814283) baseStart_1814283 baseEnd_1814283 := by
    simpa [prefixWord, tailWord_1814283, baseEnd_1814283] using wordTrace_append hprefix tailTrace_1814283
  have hstable : (prefixWord ++ tailWord_1814283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814283).length < 2 ^ (prefixWord ++ tailWord_1814283).sum := by decide
  have hdescent : baseEnd_1814283 < baseStart_1814283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814334 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1814334 : Nat := 118140960795 + 1814334 * 2 ^ 59
def prefixEnd_1814334 : Nat := 4983230072969 + 3 ^ 40 * 1814334 * 2
def baseEnd_1814334 : Nat := 414055737686493174924905

theorem tailTrace_1814334 : CollatzResearch.WordTrace tailWord_1814334 prefixEnd_1814334 414055737686493174924905 := by
  unfold tailWord_1814334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271774676123157052851257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44116131605990170948540037 8271774676123157052851257)
  ·
    refine ⟨6203831007092367789638443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8271774676123157052851257 6203831007092367789638443)
    ·
      refine ⟨9305746510638551684457665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6203831007092367789638443 9305746510638551684457665)
      ·
        refine ⟨6979309882978913763343249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9305746510638551684457665 6979309882978913763343249)
        ·
          refine ⟨5234482412234185322507437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6979309882978913763343249 5234482412234185322507437)
          ·
            refine ⟨1962930904587819495940289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5234482412234185322507437 1962930904587819495940289)
            ·
              refine ⟨1472198178440864621955217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962930904587819495940289 1472198178440864621955217)
              ·
                refine ⟨1104148633830648466466413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472198178440864621955217 1104148633830648466466413)
                ·
                  refine ⟨414055737686493174924905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104148633830648466466413 414055737686493174924905)
                  ·
                    rfl

theorem cell21_1814334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1814334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814334 prefixEnd_1814334 := by exact prefixLift 1814334
  have htrace : WordTrace (prefixWord ++ tailWord_1814334) baseStart_1814334 baseEnd_1814334 := by
    simpa [prefixWord, tailWord_1814334, baseEnd_1814334] using wordTrace_append hprefix tailTrace_1814334
  have hstable : (prefixWord ++ tailWord_1814334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814334).length < 2 ^ (prefixWord ++ tailWord_1814334).sum := by decide
  have hdescent : baseEnd_1814334 < baseStart_1814334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814359 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_1814359 : Nat := 118140960795 + 1814359 * 2 ^ 59
def prefixEnd_1814359 : Nat := 4983230072969 + 3 ^ 40 * 1814359 * 2
def baseEnd_1814359 : Nat := 414061443027098687008187

theorem tailTrace_1814359 : CollatzResearch.WordTrace tailWord_1814359 prefixEnd_1814359 414061443027098687008187 := by
  unfold tailWord_1814359
  simp only [CollatzResearch.WordTrace]
  refine ⟨66175109233894685692470131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44116739489263123794980087 66175109233894685692470131)
  ·
    refine ⟨99262663850842028538705197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66175109233894685692470131 99262663850842028538705197)
    ·
      refine ⟨37223498944065760702014449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99262663850842028538705197 37223498944065760702014449)
      ·
        refine ⟨27917624208049320526510837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37223498944065760702014449 27917624208049320526510837)
        ·
          refine ⟨2617277269504623799360391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27917624208049320526510837 2617277269504623799360391)
          ·
            refine ⟨3925915904256935699040587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617277269504623799360391 3925915904256935699040587)
            ·
              refine ⟨5888873856385403548560881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925915904256935699040587 5888873856385403548560881)
              ·
                refine ⟨4416655392289052661420661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5888873856385403548560881 4416655392289052661420661)
                ·
                  refine ⟨414061443027098687008187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4416655392289052661420661 414061443027098687008187)
                  ·
                    rfl

theorem cell21_1814359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_1814359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814359 prefixEnd_1814359 := by exact prefixLift 1814359
  have htrace : WordTrace (prefixWord ++ tailWord_1814359) baseStart_1814359 baseEnd_1814359 := by
    simpa [prefixWord, tailWord_1814359, baseEnd_1814359] using wordTrace_append hprefix tailTrace_1814359
  have hstable : (prefixWord ++ tailWord_1814359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814359).length < 2 ^ (prefixWord ++ tailWord_1814359).sum := by decide
  have hdescent : baseEnd_1814359 < baseStart_1814359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814376 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_1814376 : Nat := 118140960795 + 1814376 * 2 ^ 59
def prefixEnd_1814376 : Nat := 4983230072969 + 3 ^ 40 * 1814376 * 2
def baseEnd_1814376 : Nat := 414065322658710435224819

theorem tailTrace_1814376 : CollatzResearch.WordTrace tailWord_1814376 prefixEnd_1814376 414065322658710435224819 := by
  unfold tailWord_1814376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33087864637416548797919491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44117152849888731730559321 33087864637416548797919491)
  ·
    refine ⟨49631796956124823196879237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33087864637416548797919491 49631796956124823196879237)
    ·
      refine ⟨9305961929273404349414857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49631796956124823196879237 9305961929273404349414857)
      ·
        refine ⟨6979471446955053262061143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9305961929273404349414857 6979471446955053262061143)
        ·
          refine ⟨10469207170432579893091715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979471446955053262061143 10469207170432579893091715)
          ·
            refine ⟨15703810755648869839637573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469207170432579893091715 15703810755648869839637573)
            ·
              refine ⟨2944464516684163094932045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15703810755648869839637573 2944464516684163094932045)
              ·
                refine ⟨1104174193756561160599517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2944464516684163094932045 1104174193756561160599517)
                ·
                  refine ⟨414065322658710435224819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104174193756561160599517 414065322658710435224819)
                  ·
                    rfl

theorem cell21_1814376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_1814376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814376 prefixEnd_1814376 := by exact prefixLift 1814376
  have htrace : WordTrace (prefixWord ++ tailWord_1814376) baseStart_1814376 baseEnd_1814376 := by
    simpa [prefixWord, tailWord_1814376, baseEnd_1814376] using wordTrace_append hprefix tailTrace_1814376
  have hstable : (prefixWord ++ tailWord_1814376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814376).length < 2 ^ (prefixWord ++ tailWord_1814376).sum := by decide
  have hdescent : baseEnd_1814376 < baseStart_1814376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814407 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 4]
def baseStart_1814407 : Nat := 118140960795 + 1814407 * 2 ^ 59
def prefixEnd_1814407 : Nat := 4983230072969 + 3 ^ 40 * 1814407 * 2
def baseEnd_1814407 : Nat := 414072397281061270208089

theorem tailTrace_1814407 : CollatzResearch.WordTrace tailWord_1814407 prefixEnd_1814407 414072397281061270208089 := by
  unfold tailWord_1814407
  simp only [CollatzResearch.WordTrace]
  refine ⟨66176859937720789890217475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44117906625147193260144983 66176859937720789890217475)
  ·
    refine ⟨99265289906581184835326213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66176859937720789890217475 99265289906581184835326213)
    ·
      refine ⟨18612241857483972156623665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99265289906581184835326213 18612241857483972156623665)
      ·
        refine ⟨13959181393112979117467749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18612241857483972156623665 13959181393112979117467749)
        ·
          refine ⟨2617346511208683584525203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13959181393112979117467749 2617346511208683584525203)
          ·
            refine ⟨3926019766813025376787805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617346511208683584525203 3926019766813025376787805)
            ·
              refine ⟨1472257412554884516295427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3926019766813025376787805 1472257412554884516295427)
              ·
                refine ⟨2208386118832326774443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472257412554884516295427 2208386118832326774443141)
                ·
                  refine ⟨414072397281061270208089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208386118832326774443141 414072397281061270208089)
                  ·
                    rfl

theorem cell21_1814407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4].length) (baseStart_1814407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814407 prefixEnd_1814407 := by exact prefixLift 1814407
  have htrace : WordTrace (prefixWord ++ tailWord_1814407) baseStart_1814407 baseEnd_1814407 := by
    simpa [prefixWord, tailWord_1814407, baseEnd_1814407] using wordTrace_append hprefix tailTrace_1814407
  have hstable : (prefixWord ++ tailWord_1814407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814407).length < 2 ^ (prefixWord ++ tailWord_1814407).sum := by decide
  have hdescent : baseEnd_1814407 < baseStart_1814407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814449 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_1814449 : Nat := 118140960795 + 1814449 * 2 ^ 59
def prefixEnd_1814449 : Nat := 4983230072969 + 3 ^ 40 * 1814449 * 2
def baseEnd_1814449 : Nat := 414081982253278530508003

theorem tailTrace_1814449 : CollatzResearch.WordTrace tailWord_1814449 prefixEnd_1814449 414081982253278530508003 := by
  unfold tailWord_1814449
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178391803568631063246401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44118927869045754042164267 66178391803568631063246401)
  ·
    refine ⟨49633793852676473297434801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66178391803568631063246401 49633793852676473297434801)
    ·
      refine ⟨37225345389507354973076101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49633793852676473297434801 37225345389507354973076101)
      ·
        refine ⟨6979752260532629057451769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37225345389507354973076101 6979752260532629057451769)
        ·
          refine ⟨5234814195399471793088827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6979752260532629057451769 5234814195399471793088827)
          ·
            refine ⟨7852221293099207689633241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234814195399471793088827 7852221293099207689633241)
            ·
              refine ⟨5889165969824405767224931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852221293099207689633241 5889165969824405767224931)
              ·
                refine ⟨8833748954736608650837397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889165969824405767224931 8833748954736608650837397)
                ·
                  refine ⟨414081982253278530508003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8833748954736608650837397 414081982253278530508003)
                  ·
                    rfl

theorem cell21_1814449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_1814449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814449 prefixEnd_1814449 := by exact prefixLift 1814449
  have htrace : WordTrace (prefixWord ++ tailWord_1814449) baseStart_1814449 baseEnd_1814449 := by
    simpa [prefixWord, tailWord_1814449, baseEnd_1814449] using wordTrace_append hprefix tailTrace_1814449
  have hstable : (prefixWord ++ tailWord_1814449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814449).length < 2 ^ (prefixWord ++ tailWord_1814449).sum := by decide
  have hdescent : baseEnd_1814449 < baseStart_1814449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814463 : List Nat := [1, 1, 2, 2, 2, 1, 6, 6]
def baseStart_1814463 : Nat := 118140960795 + 1814463 * 2 ^ 59
def prefixEnd_1814463 : Nat := 4983230072969 + 3 ^ 40 * 1814463 * 2
def baseEnd_1814463 : Nat := 138028392414672539091547

theorem tailTrace_1814463 : CollatzResearch.WordTrace tailWord_1814463 prefixEnd_1814463 138028392414672539091547 := by
  unfold tailWord_1814463
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178902425517911454256043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44119268283678607636170695 66178902425517911454256043)
  ·
    refine ⟨99268353638276867181384065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66178902425517911454256043 99268353638276867181384065)
    ·
      refine ⟨74451265228707650386038049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99268353638276867181384065 74451265228707650386038049)
      ·
        refine ⟨55838448921530737789528537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74451265228707650386038049 55838448921530737789528537)
        ·
          refine ⟨41878836691148053342146403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55838448921530737789528537 41878836691148053342146403)
          ·
            refine ⟨62818255036722080013219605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41878836691148053342146403 62818255036722080013219605)
            ·
              refine ⟨2944605704846347500619669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62818255036722080013219605 2944605704846347500619669)
              ·
                refine ⟨138028392414672539091547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2944605704846347500619669 138028392414672539091547)
                ·
                  rfl

theorem cell21_1814463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_1814463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814463 prefixEnd_1814463 := by exact prefixLift 1814463
  have htrace : WordTrace (prefixWord ++ tailWord_1814463) baseStart_1814463 baseEnd_1814463 := by
    simpa [prefixWord, tailWord_1814463, baseEnd_1814463] using wordTrace_append hprefix tailTrace_1814463
  have hstable : (prefixWord ++ tailWord_1814463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814463).length < 2 ^ (prefixWord ++ tailWord_1814463).sum := by decide
  have hdescent : baseEnd_1814463 < baseStart_1814463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814508 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_1814508 : Nat := 118140960795 + 1814508 * 2 ^ 59
def prefixEnd_1814508 : Nat := 4983230072969 + 3 ^ 40 * 1814508 * 2
def baseEnd_1814508 : Nat := 414095446857107539024549

theorem tailTrace_1814508 : CollatzResearch.WordTrace tailWord_1814508 prefixEnd_1814508 414095446857107539024549 := by
  unfold tailWord_1814508
  simp only [CollatzResearch.WordTrace]
  refine ⟨33090271855177442069822089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44120362473569922759762785 33090271855177442069822089)
  ·
    refine ⟨24817703891383081552366567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33090271855177442069822089 24817703891383081552366567)
    ·
      refine ⟨37226555837074622328549851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24817703891383081552366567 37226555837074622328549851)
      ·
        refine ⟨55839833755611933492824777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37226555837074622328549851 55839833755611933492824777)
        ·
          refine ⟨41879875316708950119618583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55839833755611933492824777 41879875316708950119618583)
          ·
            refine ⟨62819812975063425179427875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41879875316708950119618583 62819812975063425179427875)
            ·
              refine ⟨94229719462595137769141813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62819812975063425179427875 94229719462595137769141813)
              ·
                refine ⟨8834036199618294165857045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94229719462595137769141813 8834036199618294165857045)
                ·
                  refine ⟨414095446857107539024549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8834036199618294165857045 414095446857107539024549)
                  ·
                    rfl

theorem cell21_1814508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_1814508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814508 prefixEnd_1814508 := by exact prefixLift 1814508
  have htrace : WordTrace (prefixWord ++ tailWord_1814508) baseStart_1814508 baseEnd_1814508 := by
    simpa [prefixWord, tailWord_1814508, baseEnd_1814508] using wordTrace_append hprefix tailTrace_1814508
  have hstable : (prefixWord ++ tailWord_1814508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814508).length < 2 ^ (prefixWord ++ tailWord_1814508).sum := by decide
  have hdescent : baseEnd_1814508 < baseStart_1814508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814511 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 3]
def baseStart_1814511 : Nat := 118140960795 + 1814511 * 2 ^ 59
def prefixEnd_1814511 : Nat := 4983230072969 + 3 ^ 40 * 1814511 * 2
def baseEnd_1814511 : Nat := 414096131497980200474543

theorem tailTrace_1814511 : CollatzResearch.WordTrace tailWord_1814511 prefixEnd_1814511 414096131497980200474543 := by
  unfold tailWord_1814511
  simp only [CollatzResearch.WordTrace]
  refine ⟨66180653129344015652003387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44120435419562677101335591 66180653129344015652003387)
  ·
    refine ⟨99270979694016023478005081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66180653129344015652003387 99270979694016023478005081)
    ·
      refine ⟨74453234770512017608503811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99270979694016023478005081 74453234770512017608503811)
      ·
        refine ⟨111679852155768026412755717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74453234770512017608503811 111679852155768026412755717)
        ·
          refine ⟨20939972279206504952391697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111679852155768026412755717 20939972279206504952391697)
          ·
            refine ⟨15704979209404878714293773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20939972279206504952391697 15704979209404878714293773)
            ·
              refine ⟨5889367203526829517860165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15704979209404878714293773 5889367203526829517860165)
              ·
                refine ⟨1104256350661280534598781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5889367203526829517860165 1104256350661280534598781)
                ·
                  refine ⟨414096131497980200474543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104256350661280534598781 414096131497980200474543)
                  ·
                    rfl

theorem cell21_1814511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3].length) (baseStart_1814511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814511 prefixEnd_1814511 := by exact prefixLift 1814511
  have htrace : WordTrace (prefixWord ++ tailWord_1814511) baseStart_1814511 baseEnd_1814511 := by
    simpa [prefixWord, tailWord_1814511, baseEnd_1814511] using wordTrace_append hprefix tailTrace_1814511
  have hstable : (prefixWord ++ tailWord_1814511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814511).length < 2 ^ (prefixWord ++ tailWord_1814511).sum := by decide
  have hdescent : baseEnd_1814511 < baseStart_1814511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814525 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1814525 : Nat := 118140960795 + 1814525 * 2 ^ 59
def prefixEnd_1814525 : Nat := 4983230072969 + 3 ^ 40 * 1814525 * 2
def baseEnd_1814525 : Nat := 414099326488719287241181

theorem tailTrace_1814525 : CollatzResearch.WordTrace tailWord_1814525 prefixEnd_1814525 414099326488719287241181 := by
  unfold tailWord_1814525
  simp only [CollatzResearch.WordTrace]
  refine ⟨66181163751293296043013029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44120775834195530695342019 66181163751293296043013029)
  ·
    refine ⟨12408968203367493008064943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66181163751293296043013029 12408968203367493008064943)
    ·
      refine ⟨18613452305051239512097415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12408968203367493008064943 18613452305051239512097415)
      ·
        refine ⟨27920178457576859268146123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18613452305051239512097415 27920178457576859268146123)
        ·
          refine ⟨41880267686365288902219185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27920178457576859268146123 41880267686365288902219185)
          ·
            refine ⟨31410200764773966676664389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41880267686365288902219185 31410200764773966676664389)
            ·
              refine ⟨5889412643395118751874573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31410200764773966676664389 5889412643395118751874573)
              ·
                refine ⟨2208529741273169531952965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889412643395118751874573 2208529741273169531952965)
                ·
                  refine ⟨414099326488719287241181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208529741273169531952965 414099326488719287241181)
                  ·
                    rfl

theorem cell21_1814525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1814525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814525 prefixEnd_1814525 := by exact prefixLift 1814525
  have htrace : WordTrace (prefixWord ++ tailWord_1814525) baseStart_1814525 baseEnd_1814525 := by
    simpa [prefixWord, tailWord_1814525, baseEnd_1814525] using wordTrace_append hprefix tailTrace_1814525
  have hstable : (prefixWord ++ tailWord_1814525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814525).length < 2 ^ (prefixWord ++ tailWord_1814525).sum := by decide
  have hdescent : baseEnd_1814525 < baseStart_1814525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814553 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_1814553 : Nat := 118140960795 + 1814553 * 2 ^ 59
def prefixEnd_1814553 : Nat := 4983230072969 + 3 ^ 40 * 1814553 * 2
def baseEnd_1814553 : Nat := 414105716470197460774457

theorem tailTrace_1814553 : CollatzResearch.WordTrace tailWord_1814553 prefixEnd_1814553 414105716470197460774457 := by
  unfold tailWord_1814553
  simp only [CollatzResearch.WordTrace]
  refine ⟨66182184995191856825032313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44121456663461237883354875 66182184995191856825032313)
  ·
    refine ⟨49636638746393892618774235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66182184995191856825032313 49636638746393892618774235)
    ·
      refine ⟨74454958119590838928161353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49636638746393892618774235 74454958119590838928161353)
      ·
        refine ⟨55841218589693129196121015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74454958119590838928161353 55841218589693129196121015)
        ·
          refine ⟨83761827884539693794181523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55841218589693129196121015 83761827884539693794181523)
          ·
            refine ⟨125642741826809540691272285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83761827884539693794181523 125642741826809540691272285)
            ·
              refine ⟨47116028185053577759227107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125642741826809540691272285 47116028185053577759227107)
              ·
                refine ⟨70674042277580366638840661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47116028185053577759227107 70674042277580366638840661)
                ·
                  refine ⟨414105716470197460774457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70674042277580366638840661 414105716470197460774457)
                  ·
                    rfl

theorem cell21_1814553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_1814553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814553 prefixEnd_1814553 := by exact prefixLift 1814553
  have htrace : WordTrace (prefixWord ++ tailWord_1814553) baseStart_1814553 baseEnd_1814553 := by
    simpa [prefixWord, tailWord_1814553, baseEnd_1814553] using wordTrace_append hprefix tailTrace_1814553
  have hstable : (prefixWord ++ tailWord_1814553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814553).length < 2 ^ (prefixWord ++ tailWord_1814553).sum := by decide
  have hdescent : baseEnd_1814553 < baseStart_1814553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814590 : List Nat := [4, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1814590 : Nat := 118140960795 + 1814590 * 2 ^ 59
def prefixEnd_1814590 : Nat := 4983230072969 + 3 ^ 40 * 1814590 * 2
def baseEnd_1814590 : Nat := 138038053458097872885905

theorem tailTrace_1814590 : CollatzResearch.WordTrace tailWord_1814590 prefixEnd_1814590 138038053458097872885905 := by
  unfold tailWord_1814590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272941812007226518016153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44122356330705208096086149 8272941812007226518016153)
  ·
    refine ⟨6204706359005419888512115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8272941812007226518016153 6204706359005419888512115)
    ·
      refine ⟨9307059538508129832768173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6204706359005419888512115 9307059538508129832768173)
      ·
        refine ⟨3490147326940548687288065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9307059538508129832768173 3490147326940548687288065)
        ·
          refine ⟨2617610495205411515466049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3490147326940548687288065 2617610495205411515466049)
          ·
            refine ⟨1963207871404058636599537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2617610495205411515466049 1963207871404058636599537)
            ·
              refine ⟨1472405903553043977449653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963207871404058636599537 1472405903553043977449653)
              ·
                refine ⟨138038053458097872885905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1472405903553043977449653 138038053458097872885905)
                ·
                  rfl

theorem cell21_1814590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1814590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814590 prefixEnd_1814590 := by exact prefixLift 1814590
  have htrace : WordTrace (prefixWord ++ tailWord_1814590) baseStart_1814590 baseEnd_1814590 := by
    simpa [prefixWord, tailWord_1814590, baseEnd_1814590] using wordTrace_append hprefix tailTrace_1814590
  have hstable : (prefixWord ++ tailWord_1814590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814590).length < 2 ^ (prefixWord ++ tailWord_1814590).sum := by decide
  have hdescent : baseEnd_1814590 < baseStart_1814590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814677 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_1814677 : Nat := 118140960795 + 1814677 * 2 ^ 59
def prefixEnd_1814677 : Nat := 4983230072969 + 3 ^ 40 * 1814677 * 2
def baseEnd_1814677 : Nat := 414134014959600800707537

theorem tailTrace_1814677 : CollatzResearch.WordTrace tailWord_1814677 prefixEnd_1814677 414134014959600800707537 := by
  unfold tailWord_1814677
  simp only [CollatzResearch.WordTrace]
  refine ⟨66186707646742626002546285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44124471764495084001697523 66186707646742626002546285)
  ·
    refine ⟨24820015367528484750954857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66186707646742626002546285 24820015367528484750954857)
    ·
      refine ⟨18615011525646363563216143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24820015367528484750954857 18615011525646363563216143)
      ·
        refine ⟨27922517288469545344824215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18615011525646363563216143 27922517288469545344824215)
        ·
          refine ⟨41883775932704318017236323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27922517288469545344824215 41883775932704318017236323)
          ·
            refine ⟨62825663899056477025854485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41883775932704318017236323 62825663899056477025854485)
            ·
              refine ⟨2944952995268272360586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62825663899056477025854485 2944952995268272360586929)
              ·
                refine ⟨2208714746451204270440197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944952995268272360586929 2208714746451204270440197)
                ·
                  refine ⟨414134014959600800707537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208714746451204270440197 414134014959600800707537)
                  ·
                    rfl

theorem cell21_1814677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_1814677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814677 prefixEnd_1814677 := by exact prefixLift 1814677
  have htrace : WordTrace (prefixWord ++ tailWord_1814677) baseStart_1814677 baseEnd_1814677 := by
    simpa [prefixWord, tailWord_1814677, baseEnd_1814677] using wordTrace_append hprefix tailTrace_1814677
  have hstable : (prefixWord ++ tailWord_1814677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814677).length < 2 ^ (prefixWord ++ tailWord_1814677).sum := by decide
  have hdescent : baseEnd_1814677 < baseStart_1814677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814680 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_1814680 : Nat := 118140960795 + 1814680 * 2 ^ 59
def prefixEnd_1814680 : Nat := 4983230072969 + 3 ^ 40 * 1814680 * 2
def baseEnd_1814680 : Nat := 414134699600473462157531

theorem tailTrace_1814680 : CollatzResearch.WordTrace tailWord_1814680 prefixEnd_1814680 414134699600473462157531 := by
  unfold tailWord_1814680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33093408532865878757452747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44124544710487838343270329 33093408532865878757452747)
  ·
    refine ⟨49640112799298818136179121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33093408532865878757452747 49640112799298818136179121)
    ·
      refine ⟨37230084599474113602134341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49640112799298818136179121 37230084599474113602134341)
      ·
        refine ⟨6980640862401396300400189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37230084599474113602134341 6980640862401396300400189)
        ·
          refine ⟨2617740323400523612650071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6980640862401396300400189 2617740323400523612650071)
          ·
            refine ⟨3926610485100785418975107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617740323400523612650071 3926610485100785418975107)
            ·
              refine ⟨5889915727651178128462661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926610485100785418975107 5889915727651178128462661)
              ·
                refine ⟨1104359198934595899086749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5889915727651178128462661 1104359198934595899086749)
                ·
                  refine ⟨414134699600473462157531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104359198934595899086749 414134699600473462157531)
                  ·
                    rfl

theorem cell21_1814680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_1814680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814680 prefixEnd_1814680 := by exact prefixLift 1814680
  have htrace : WordTrace (prefixWord ++ tailWord_1814680) baseStart_1814680 baseEnd_1814680 := by
    simpa [prefixWord, tailWord_1814680, baseEnd_1814680] using wordTrace_append hprefix tailTrace_1814680
  have hstable : (prefixWord ++ tailWord_1814680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814680).length < 2 ^ (prefixWord ++ tailWord_1814680).sum := by decide
  have hdescent : baseEnd_1814680 < baseStart_1814680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814767 : List Nat := [1, 1, 2, 1, 6, 2, 1, 7]
def baseStart_1814767 : Nat := 118140960795 + 1814767 * 2 ^ 59
def prefixEnd_1814767 : Nat := 4983230072969 + 3 ^ 40 * 1814767 * 2
def baseEnd_1814767 : Nat := 138051518061926881402451

theorem tailTrace_1814767 : CollatzResearch.WordTrace tailWord_1814767 prefixEnd_1814767 138051518061926881402451 := by
  unfold tailWord_1814767
  simp only [CollatzResearch.WordTrace]
  refine ⟨66189990216416571373322555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44126660144277714248881703 66189990216416571373322555)
  ·
    refine ⟨99284985324624857059983833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66189990216416571373322555 99284985324624857059983833)
    ·
      refine ⟨74463738993468642794987875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99284985324624857059983833 74463738993468642794987875)
      ·
        refine ⟨111695608490202964192481813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74463738993468642794987875 111695608490202964192481813)
        ·
          refine ⟨5235731647978263946522585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111695608490202964192481813 5235731647978263946522585)
          ·
            refine ⟨3926798735983697959891939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5235731647978263946522585 3926798735983697959891939)
            ·
              refine ⟨5890198103975546939837909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926798735983697959891939 5890198103975546939837909)
              ·
                refine ⟨138051518061926881402451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5890198103975546939837909 138051518061926881402451)
                ·
                  rfl

theorem cell21_1814767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_1814767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814767 prefixEnd_1814767 := by exact prefixLift 1814767
  have htrace : WordTrace (prefixWord ++ tailWord_1814767) baseStart_1814767 baseEnd_1814767 := by
    simpa [prefixWord, tailWord_1814767, baseEnd_1814767] using wordTrace_append hprefix tailTrace_1814767
  have hstable : (prefixWord ++ tailWord_1814767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814767).length < 2 ^ (prefixWord ++ tailWord_1814767).sum := by decide
  have hdescent : baseEnd_1814767 < baseStart_1814767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814781 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1814781 : Nat := 118140960795 + 1814781 * 2 ^ 59
def prefixEnd_1814781 : Nat := 4983230072969 + 3 ^ 40 * 1814781 * 2
def baseEnd_1814781 : Nat := 414157749176519730973991

theorem tailTrace_1814781 : CollatzResearch.WordTrace tailWord_1814781 prefixEnd_1814781 414157749176519730973991 := by
  unfold tailWord_1814781
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190500838365851764332197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44127000558910567842888131 66190500838365851764332197)
  ·
    refine ⟨12410718907193597205812287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66190500838365851764332197 12410718907193597205812287)
    ·
      refine ⟨18616078360790395808718431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12410718907193597205812287 18616078360790395808718431)
      ·
        refine ⟨27924117541185593713077647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18616078360790395808718431 27924117541185593713077647)
        ·
          refine ⟨41886176311778390569616471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27924117541185593713077647 41886176311778390569616471)
          ·
            refine ⟨62829264467667585854424707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41886176311778390569616471 62829264467667585854424707)
            ·
              refine ⟨94243896701501378781637061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62829264467667585854424707 94243896701501378781637061)
              ·
                refine ⟨17670730631531508521556949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94243896701501378781637061 17670730631531508521556949)
                ·
                  refine ⟨414157749176519730973991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17670730631531508521556949 414157749176519730973991)
                  ·
                    rfl

theorem cell21_1814781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1814781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814781 prefixEnd_1814781 := by exact prefixLift 1814781
  have htrace : WordTrace (prefixWord ++ tailWord_1814781) baseStart_1814781 baseEnd_1814781 := by
    simpa [prefixWord, tailWord_1814781, baseEnd_1814781] using wordTrace_append hprefix tailTrace_1814781
  have hstable : (prefixWord ++ tailWord_1814781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814781).length < 2 ^ (prefixWord ++ tailWord_1814781).sum := by decide
  have hdescent : baseEnd_1814781 < baseStart_1814781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814846 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1814846 : Nat := 118140960795 + 1814846 * 2 ^ 59
def prefixEnd_1814846 : Nat := 4983230072969 + 3 ^ 40 * 1814846 * 2
def baseEnd_1814846 : Nat := 414172583062094062390525

theorem tailTrace_1814846 : CollatzResearch.WordTrace tailWord_1814846 prefixEnd_1814846 414172583062094062390525 := by
  unfold tailWord_1814846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8274108947891295983181049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44128581055420245243632261 8274108947891295983181049)
  ·
    refine ⟨6205581710918471987385787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8274108947891295983181049 6205581710918471987385787)
    ·
      refine ⟨9308372566377707981078681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205581710918471987385787 9308372566377707981078681)
      ·
        refine ⟨6981279424783280985809011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9308372566377707981078681 6981279424783280985809011)
        ·
          refine ⟨10471919137174921478713517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981279424783280985809011 10471919137174921478713517)
          ·
            refine ⟨3926969676440595554517569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10471919137174921478713517 3926969676440595554517569)
            ·
              refine ⟨2945227257330446665888177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926969676440595554517569 2945227257330446665888177)
              ·
                refine ⟨2208920442997834999416133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945227257330446665888177 2208920442997834999416133)
                ·
                  refine ⟨414172583062094062390525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208920442997834999416133 414172583062094062390525)
                  ·
                    rfl

theorem cell21_1814846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1814846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814846 prefixEnd_1814846 := by exact prefixLift 1814846
  have htrace : WordTrace (prefixWord ++ tailWord_1814846) baseStart_1814846 baseEnd_1814846 := by
    simpa [prefixWord, tailWord_1814846, baseEnd_1814846] using wordTrace_append hprefix tailTrace_1814846
  have hstable : (prefixWord ++ tailWord_1814846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814846).length < 2 ^ (prefixWord ++ tailWord_1814846).sum := by decide
  have hdescent : baseEnd_1814846 < baseStart_1814846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814857 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_1814857 : Nat := 118140960795 + 1814857 * 2 ^ 59
def prefixEnd_1814857 : Nat := 4983230072969 + 3 ^ 40 * 1814857 * 2
def baseEnd_1814857 : Nat := 414175093411960487707169

theorem tailTrace_1814857 : CollatzResearch.WordTrace tailWord_1814857 prefixEnd_1814857 414175093411960487707169 := by
  unfold tailWord_1814857
  simp only [CollatzResearch.WordTrace]
  refine ⟨66193272786090516744098825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44128848524060344496065883 66193272786090516744098825)
  ·
    refine ⟨49644954589567887558074119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66193272786090516744098825 49644954589567887558074119)
    ·
      refine ⟨74467431884351831337111179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49644954589567887558074119 74467431884351831337111179)
      ·
        refine ⟨111701147826527747005666769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74467431884351831337111179 111701147826527747005666769)
        ·
          refine ⟨83775860869895810254250077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111701147826527747005666769 83775860869895810254250077)
          ·
            refine ⟨31415947826210928845343779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83775860869895810254250077 31415947826210928845343779)
            ·
              refine ⟨47123921739316393268015669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31415947826210928845343779 47123921739316393268015669)
              ·
                refine ⟨4417867663060911868876469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47123921739316393268015669 4417867663060911868876469)
                ·
                  refine ⟨414175093411960487707169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4417867663060911868876469 414175093411960487707169)
                  ·
                    rfl

theorem cell21_1814857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_1814857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814857 prefixEnd_1814857 := by exact prefixLift 1814857
  have htrace : WordTrace (prefixWord ++ tailWord_1814857) baseStart_1814857 baseEnd_1814857 := by
    simpa [prefixWord, tailWord_1814857, baseEnd_1814857] using wordTrace_append hprefix tailTrace_1814857
  have hstable : (prefixWord ++ tailWord_1814857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814857).length < 2 ^ (prefixWord ++ tailWord_1814857).sum := by decide
  have hdescent : baseEnd_1814857 < baseStart_1814857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814936 : List Nat := [2, 1, 2, 5, 1, 1, 4, 5]
def baseStart_1814936 : Nat := 118140960795 + 1814936 * 2 ^ 59
def prefixEnd_1814936 : Nat := 4983230072969 + 3 ^ 40 * 1814936 * 2
def baseEnd_1814936 : Nat := 138064374096091301963447

theorem tailTrace_1814936 : CollatzResearch.WordTrace tailWord_1814936 prefixEnd_1814936 138064374096091301963447 := by
  unfold tailWord_1814936
  simp only [CollatzResearch.WordTrace]
  refine ⟨33098077076402156618112331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44130769435202875490816441 33098077076402156618112331)
  ·
    refine ⟨49647115614603234927168497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33098077076402156618112331 49647115614603234927168497)
    ·
      refine ⟨37235336710952426195376373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49647115614603234927168497 37235336710952426195376373)
      ·
        refine ⟨3490812816651789955816535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37235336710952426195376373 3490812816651789955816535)
        ·
          refine ⟨5236219224977684933724803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490812816651789955816535 5236219224977684933724803)
          ·
            refine ⟨7854328837466527400587205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236219224977684933724803 7854328837466527400587205)
            ·
              refine ⟨1472686657024973887610101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7854328837466527400587205 1472686657024973887610101)
              ·
                refine ⟨138064374096091301963447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1472686657024973887610101 138064374096091301963447)
                ·
                  rfl

theorem cell21_1814936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_1814936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1814936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1814936 prefixEnd_1814936 := by exact prefixLift 1814936
  have htrace : WordTrace (prefixWord ++ tailWord_1814936) baseStart_1814936 baseEnd_1814936 := by
    simpa [prefixWord, tailWord_1814936, baseEnd_1814936] using wordTrace_append hprefix tailTrace_1814936
  have hstable : (prefixWord ++ tailWord_1814936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814936).length < 2 ^ (prefixWord ++ tailWord_1814936).sum := by decide
  have hdescent : baseEnd_1814936 < baseStart_1814936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815029 : List Nat := [1, 3, 5, 1, 2, 2, 1, 6]
def baseStart_1815029 : Nat := 118140960795 + 1815029 * 2 ^ 59
def prefixEnd_1815029 : Nat := 4983230072969 + 3 ^ 40 * 1815029 * 2
def baseEnd_1815029 : Nat := 138071448718442136946717

theorem tailTrace_1815029 : CollatzResearch.WordTrace tailWord_1815029 prefixEnd_1815029 138071448718442136946717 := by
  unfold tailWord_1815029
  simp only [CollatzResearch.WordTrace]
  refine ⟨66199546141467390119360141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44133030760978260079573427 66199546141467390119360141)
  ·
    refine ⟨24824829803050271294760053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66199546141467390119360141 24824829803050271294760053)
    ·
      refine ⟨2327327794035962933883755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24824829803050271294760053 2327327794035962933883755)
      ·
        refine ⟨3490991691053944400825633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327327794035962933883755 3490991691053944400825633)
        ·
          refine ⟨2618243768290458300619225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3490991691053944400825633 2618243768290458300619225)
          ·
            refine ⟨1963682826217843725464419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618243768290458300619225 1963682826217843725464419)
            ·
              refine ⟨2945524239326765588196629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963682826217843725464419 2945524239326765588196629)
              ·
                refine ⟨138071448718442136946717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2945524239326765588196629 138071448718442136946717)
                ·
                  rfl

theorem cell21_1815029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 6].length) (baseStart_1815029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815029 prefixEnd_1815029 := by exact prefixLift 1815029
  have htrace : WordTrace (prefixWord ++ tailWord_1815029) baseStart_1815029 baseEnd_1815029 := by
    simpa [prefixWord, tailWord_1815029, baseEnd_1815029] using wordTrace_append hprefix tailTrace_1815029
  have hstable : (prefixWord ++ tailWord_1815029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815029).length < 2 ^ (prefixWord ++ tailWord_1815029).sum := by decide
  have hdescent : baseEnd_1815029 < baseStart_1815029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815060 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1815060 : Nat := 118140960795 + 1815060 * 2 ^ 59
def prefixEnd_1815060 : Nat := 4983230072969 + 3 ^ 40 * 1815060 * 2
def baseEnd_1815060 : Nat := 414221420777677245823421

theorem tailTrace_1815060 : CollatzResearch.WordTrace tailWord_1815060 prefixEnd_1815060 414221420777677245823421 := by
  unfold tailWord_1815060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33100338402177541206869317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44133784536236721609159089 33100338402177541206869317)
  ·
    refine ⟨6206313450408288976287997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33100338402177541206869317 6206313450408288976287997)
    ·
      refine ⟨2327367543903108366107999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6206313450408288976287997 2327367543903108366107999)
      ·
        refine ⟨3491051315854662549161999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327367543903108366107999 3491051315854662549161999)
        ·
          refine ⟨5236576973781993823742999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491051315854662549161999 5236576973781993823742999)
          ·
            refine ⟨7854865460672990735614499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236576973781993823742999 7854865460672990735614499)
            ·
              refine ⟨11782298191009486103421749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854865460672990735614499 11782298191009486103421749)
              ·
                refine ⟨1104590455407139322195789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11782298191009486103421749 1104590455407139322195789)
                ·
                  refine ⟨414221420777677245823421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104590455407139322195789 414221420777677245823421)
                  ·
                    rfl

theorem cell21_1815060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1815060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815060 prefixEnd_1815060 := by exact prefixLift 1815060
  have htrace : WordTrace (prefixWord ++ tailWord_1815060) baseStart_1815060 baseEnd_1815060 := by
    simpa [prefixWord, tailWord_1815060, baseEnd_1815060] using wordTrace_append hprefix tailTrace_1815060
  have hstable : (prefixWord ++ tailWord_1815060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815060).length < 2 ^ (prefixWord ++ tailWord_1815060).sum := by decide
  have hdescent : baseEnd_1815060 < baseStart_1815060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815150 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1815150 : Nat := 118140960795 + 1815150 * 2 ^ 59
def prefixEnd_1815150 : Nat := 4983230072969 + 3 ^ 40 * 1815150 * 2
def baseEnd_1815150 : Nat := 414241960003857089323237

theorem tailTrace_1815150 : CollatzResearch.WordTrace tailWord_1815150 prefixEnd_1815150 414241960003857089323237 := by
  unfold tailWord_1815150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275494921753628473064363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44135972916019351856343269 8275494921753628473064363)
  ·
    refine ⟨12413242382630442709596545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8275494921753628473064363 12413242382630442709596545)
    ·
      refine ⟨9309931786972832032197409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12413242382630442709596545 9309931786972832032197409)
      ·
        refine ⟨6982448840229624024148057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9309931786972832032197409 6982448840229624024148057)
        ·
          refine ⟨5236836630172218018111043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6982448840229624024148057 5236836630172218018111043)
          ·
            refine ⟨7855254945258327027166565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236836630172218018111043 7855254945258327027166565)
            ·
              refine ⟨1472860302235936317593731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7855254945258327027166565 1472860302235936317593731)
              ·
                refine ⟨2209290453353904476390597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472860302235936317593731 2209290453353904476390597)
                ·
                  refine ⟨414241960003857089323237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209290453353904476390597 414241960003857089323237)
                  ·
                    rfl

theorem cell21_1815150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1815150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815150 prefixEnd_1815150 := by exact prefixLift 1815150
  have htrace : WordTrace (prefixWord ++ tailWord_1815150) baseStart_1815150 baseEnd_1815150 := by
    simpa [prefixWord, tailWord_1815150, baseEnd_1815150] using wordTrace_append hprefix tailTrace_1815150
  have hstable : (prefixWord ++ tailWord_1815150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815150).length < 2 ^ (prefixWord ++ tailWord_1815150).sum := by decide
  have hdescent : baseEnd_1815150 < baseStart_1815150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815313 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_1815313 : Nat := 118140960795 + 1815313 * 2 ^ 59
def prefixEnd_1815313 : Nat := 4983230072969 + 3 ^ 40 * 1815313 * 2
def baseEnd_1815313 : Nat := 414279158824605028106237

theorem tailTrace_1815313 : CollatzResearch.WordTrace tailWord_1815313 prefixEnd_1815313 414279158824605028106237 := by
  unfold tailWord_1815313
  simp only [CollatzResearch.WordTrace]
  refine ⟨66209904472438506622698593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44139936314959004415132395 66209904472438506622698593)
  ·
    refine ⟨49657428354328879967023945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66209904472438506622698593 49657428354328879967023945)
    ·
      refine ⟨37243071265746659975267959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49657428354328879967023945 37243071265746659975267959)
      ·
        refine ⟨55864606898619989962901939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37243071265746659975267959 55864606898619989962901939)
        ·
          refine ⟨83796910347929984944352909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55864606898619989962901939 83796910347929984944352909)
          ·
            refine ⟨31423841380473744354132341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83796910347929984944352909 31423841380473744354132341)
            ·
              refine ⟨2945985129419413533199907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31423841380473744354132341 2945985129419413533199907)
              ·
                refine ⟨4418977694129120299799861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945985129419413533199907 4418977694129120299799861)
                ·
                  refine ⟨414279158824605028106237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4418977694129120299799861 414279158824605028106237)
                  ·
                    rfl

theorem cell21_1815313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_1815313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815313 prefixEnd_1815313 := by exact prefixLift 1815313
  have htrace : WordTrace (prefixWord ++ tailWord_1815313) baseStart_1815313 baseEnd_1815313 := by
    simpa [prefixWord, tailWord_1815313, baseEnd_1815313] using wordTrace_append hprefix tailTrace_1815313
  have hstable : (prefixWord ++ tailWord_1815313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815313).length < 2 ^ (prefixWord ++ tailWord_1815313).sum := by decide
  have hdescent : baseEnd_1815313 < baseStart_1815313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815319 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 4]
def baseStart_1815319 : Nat := 118140960795 + 1815319 * 2 ^ 59
def prefixEnd_1815319 : Nat := 4983230072969 + 3 ^ 40 * 1815319 * 2
def baseEnd_1815319 : Nat := 414280528106350351006225

theorem tailTrace_1815319 : CollatzResearch.WordTrace tailWord_1815319 prefixEnd_1815319 414280528106350351006225 := by
  unfold tailWord_1815319
  simp only [CollatzResearch.WordTrace]
  refine ⟨66210123310416769647417011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44140082206944513098278007 66210123310416769647417011)
  ·
    refine ⟨99315184965625154471125517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66210123310416769647417011 99315184965625154471125517)
    ·
      refine ⟨37243194362109432926672069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99315184965625154471125517 37243194362109432926672069)
      ·
        refine ⟨6983098942895518673751013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37243194362109432926672069 6983098942895518673751013)
        ·
          refine ⟨1309331051792909751328315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6983098942895518673751013 1309331051792909751328315)
          ·
            refine ⟨1963996577689364626992473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309331051792909751328315 1963996577689364626992473)
            ·
              refine ⟨1472997433267023470244355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963996577689364626992473 1472997433267023470244355)
              ·
                refine ⟨2209496149900535205366533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472997433267023470244355 2209496149900535205366533)
                ·
                  refine ⟨414280528106350351006225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209496149900535205366533 414280528106350351006225)
                  ·
                    rfl

theorem cell21_1815319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4].length) (baseStart_1815319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815319 prefixEnd_1815319 := by exact prefixLift 1815319
  have htrace : WordTrace (prefixWord ++ tailWord_1815319) baseStart_1815319 baseEnd_1815319 := by
    simpa [prefixWord, tailWord_1815319, baseEnd_1815319] using wordTrace_append hprefix tailTrace_1815319
  have hstable : (prefixWord ++ tailWord_1815319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815319).length < 2 ^ (prefixWord ++ tailWord_1815319).sum := by decide
  have hdescent : baseEnd_1815319 < baseStart_1815319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815358 : List Nat := [4, 2, 1, 2, 12]
def baseStart_1815358 : Nat := 118140960795 + 1815358 * 2 ^ 59
def prefixEnd_1815358 : Nat := 4983230072969 + 3 ^ 40 * 1815358 * 2
def baseEnd_1815358 : Nat := 5114684301699937652545

theorem tailTrace_1815358 : CollatzResearch.WordTrace tailWord_1815358 prefixEnd_1815358 5114684301699937652545 := by
  unfold tailWord_1815358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276443219659434913510841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44141030504850319538724485 8276443219659434913510841)
  ·
    refine ⟨6207332414744576185133131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8276443219659434913510841 6207332414744576185133131)
    ·
      refine ⟨9310998622116864277699697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207332414744576185133131 9310998622116864277699697)
      ·
        refine ⟨6983248966587648208274773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9310998622116864277699697 6983248966587648208274773)
        ·
          refine ⟨5114684301699937652545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6983248966587648208274773 5114684301699937652545)
          ·
            rfl

theorem cell21_1815358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 12].length) (baseStart_1815358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815358 prefixEnd_1815358 := by exact prefixLift 1815358
  have htrace : WordTrace (prefixWord ++ tailWord_1815358) baseStart_1815358 baseEnd_1815358 := by
    simpa [prefixWord, tailWord_1815358, baseEnd_1815358] using wordTrace_append hprefix tailTrace_1815358
  have hstable : (prefixWord ++ tailWord_1815358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815358).length < 2 ^ (prefixWord ++ tailWord_1815358).sum := by decide
  have hdescent : baseEnd_1815358 < baseStart_1815358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815479 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_1815479 : Nat := 118140960795 + 1815479 * 2 ^ 59
def prefixEnd_1815479 : Nat := 4983230072969 + 3 ^ 40 * 1815479 * 2
def baseEnd_1815479 : Nat := 414317042286225628339231

theorem tailTrace_1815479 : CollatzResearch.WordTrace tailWord_1815479 prefixEnd_1815479 414317042286225628339231 := by
  unfold tailWord_1815479
  simp only [CollatzResearch.WordTrace]
  refine ⟨66215958989837116973241491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44143972659891411315494327 66215958989837116973241491)
  ·
    refine ⟨99323938484755675459862237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66215958989837116973241491 99323938484755675459862237)
    ·
      refine ⟨37246476931783378297448339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99323938484755675459862237 37246476931783378297448339)
      ·
        refine ⟨55869715397675067446172509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37246476931783378297448339 55869715397675067446172509)
        ·
          refine ⟨20951143274128150292314691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55869715397675067446172509 20951143274128150292314691)
          ·
            refine ⟨31426714911192225438472037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20951143274128150292314691 31426714911192225438472037)
            ·
              refine ⟨5892509045848542269713507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31426714911192225438472037 5892509045848542269713507)
              ·
                refine ⟨8838763568772813404570261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892509045848542269713507 8838763568772813404570261)
                ·
                  refine ⟨414317042286225628339231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8838763568772813404570261 414317042286225628339231)
                  ·
                    rfl

theorem cell21_1815479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_1815479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815479 prefixEnd_1815479 := by exact prefixLift 1815479
  have htrace : WordTrace (prefixWord ++ tailWord_1815479) baseStart_1815479 baseEnd_1815479 := by
    simpa [prefixWord, tailWord_1815479, baseEnd_1815479] using wordTrace_append hprefix tailTrace_1815479
  have hstable : (prefixWord ++ tailWord_1815479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815479).length < 2 ^ (prefixWord ++ tailWord_1815479).sum := by decide
  have hdescent : baseEnd_1815479 < baseStart_1815479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815524 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1815524 : Nat := 118140960795 + 1815524 * 2 ^ 59
def prefixEnd_1815524 : Nat := 4983230072969 + 3 ^ 40 * 1815524 * 2
def baseEnd_1815524 : Nat := 414327311899315550089139

theorem tailTrace_1815524 : CollatzResearch.WordTrace tailWord_1815524 prefixEnd_1815524 414327311899315550089139 := by
  unfold tailWord_1815524
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108800137337044829314813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44145066849782726439086417 33108800137337044829314813)
  ·
    refine ⟨12415800051501391810993055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33108800137337044829314813 12415800051501391810993055)
    ·
      refine ⟨18623700077252087716489583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415800051501391810993055 18623700077252087716489583)
      ·
        refine ⟨27935550115878131574734375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18623700077252087716489583 27935550115878131574734375)
        ·
          refine ⟨41903325173817197362101563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27935550115878131574734375 41903325173817197362101563)
          ·
            refine ⟨62854987760725796043152345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41903325173817197362101563 62854987760725796043152345)
            ·
              refine ⟨47141240820544347032364259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62854987760725796043152345 47141240820544347032364259)
              ·
                refine ⟨70711861230816520548546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47141240820544347032364259 70711861230816520548546389)
                ·
                  refine ⟨414327311899315550089139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70711861230816520548546389 414327311899315550089139)
                  ·
                    rfl

theorem cell21_1815524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1815524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815524 prefixEnd_1815524 := by exact prefixLift 1815524
  have htrace : WordTrace (prefixWord ++ tailWord_1815524) baseStart_1815524 baseEnd_1815524 := by
    simpa [prefixWord, tailWord_1815524, baseEnd_1815524] using wordTrace_append hprefix tailTrace_1815524
  have hstable : (prefixWord ++ tailWord_1815524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815524).length < 2 ^ (prefixWord ++ tailWord_1815524).sum := by decide
  have hdescent : baseEnd_1815524 < baseStart_1815524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815569 : List Nat := [1, 2, 2, 1, 1, 2, 1, 11]
def baseStart_1815569 : Nat := 118140960795 + 1815569 * 2 ^ 59
def prefixEnd_1815569 : Nat := 4983230072969 + 3 ^ 40 * 1815569 * 2
def baseEnd_1815569 : Nat := 138112527170801823946349

theorem tailTrace_1815569 : CollatzResearch.WordTrace tailWord_1815569 prefixEnd_1815569 138112527170801823946349 := by
  unfold tailWord_1815569
  simp only [CollatzResearch.WordTrace]
  refine ⟨66219241559511062344017761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44146161039674041562678507 66219241559511062344017761)
  ·
    refine ⟨49664431169633296758013321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66219241559511062344017761 49664431169633296758013321)
    ·
      refine ⟨37248323377224972568509991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49664431169633296758013321 37248323377224972568509991)
      ·
        refine ⟨55872485065837458852764987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37248323377224972568509991 55872485065837458852764987)
        ·
          refine ⟨83808727598756188279147481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55872485065837458852764987 83808727598756188279147481)
          ·
            refine ⟨62856545699067141209360611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83808727598756188279147481 62856545699067141209360611)
            ·
              refine ⟨94284818548600711814040917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62856545699067141209360611 94284818548600711814040917)
              ·
                refine ⟨138112527170801823946349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94284818548600711814040917 138112527170801823946349)
                ·
                  rfl

theorem cell21_1815569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_1815569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815569 prefixEnd_1815569 := by exact prefixLift 1815569
  have htrace : WordTrace (prefixWord ++ tailWord_1815569) baseStart_1815569 baseEnd_1815569 := by
    simpa [prefixWord, tailWord_1815569, baseEnd_1815569] using wordTrace_append hprefix tailTrace_1815569
  have hstable : (prefixWord ++ tailWord_1815569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815569).length < 2 ^ (prefixWord ++ tailWord_1815569).sum := by decide
  have hdescent : baseEnd_1815569 < baseStart_1815569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815575 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 3]
def baseStart_1815575 : Nat := 118140960795 + 1815575 * 2 ^ 59
def prefixEnd_1815575 : Nat := 4983230072969 + 3 ^ 40 * 1815575 * 2
def baseEnd_1815575 : Nat := 414338950794150794739035

theorem tailTrace_1815575 : CollatzResearch.WordTrace tailWord_1815575 prefixEnd_1815575 414338950794150794739035 := by
  unfold tailWord_1815575
  simp only [CollatzResearch.WordTrace]
  refine ⟨66219460397489325368736179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44146306931659550245824119 66219460397489325368736179)
  ·
    refine ⟨99329190596233988053104269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66219460397489325368736179 99329190596233988053104269)
    ·
      refine ⟨37248446473587745519914101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99329190596233988053104269 37248446473587745519914101)
      ·
        refine ⟨3492041856898851142491947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37248446473587745519914101 3492041856898851142491947)
        ·
          refine ⟨5238062785348276713737921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492041856898851142491947 5238062785348276713737921)
          ·
            refine ⟨3928547089011207535303441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238062785348276713737921 3928547089011207535303441)
            ·
              refine ⟨2946410316758405651477581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928547089011207535303441 2946410316758405651477581)
              ·
                refine ⟨1104903868784402119304093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946410316758405651477581 1104903868784402119304093)
                ·
                  refine ⟨414338950794150794739035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104903868784402119304093 414338950794150794739035)
                  ·
                    rfl

theorem cell21_1815575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3].length) (baseStart_1815575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815575 prefixEnd_1815575 := by exact prefixLift 1815575
  have htrace : WordTrace (prefixWord ++ tailWord_1815575) baseStart_1815575 baseEnd_1815575 := by
    simpa [prefixWord, tailWord_1815575, baseEnd_1815575] using wordTrace_append hprefix tailTrace_1815575
  have hstable : (prefixWord ++ tailWord_1815575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815575).length < 2 ^ (prefixWord ++ tailWord_1815575).sum := by decide
  have hdescent : baseEnd_1815575 < baseStart_1815575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815586 : List Nat := [3, 3, 1, 1, 1, 4, 8]
def baseStart_1815586 : Nat := 118140960795 + 1815586 * 2 ^ 59
def prefixEnd_1815586 : Nat := 4983230072969 + 3 ^ 40 * 1815586 * 2
def baseEnd_1815586 : Nat := 46037940127113024450631

theorem tailTrace_1815586 : CollatzResearch.WordTrace tailWord_1815586 prefixEnd_1815586 46037940127113024450631 := by
  unfold tailWord_1815586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554965400112368561846653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44146574400299649498257741 16554965400112368561846653)
  ·
    refine ⟨6208112025042138210692495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16554965400112368561846653 6208112025042138210692495)
    ·
      refine ⟨9312168037563207316038743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6208112025042138210692495 9312168037563207316038743)
      ·
        refine ⟨13968252056344810974058115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312168037563207316038743 13968252056344810974058115)
        ·
          refine ⟨20952378084517216461087173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13968252056344810974058115 20952378084517216461087173)
          ·
            refine ⟨3928570890846978086453845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20952378084517216461087173 3928570890846978086453845)
            ·
              refine ⟨46037940127113024450631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3928570890846978086453845 46037940127113024450631)
              ·
                rfl

theorem cell21_1815586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 8].length) (baseStart_1815586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815586 prefixEnd_1815586 := by exact prefixLift 1815586
  have htrace : WordTrace (prefixWord ++ tailWord_1815586) baseStart_1815586 baseEnd_1815586 := by
    simpa [prefixWord, tailWord_1815586, baseEnd_1815586] using wordTrace_append hprefix tailTrace_1815586
  have hstable : (prefixWord ++ tailWord_1815586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815586).length < 2 ^ (prefixWord ++ tailWord_1815586).sum := by decide
  have hdescent : baseEnd_1815586 < baseStart_1815586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815606 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1815606 : Nat := 118140960795 + 1815606 * 2 ^ 59
def prefixEnd_1815606 : Nat := 4983230072969 + 3 ^ 40 * 1815606 * 2
def baseEnd_1815606 : Nat := 414346025416501629722305

theorem tailTrace_1815606 : CollatzResearch.WordTrace tailWord_1815606 prefixEnd_1815606 414346025416501629722305 := by
  unfold tailWord_1815606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138786941273563603944667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44147060706918011775409781 4138786941273563603944667)
  ·
    refine ⟨6208180411910345405917001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138786941273563603944667 6208180411910345405917001)
    ·
      refine ⟨4656135308932759054437751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208180411910345405917001 4656135308932759054437751)
      ·
        refine ⟨6984202963399138581656627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656135308932759054437751 6984202963399138581656627)
        ·
          refine ⟨10476304445098707872484941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984202963399138581656627 10476304445098707872484941)
          ·
            refine ⟨3928614166912015452181853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10476304445098707872484941 3928614166912015452181853)
            ·
              refine ⟨1473230312592005794568195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3928614166912015452181853 1473230312592005794568195)
              ·
                refine ⟨2209845468888008691852293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473230312592005794568195 2209845468888008691852293)
                ·
                  refine ⟨414346025416501629722305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209845468888008691852293 414346025416501629722305)
                  ·
                    rfl

theorem cell21_1815606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1815606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815606 prefixEnd_1815606 := by exact prefixLift 1815606
  have htrace : WordTrace (prefixWord ++ tailWord_1815606) baseStart_1815606 baseEnd_1815606 := by
    simpa [prefixWord, tailWord_1815606, baseEnd_1815606] using wordTrace_append hprefix tailTrace_1815606
  have hstable : (prefixWord ++ tailWord_1815606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815606).length < 2 ^ (prefixWord ++ tailWord_1815606).sum := by decide
  have hdescent : baseEnd_1815606 < baseStart_1815606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815662 : List Nat := [4, 1, 2, 2, 1, 2, 1, 8]
def baseStart_1815662 : Nat := 118140960795 + 1815662 * 2 ^ 59
def prefixEnd_1815662 : Nat := 4983230072969 + 3 ^ 40 * 1815662 * 2
def baseEnd_1815662 : Nat := 138119601793152658929619

theorem tailTrace_1815662 : CollatzResearch.WordTrace tailWord_1815662 prefixEnd_1815662 138119601793152658929619 := by
  unfold tailWord_1815662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277829193521767403394155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44148422365449426151435493 8277829193521767403394155)
  ·
    refine ⟨12416743790282651105091233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8277829193521767403394155 12416743790282651105091233)
    ·
      refine ⟨9312557842711988328818425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12416743790282651105091233 9312557842711988328818425)
      ·
        refine ⟨6984418382033991246613819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9312557842711988328818425 6984418382033991246613819)
        ·
          refine ⟨10476627573050986869920729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984418382033991246613819 10476627573050986869920729)
          ·
            refine ⟨7857470679788240152440547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476627573050986869920729 7857470679788240152440547)
            ·
              refine ⟨11786206019682360228660821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857470679788240152440547 11786206019682360228660821)
              ·
                refine ⟨138119601793152658929619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11786206019682360228660821 138119601793152658929619)
                ·
                  rfl

theorem cell21_1815662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_1815662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815662 prefixEnd_1815662 := by exact prefixLift 1815662
  have htrace : WordTrace (prefixWord ++ tailWord_1815662) baseStart_1815662 baseEnd_1815662 := by
    simpa [prefixWord, tailWord_1815662, baseEnd_1815662] using wordTrace_append hprefix tailTrace_1815662
  have hstable : (prefixWord ++ tailWord_1815662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815662).length < 2 ^ (prefixWord ++ tailWord_1815662).sum := by decide
  have hdescent : baseEnd_1815662 < baseStart_1815662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815676 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_1815676 : Nat := 118140960795 + 1815676 * 2 ^ 59
def prefixEnd_1815676 : Nat := 4983230072969 + 3 ^ 40 * 1815676 * 2
def baseEnd_1815676 : Nat := 414362000370197063555495

theorem tailTrace_1815676 : CollatzResearch.WordTrace tailWord_1815676 prefixEnd_1815676 414362000370197063555495 := by
  unfold tailWord_1815676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33111572085061709809081441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44148762780082279745441921 33111572085061709809081441)
  ·
    refine ⟨24833679063796282356811081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33111572085061709809081441 24833679063796282356811081)
    ·
      refine ⟨18625259297847211767608311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24833679063796282356811081 18625259297847211767608311)
      ·
        refine ⟨27937888946770817651412467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18625259297847211767608311 27937888946770817651412467)
        ·
          refine ⟨41906833420156226477118701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27937888946770817651412467 41906833420156226477118701)
          ·
            refine ⟨15715062532558584928919513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41906833420156226477118701 15715062532558584928919513)
            ·
              refine ⟨11786296899418938696689635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15715062532558584928919513 11786296899418938696689635)
              ·
                refine ⟨17679445349128408045034453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786296899418938696689635 17679445349128408045034453)
                ·
                  refine ⟨414362000370197063555495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17679445349128408045034453 414362000370197063555495)
                  ·
                    rfl

theorem cell21_1815676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_1815676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815676 prefixEnd_1815676 := by exact prefixLift 1815676
  have htrace : WordTrace (prefixWord ++ tailWord_1815676) baseStart_1815676 baseEnd_1815676 := by
    simpa [prefixWord, tailWord_1815676, baseEnd_1815676] using wordTrace_append hprefix tailTrace_1815676
  have hstable : (prefixWord ++ tailWord_1815676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815676).length < 2 ^ (prefixWord ++ tailWord_1815676).sum := by decide
  have hdescent : baseEnd_1815676 < baseStart_1815676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815758 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1815758 : Nat := 118140960795 + 1815758 * 2 ^ 59
def prefixEnd_1815758 : Nat := 4983230072969 + 3 ^ 40 * 1815758 * 2
def baseEnd_1815758 : Nat := 414380713887383143188661

theorem tailTrace_1815758 : CollatzResearch.WordTrace tailWord_1815758 prefixEnd_1815758 414380713887383143188661 := by
  unfold tailWord_1815758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278266869478293452830991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44150756637217565081765285 8278266869478293452830991)
  ·
    refine ⟨12417400304217440179246487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8278266869478293452830991 12417400304217440179246487)
    ·
      refine ⟨18626100456326160268869731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12417400304217440179246487 18626100456326160268869731)
      ·
        refine ⟨27939150684489240403304597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18626100456326160268869731 27939150684489240403304597)
        ·
          refine ⟨1309647688335433143904903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27939150684489240403304597 1309647688335433143904903)
          ·
            refine ⟨1964471532503149715857355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309647688335433143904903 1964471532503149715857355)
            ·
              refine ⟨2946707298754724573786033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964471532503149715857355 2946707298754724573786033)
              ·
                refine ⟨2210030474066043430339525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946707298754724573786033 2210030474066043430339525)
                ·
                  refine ⟨414380713887383143188661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210030474066043430339525 414380713887383143188661)
                  ·
                    rfl

theorem cell21_1815758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1815758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815758 prefixEnd_1815758 := by exact prefixLift 1815758
  have htrace : WordTrace (prefixWord ++ tailWord_1815758) baseStart_1815758 baseEnd_1815758 := by
    simpa [prefixWord, tailWord_1815758, baseEnd_1815758] using wordTrace_append hprefix tailTrace_1815758
  have hstable : (prefixWord ++ tailWord_1815758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815758).length < 2 ^ (prefixWord ++ tailWord_1815758).sum := by decide
  have hdescent : baseEnd_1815758 < baseStart_1815758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815879 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 3]
def baseStart_1815879 : Nat := 118140960795 + 1815879 * 2 ^ 59
def prefixEnd_1815879 : Nat := 4983230072969 + 3 ^ 40 * 1815879 * 2
def baseEnd_1815879 : Nat := 414408327735913821671747

theorem tailTrace_1815879 : CollatzResearch.WordTrace tailWord_1815879 prefixEnd_1815879 414408327735913821671747 := by
  unfold tailWord_1815879
  simp only [CollatzResearch.WordTrace]
  refine ⟨66230548188387985287802691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44153698792258656858535127 66230548188387985287802691)
  ·
    refine ⟨99345822282581977931704037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66230548188387985287802691 99345822282581977931704037)
    ·
      refine ⟨18627341677984120862194507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99345822282581977931704037 18627341677984120862194507)
      ·
        refine ⟨27941012516976181293291761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18627341677984120862194507 27941012516976181293291761)
        ·
          refine ⟨20955759387732135969968821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27941012516976181293291761 20955759387732135969968821)
          ·
            refine ⟨1964602442599887747184577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20955759387732135969968821 1964602442599887747184577)
            ·
              refine ⟨1473451831949915810388433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964602442599887747184577 1473451831949915810388433)
              ·
                refine ⟨1105088873962436857791325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473451831949915810388433 1105088873962436857791325)
                ·
                  refine ⟨414408327735913821671747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105088873962436857791325 414408327735913821671747)
                  ·
                    rfl

theorem cell21_1815879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3].length) (baseStart_1815879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815879 prefixEnd_1815879 := by exact prefixLift 1815879
  have htrace : WordTrace (prefixWord ++ tailWord_1815879) baseStart_1815879 baseEnd_1815879 := by
    simpa [prefixWord, tailWord_1815879, baseEnd_1815879] using wordTrace_append hprefix tailTrace_1815879
  have hstable : (prefixWord ++ tailWord_1815879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815879).length < 2 ^ (prefixWord ++ tailWord_1815879).sum := by decide
  have hdescent : baseEnd_1815879 < baseStart_1815879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815904 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_1815904 : Nat := 118140960795 + 1815904 * 2 ^ 59
def prefixEnd_1815904 : Nat := 4983230072969 + 3 ^ 40 * 1815904 * 2
def baseEnd_1815904 : Nat := 414414033076519333755029

theorem tailTrace_1815904 : CollatzResearch.WordTrace tailWord_1815904 prefixEnd_1815904 414414033076519333755029 := by
  unfold tailWord_1815904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33115730006648707278731383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44154306675531609704975177 33115730006648707278731383)
  ·
    refine ⟨49673595009973060918097075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33115730006648707278731383 49673595009973060918097075)
    ·
      refine ⟨74510392514959591377145613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49673595009973060918097075 74510392514959591377145613)
      ·
        refine ⟨27941397193109846766429605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74510392514959591377145613 27941397193109846766429605)
        ·
          refine ⟨5239011973708096268705551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27941397193109846766429605 5239011973708096268705551)
          ·
            refine ⟨7858517960562144403058327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239011973708096268705551 7858517960562144403058327)
            ·
              refine ⟨11787776940843216604587491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858517960562144403058327 11787776940843216604587491)
              ·
                refine ⟨17681665411264824906881237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787776940843216604587491 17681665411264824906881237)
                ·
                  refine ⟨414414033076519333755029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17681665411264824906881237 414414033076519333755029)
                  ·
                    rfl

theorem cell21_1815904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_1815904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815904 prefixEnd_1815904 := by exact prefixLift 1815904
  have htrace : WordTrace (prefixWord ++ tailWord_1815904) baseStart_1815904 baseEnd_1815904 := by
    simpa [prefixWord, tailWord_1815904, baseEnd_1815904] using wordTrace_append hprefix tailTrace_1815904
  have hstable : (prefixWord ++ tailWord_1815904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815904).length < 2 ^ (prefixWord ++ tailWord_1815904).sum := by decide
  have hdescent : baseEnd_1815904 < baseStart_1815904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815921 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 3]
def baseStart_1815921 : Nat := 118140960795 + 1815921 * 2 ^ 59
def prefixEnd_1815921 : Nat := 4983230072969 + 3 ^ 40 * 1815921 * 2
def baseEnd_1815921 : Nat := 414417912708131081971661

theorem tailTrace_1815921 : CollatzResearch.WordTrace tailWord_1815921 prefixEnd_1815921 414417912708131081971661 := by
  unfold tailWord_1815921
  simp only [CollatzResearch.WordTrace]
  refine ⟨66232080054235826460831617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44154720036157217640554411 66232080054235826460831617)
  ·
    refine ⟨49674060040676869845623713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66232080054235826460831617 49674060040676869845623713)
    ·
      refine ⟨37255545030507652384217785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49674060040676869845623713 37255545030507652384217785)
      ·
        refine ⟨27941658772880739288163339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37255545030507652384217785 27941658772880739288163339)
        ·
          refine ⟨41912488159321108932245009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27941658772880739288163339 41912488159321108932245009)
          ·
            refine ⟨31434366119490831699183757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41912488159321108932245009 31434366119490831699183757)
            ·
              refine ⟨11787887294809061887193909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31434366119490831699183757 11787887294809061887193909)
              ·
                refine ⟨1105114433888349551924429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11787887294809061887193909 1105114433888349551924429)
                ·
                  refine ⟨414417912708131081971661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105114433888349551924429 414417912708131081971661)
                  ·
                    rfl

theorem cell21_1815921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_1815921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815921 prefixEnd_1815921 := by exact prefixLift 1815921
  have htrace : WordTrace (prefixWord ++ tailWord_1815921) baseStart_1815921 baseEnd_1815921 := by
    simpa [prefixWord, tailWord_1815921, baseEnd_1815921] using wordTrace_append hprefix tailTrace_1815921
  have hstable : (prefixWord ++ tailWord_1815921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815921).length < 2 ^ (prefixWord ++ tailWord_1815921).sum := by decide
  have hdescent : baseEnd_1815921 < baseStart_1815921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815938 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1815938 : Nat := 118140960795 + 1815938 * 2 ^ 59
def prefixEnd_1815938 : Nat := 4983230072969 + 3 ^ 40 * 1815938 * 2
def baseEnd_1815938 : Nat := 414421792339742830188293

theorem tailTrace_1815938 : CollatzResearch.WordTrace tailWord_1815938 prefixEnd_1815938 414421792339742830188293 := by
  unfold tailWord_1815938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16558175023793559591050117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44155133396782825576133645 16558175023793559591050117)
  ·
    refine ⟨3104657816961292423321897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16558175023793559591050117 3104657816961292423321897)
    ·
      refine ⟨2328493362720969317491423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3104657816961292423321897 2328493362720969317491423)
      ·
        refine ⟨3492740044081453976237135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328493362720969317491423 3492740044081453976237135)
        ·
          refine ⟨5239110066122180964355703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492740044081453976237135 5239110066122180964355703)
          ·
            refine ⟨7858665099183271446533555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239110066122180964355703 7858665099183271446533555)
            ·
              refine ⟨11787997648774907169800333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858665099183271446533555 11787997648774907169800333)
              ·
                refine ⟨4420499118290590188675125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11787997648774907169800333 4420499118290590188675125)
                ·
                  refine ⟨414421792339742830188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4420499118290590188675125 414421792339742830188293)
                  ·
                    rfl

theorem cell21_1815938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1815938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1815938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1815938 prefixEnd_1815938 := by exact prefixLift 1815938
  have htrace : WordTrace (prefixWord ++ tailWord_1815938) baseStart_1815938 baseEnd_1815938 := by
    simpa [prefixWord, tailWord_1815938, baseEnd_1815938] using wordTrace_append hprefix tailTrace_1815938
  have hstable : (prefixWord ++ tailWord_1815938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815938).length < 2 ^ (prefixWord ++ tailWord_1815938).sum := by decide
  have hdescent : baseEnd_1815938 < baseStart_1815938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816025 : List Nat := [1, 2, 1, 2, 4, 2, 2, 7]
def baseStart_1816025 : Nat := 118140960795 + 1816025 * 2 ^ 59
def prefixEnd_1816025 : Nat := 4983230072969 + 3 ^ 40 * 1816025 * 2
def baseEnd_1816025 : Nat := 138147215641683337412705

theorem tailTrace_1816025 : CollatzResearch.WordTrace tailWord_1816025 prefixEnd_1816025 138147215641683337412705 := by
  unfold tailWord_1816025
  simp only [CollatzResearch.WordTrace]
  refine ⟨66235873245859052222617529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44157248830572701481745019 66235873245859052222617529)
  ·
    refine ⟨49676904934394289166963147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66235873245859052222617529 49676904934394289166963147)
    ·
      refine ⟨74515357401591433750444721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49676904934394289166963147 74515357401591433750444721)
      ·
        refine ⟨55886518051193575312833541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74515357401591433750444721 55886518051193575312833541)
        ·
          refine ⟨10478722134598795371156289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55886518051193575312833541 10478722134598795371156289)
          ·
            refine ⟨7859041600949096528367217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10478722134598795371156289 7859041600949096528367217)
            ·
              refine ⟨5894281200711822396275413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7859041600949096528367217 5894281200711822396275413)
              ·
                refine ⟨138147215641683337412705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5894281200711822396275413 138147215641683337412705)
                ·
                  rfl

theorem cell21_1816025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_1816025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816025 prefixEnd_1816025 := by exact prefixLift 1816025
  have htrace : WordTrace (prefixWord ++ tailWord_1816025) baseStart_1816025 baseEnd_1816025 := by
    simpa [prefixWord, tailWord_1816025, baseEnd_1816025] using wordTrace_append hprefix tailTrace_1816025
  have hstable : (prefixWord ++ tailWord_1816025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816025).length < 2 ^ (prefixWord ++ tailWord_1816025).sum := by decide
  have hdescent : baseEnd_1816025 < baseStart_1816025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816042 : List Nat := [3, 1, 3, 1, 5, 8]
def baseStart_1816042 : Nat := 118140960795 + 1816042 * 2 ^ 59
def prefixEnd_1816042 : Nat := 4983230072969 + 3 ^ 40 * 1816042 * 2
def baseEnd_1816042 : Nat := 15349834316913398535361

theorem tailTrace_1816042 : CollatzResearch.WordTrace tailWord_1816042 prefixEnd_1816042 15349834316913398535361 := by
  unfold tailWord_1816042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559123321699366031496595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44157662191198309417324253 16559123321699366031496595)
  ·
    refine ⟨24838684982549049047244893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16559123321699366031496595 24838684982549049047244893)
    ·
      refine ⟨9314506868455893392716835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24838684982549049047244893 9314506868455893392716835)
      ·
        refine ⟨13971760302683840089075253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314506868455893392716835 13971760302683840089075253)
        ·
          refine ⟨1309852528376610008350805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13971760302683840089075253 1309852528376610008350805)
          ·
            refine ⟨15349834316913398535361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1309852528376610008350805 15349834316913398535361)
            ·
              rfl

theorem cell21_1816042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 8].length) (baseStart_1816042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816042 prefixEnd_1816042 := by exact prefixLift 1816042
  have htrace : WordTrace (prefixWord ++ tailWord_1816042) baseStart_1816042 baseEnd_1816042 := by
    simpa [prefixWord, tailWord_1816042, baseEnd_1816042] using wordTrace_append hprefix tailTrace_1816042
  have hstable : (prefixWord ++ tailWord_1816042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816042).length < 2 ^ (prefixWord ++ tailWord_1816042).sum := by decide
  have hdescent : baseEnd_1816042 < baseStart_1816042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816045 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1816045 : Nat := 118140960795 + 1816045 * 2 ^ 59
def prefixEnd_1816045 : Nat := 4983230072969 + 3 ^ 40 * 1816045 * 2
def baseEnd_1816045 : Nat := 414446211197534421904741

theorem tailTrace_1816045 : CollatzResearch.WordTrace tailWord_1816045 prefixEnd_1816045 414446211197534421904741 := by
  unfold tailWord_1816045
  simp only [CollatzResearch.WordTrace]
  refine ⟨66236602705786595638345589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44157735137191063758897059 66236602705786595638345589)
  ·
    refine ⟨6209681503667493341094899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66236602705786595638345589 6209681503667493341094899)
    ·
      refine ⟨9314522255501240011642349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209681503667493341094899 9314522255501240011642349)
      ·
        refine ⟨3492945845812965004365881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9314522255501240011642349 3492945845812965004365881)
        ·
          refine ⟨2619709384359723753274411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3492945845812965004365881 2619709384359723753274411)
          ·
            refine ⟨3929564076539585629911617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619709384359723753274411 3929564076539585629911617)
            ·
              refine ⟨2947173057404689222433713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3929564076539585629911617 2947173057404689222433713)
              ·
                refine ⟨2210379793053516916825285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947173057404689222433713 2210379793053516916825285)
                ·
                  refine ⟨414446211197534421904741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210379793053516916825285 414446211197534421904741)
                  ·
                    rfl

theorem cell21_1816045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1816045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816045 prefixEnd_1816045 := by exact prefixLift 1816045
  have htrace : WordTrace (prefixWord ++ tailWord_1816045) baseStart_1816045 baseEnd_1816045 := by
    simpa [prefixWord, tailWord_1816045, baseEnd_1816045] using wordTrace_append hprefix tailTrace_1816045
  have hstable : (prefixWord ++ tailWord_1816045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816045).length < 2 ^ (prefixWord ++ tailWord_1816045).sum := by decide
  have hdescent : baseEnd_1816045 < baseStart_1816045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816104 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_1816104 : Nat := 118140960795 + 1816104 * 2 ^ 59
def prefixEnd_1816104 : Nat := 4983230072969 + 3 ^ 40 * 1816104 * 2
def baseEnd_1816104 : Nat := 414459675801363430421287

theorem tailTrace_1816104 : CollatzResearch.WordTrace tailWord_1816104 prefixEnd_1816104 414459675801363430421287 := by
  unfold tailWord_1816104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33119377306286424357371683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44159169741715232476495577 33119377306286424357371683)
  ·
    refine ⟨49679065959429636536057525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33119377306286424357371683 49679065959429636536057525)
    ·
      refine ⟨4657412433696528425255393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49679065959429636536057525 4657412433696528425255393)
      ·
        refine ⟨3493059325272396318941545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4657412433696528425255393 3493059325272396318941545)
        ·
          refine ⟨2619794493954297239206159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3493059325272396318941545 2619794493954297239206159)
          ·
            refine ⟨3929691740931445858809239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619794493954297239206159 3929691740931445858809239)
            ·
              refine ⟨5894537611397168788213859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929691740931445858809239 5894537611397168788213859)
              ·
                refine ⟨8841806417095753182320789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894537611397168788213859 8841806417095753182320789)
                ·
                  refine ⟨414459675801363430421287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8841806417095753182320789 414459675801363430421287)
                  ·
                    rfl

theorem cell21_1816104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_1816104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816104 prefixEnd_1816104 := by exact prefixLift 1816104
  have htrace : WordTrace (prefixWord ++ tailWord_1816104) baseStart_1816104 baseEnd_1816104 := by
    simpa [prefixWord, tailWord_1816104, baseEnd_1816104] using wordTrace_append hprefix tailTrace_1816104
  have hstable : (prefixWord ++ tailWord_1816104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816104).length < 2 ^ (prefixWord ++ tailWord_1816104).sum := by decide
  have hdescent : baseEnd_1816104 < baseStart_1816104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816135 : List Nat := [1, 1, 4, 1, 5, 2, 2, 5]
def baseStart_1816135 : Nat := 118140960795 + 1816135 * 2 ^ 59
def prefixEnd_1816135 : Nat := 4983230072969 + 3 ^ 40 * 1816135 * 2
def baseEnd_1816135 : Nat := 138155583474571421801519

theorem tailTrace_1816135 : CollatzResearch.WordTrace tailWord_1816135 prefixEnd_1816135 138155583474571421801519 := by
  unfold tailWord_1816135
  simp only [CollatzResearch.WordTrace]
  refine ⟨66239885275460541009121859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44159923516973694006081239 66239885275460541009121859)
  ·
    refine ⟨99359827913190811513682789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66239885275460541009121859 99359827913190811513682789)
    ·
      refine ⟨18629967733723277158815523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99359827913190811513682789 18629967733723277158815523)
      ·
        refine ⟨27944951600584915738223285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18629967733723277158815523 27944951600584915738223285)
        ·
          refine ⟨2619839212554835850458433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27944951600584915738223285 2619839212554835850458433)
          ·
            refine ⟨1964879409416126887843825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619839212554835850458433 1964879409416126887843825)
            ·
              refine ⟨1473659557062095165882869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964879409416126887843825 1473659557062095165882869)
              ·
                refine ⟨138155583474571421801519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473659557062095165882869 138155583474571421801519)
                ·
                  rfl

theorem cell21_1816135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 5].length) (baseStart_1816135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816135 prefixEnd_1816135 := by exact prefixLift 1816135
  have htrace : WordTrace (prefixWord ++ tailWord_1816135) baseStart_1816135 baseEnd_1816135 := by
    simpa [prefixWord, tailWord_1816135, baseEnd_1816135] using wordTrace_append hprefix tailTrace_1816135
  have hstable : (prefixWord ++ tailWord_1816135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816135).length < 2 ^ (prefixWord ++ tailWord_1816135).sum := by decide
  have hdescent : baseEnd_1816135 < baseStart_1816135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816405 : List Nat := [1, 3, 2, 2, 2, 2, 3, 6]
def baseStart_1816405 : Nat := 118140960795 + 1816405 * 2 ^ 59
def prefixEnd_1816405 : Nat := 4983230072969 + 3 ^ 40 * 1816405 * 2
def baseEnd_1816405 : Nat := 138176122700751265301335

theorem tailTrace_1816405 : CollatzResearch.WordTrace tailWord_1816405 prefixEnd_1816405 138176122700751265301335 := by
  unfold tailWord_1816405
  simp only [CollatzResearch.WordTrace]
  refine ⟨66249732984482377121450669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44166488656321584747633779 66249732984482377121450669)
  ·
    refine ⟨24843649869180891420544001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66249732984482377121450669 24843649869180891420544001)
    ·
      refine ⟨18632737401885668565408001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24843649869180891420544001 18632737401885668565408001)
      ·
        refine ⟨13974553051414251424056001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18632737401885668565408001 13974553051414251424056001)
        ·
          refine ⟨10480914788560688568042001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13974553051414251424056001 10480914788560688568042001)
          ·
            refine ⟨7860686091420516426031501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10480914788560688568042001 7860686091420516426031501)
            ·
              refine ⟨2947757284282693659761813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7860686091420516426031501 2947757284282693659761813)
              ·
                refine ⟨138176122700751265301335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2947757284282693659761813 138176122700751265301335)
                ·
                  rfl

theorem cell21_1816405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_1816405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816405 prefixEnd_1816405 := by exact prefixLift 1816405
  have htrace : WordTrace (prefixWord ++ tailWord_1816405) baseStart_1816405 baseEnd_1816405 := by
    simpa [prefixWord, tailWord_1816405, baseEnd_1816405] using wordTrace_append hprefix tailTrace_1816405
  have hstable : (prefixWord ++ tailWord_1816405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816405).length < 2 ^ (prefixWord ++ tailWord_1816405).sum := by decide
  have hdescent : baseEnd_1816405 < baseStart_1816405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816557 : List Nat := [1, 5, 1, 4, 10]
def baseStart_1816557 : Nat := 118140960795 + 1816557 * 2 ^ 59
def prefixEnd_1816557 : Nat := 4983230072969 + 3 ^ 40 * 1816557 * 2
def baseEnd_1816557 : Nat := 5118062426828830979881

theorem tailTrace_1816557 : CollatzResearch.WordTrace tailWord_1816557 prefixEnd_1816557 5118062426828830979881 := by
  unfold tailWord_1816557
  simp only [CollatzResearch.WordTrace]
  refine ⟨66255276879931707080983925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44170184586621138053989283 66255276879931707080983925)
  ·
    refine ⟨6211432207493597538842243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66255276879931707080983925 6211432207493597538842243)
    ·
      refine ⟨9317148311240396308263365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6211432207493597538842243 9317148311240396308263365)
      ·
        refine ⟨1746965308357574307799381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9317148311240396308263365 1746965308357574307799381)
        ·
          refine ⟨5118062426828830979881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1746965308357574307799381 5118062426828830979881)
          ·
            rfl

theorem cell21_1816557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 10].length) (baseStart_1816557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816557 prefixEnd_1816557 := by exact prefixLift 1816557
  have htrace : WordTrace (prefixWord ++ tailWord_1816557) baseStart_1816557 baseEnd_1816557 := by
    simpa [prefixWord, tailWord_1816557, baseEnd_1816557] using wordTrace_append hprefix tailTrace_1816557
  have hstable : (prefixWord ++ tailWord_1816557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816557).length < 2 ^ (prefixWord ++ tailWord_1816557).sum := by decide
  have hdescent : baseEnd_1816557 < baseStart_1816557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816574 : List Nat := [4, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1816574 : Nat := 118140960795 + 1816574 * 2 ^ 59
def prefixEnd_1816574 : Nat := 4983230072969 + 3 ^ 40 * 1816574 * 2
def baseEnd_1816574 : Nat := 138188978734915685862331

theorem tailTrace_1816574 : CollatzResearch.WordTrace tailWord_1816574 prefixEnd_1816574 138188978734915685862331 := by
  unfold tailWord_1816574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281987115108764873044097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44170597947246745989568517 8281987115108764873044097)
  ·
    refine ⟨6211490336331573654783073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8281987115108764873044097 6211490336331573654783073)
    ·
      refine ⟨4658617752248680241087305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6211490336331573654783073 4658617752248680241087305)
      ·
        refine ⟨3493963314186510180815479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4658617752248680241087305 3493963314186510180815479)
        ·
          refine ⟨5240944971279765271223219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493963314186510180815479 5240944971279765271223219)
          ·
            refine ⟨7861417456919647906834829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240944971279765271223219 7861417456919647906834829)
            ·
              refine ⟨2948031546344867965063061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7861417456919647906834829 2948031546344867965063061)
              ·
                refine ⟨138188978734915685862331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2948031546344867965063061 138188978734915685862331)
                ·
                  rfl

theorem cell21_1816574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1816574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816574 prefixEnd_1816574 := by exact prefixLift 1816574
  have htrace : WordTrace (prefixWord ++ tailWord_1816574) baseStart_1816574 baseEnd_1816574 := by
    simpa [prefixWord, tailWord_1816574, baseEnd_1816574] using wordTrace_append hprefix tailTrace_1816574
  have hstable : (prefixWord ++ tailWord_1816574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816574).length < 2 ^ (prefixWord ++ tailWord_1816574).sum := by decide
  have hdescent : baseEnd_1816574 < baseStart_1816574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816585 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_1816585 : Nat := 118140960795 + 1816585 * 2 ^ 59
def prefixEnd_1816585 : Nat := 4983230072969 + 3 ^ 40 * 1816585 * 2
def baseEnd_1816585 : Nat := 414569446554613482903637

theorem tailTrace_1816585 : CollatzResearch.WordTrace tailWord_1816585 prefixEnd_1816585 414569446554613482903637 := by
  unfold tailWord_1816585
  simp only [CollatzResearch.WordTrace]
  refine ⟨66256298123830267863003209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44170865415886845242002139 66256298123830267863003209)
  ·
    refine ⟨49692223592872700897252407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66256298123830267863003209 49692223592872700897252407)
    ·
      refine ⟨74538335389309051345878611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49692223592872700897252407 74538335389309051345878611)
      ·
        refine ⟨111807503083963577018817917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74538335389309051345878611 111807503083963577018817917)
        ·
          refine ⟨41927813656486341382056719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111807503083963577018817917 41927813656486341382056719)
          ·
            refine ⟨62891720484729512073085079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41927813656486341382056719 62891720484729512073085079)
            ·
              refine ⟨94337580727094268109627619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62891720484729512073085079 94337580727094268109627619)
              ·
                refine ⟨141506371090641402164441429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94337580727094268109627619 141506371090641402164441429)
                ·
                  refine ⟨414569446554613482903637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141506371090641402164441429 414569446554613482903637)
                  ·
                    rfl

theorem cell21_1816585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_1816585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816585 prefixEnd_1816585 := by exact prefixLift 1816585
  have htrace : WordTrace (prefixWord ++ tailWord_1816585) baseStart_1816585 baseEnd_1816585 := by
    simpa [prefixWord, tailWord_1816585, baseEnd_1816585] using wordTrace_append hprefix tailTrace_1816585
  have hstable : (prefixWord ++ tailWord_1816585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816585).length < 2 ^ (prefixWord ++ tailWord_1816585).sum := by decide
  have hdescent : baseEnd_1816585 < baseStart_1816585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816605 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1816605 : Nat := 118140960795 + 1816605 * 2 ^ 59
def prefixEnd_1816605 : Nat := 4983230072969 + 3 ^ 40 * 1816605 * 2
def baseEnd_1816605 : Nat := 414574010827097892570263

theorem tailTrace_1816605 : CollatzResearch.WordTrace tailWord_1816605 prefixEnd_1816605 414574010827097892570263 := by
  unfold tailWord_1816605
  simp only [CollatzResearch.WordTrace]
  refine ⟨66257027583757811278731269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44171351722505207519154179 66257027583757811278731269)
  ·
    refine ⟨12423192671954589614762113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66257027583757811278731269 12423192671954589614762113)
    ·
      refine ⟨9317394503965942211071585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12423192671954589614762113 9317394503965942211071585)
      ·
        refine ⟨6988045877974456658303689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9317394503965942211071585 6988045877974456658303689)
        ·
          refine ⟨5241034408480842493727767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6988045877974456658303689 5241034408480842493727767)
          ·
            refine ⟨7861551612721263740591651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241034408480842493727767 7861551612721263740591651)
            ·
              refine ⟨11792327419081895610887477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861551612721263740591651 11792327419081895610887477)
              ·
                refine ⟨1105530695538927713520701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11792327419081895610887477 1105530695538927713520701)
                ·
                  refine ⟨414574010827097892570263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105530695538927713520701 414574010827097892570263)
                  ·
                    rfl

theorem cell21_1816605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1816605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816605 prefixEnd_1816605 := by exact prefixLift 1816605
  have htrace : WordTrace (prefixWord ++ tailWord_1816605) baseStart_1816605 baseEnd_1816605 := by
    simpa [prefixWord, tailWord_1816605, baseEnd_1816605] using wordTrace_append hprefix tailTrace_1816605
  have hstable : (prefixWord ++ tailWord_1816605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816605).length < 2 ^ (prefixWord ++ tailWord_1816605).sum := by decide
  have hdescent : baseEnd_1816605 < baseStart_1816605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816647 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_1816647 : Nat := 118140960795 + 1816647 * 2 ^ 59
def prefixEnd_1816647 : Nat := 4983230072969 + 3 ^ 40 * 1816647 * 2
def baseEnd_1816647 : Nat := 414583595799315152870177

theorem tailTrace_1816647 : CollatzResearch.WordTrace tailWord_1816647 prefixEnd_1816647 414583595799315152870177 := by
  unfold tailWord_1816647
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258559449605652451760195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44172372966403768301173463 66258559449605652451760195)
  ·
    refine ⟨99387839174408478677640293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66258559449605652451760195 99387839174408478677640293)
    ·
      refine ⟨18635219845201589752057555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99387839174408478677640293 18635219845201589752057555)
      ·
        refine ⟨27952829767802384628086333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635219845201589752057555 27952829767802384628086333)
        ·
          refine ⟨10482311162925894235532375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27952829767802384628086333 10482311162925894235532375)
          ·
            refine ⟨15723466744388841353298563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482311162925894235532375 15723466744388841353298563)
            ·
              refine ⟨23585200116583262029947845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723466744388841353298563 23585200116583262029947845)
              ·
                refine ⟨4422225021859361630615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23585200116583262029947845 4422225021859361630615221)
                ·
                  refine ⟨414583595799315152870177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4422225021859361630615221 414583595799315152870177)
                  ·
                    rfl

theorem cell21_1816647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_1816647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816647 prefixEnd_1816647 := by exact prefixLift 1816647
  have htrace : WordTrace (prefixWord ++ tailWord_1816647) baseStart_1816647 baseEnd_1816647 := by
    simpa [prefixWord, tailWord_1816647, baseEnd_1816647] using wordTrace_append hprefix tailTrace_1816647
  have hstable : (prefixWord ++ tailWord_1816647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816647).length < 2 ^ (prefixWord ++ tailWord_1816647).sum := by decide
  have hdescent : baseEnd_1816647 < baseStart_1816647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816681 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 3]
def baseStart_1816681 : Nat := 118140960795 + 1816681 * 2 ^ 59
def prefixEnd_1816681 : Nat := 4983230072969 + 3 ^ 40 * 1816681 * 2
def baseEnd_1816681 : Nat := 414591355062538649303441

theorem tailTrace_1816681 : CollatzResearch.WordTrace tailWord_1816681 prefixEnd_1816681 414591355062538649303441 := by
  unfold tailWord_1816681
  simp only [CollatzResearch.WordTrace]
  refine ⟨66259799531482476258497897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44173199687654984172331931 66259799531482476258497897)
  ·
    refine ⟨49694849648611857193873423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66259799531482476258497897 49694849648611857193873423)
    ·
      refine ⟨74542274472917785790810135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49694849648611857193873423 74542274472917785790810135)
      ·
        refine ⟨111813411709376678686215203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74542274472917785790810135 111813411709376678686215203)
        ·
          refine ⟨167720117564065018029322805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111813411709376678686215203 167720117564065018029322805)
          ·
            refine ⟨15723761021631095440249013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167720117564065018029322805 15723761021631095440249013)
            ·
              refine ⟨1474102595777915197523345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15723761021631095440249013 1474102595777915197523345)
              ·
                refine ⟨1105576946833436398142509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474102595777915197523345 1105576946833436398142509)
                ·
                  refine ⟨414591355062538649303441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105576946833436398142509 414591355062538649303441)
                  ·
                    rfl

theorem cell21_1816681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_1816681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816681 prefixEnd_1816681 := by exact prefixLift 1816681
  have htrace : WordTrace (prefixWord ++ tailWord_1816681) baseStart_1816681 baseEnd_1816681 := by
    simpa [prefixWord, tailWord_1816681, baseEnd_1816681] using wordTrace_append hprefix tailTrace_1816681
  have hstable : (prefixWord ++ tailWord_1816681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816681).length < 2 ^ (prefixWord ++ tailWord_1816681).sum := by decide
  have hdescent : baseEnd_1816681 < baseStart_1816681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816695 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 4]
def baseStart_1816695 : Nat := 118140960795 + 1816695 * 2 ^ 59
def prefixEnd_1816695 : Nat := 4983230072969 + 3 ^ 40 * 1816695 * 2
def baseEnd_1816695 : Nat := 414594550053277736070079

theorem tailTrace_1816695 : CollatzResearch.WordTrace tailWord_1816695 prefixEnd_1816695 414594550053277736070079 := by
  unfold tailWord_1816695
  simp only [CollatzResearch.WordTrace]
  refine ⟨66260310153431756649507539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44173540102287837766338359 66260310153431756649507539)
  ·
    refine ⟨99390465230147634974261309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66260310153431756649507539 99390465230147634974261309)
    ·
      refine ⟨37271424461305363115347991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99390465230147634974261309 37271424461305363115347991)
      ·
        refine ⟨55907136691958044673021987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37271424461305363115347991 55907136691958044673021987)
        ·
          refine ⟨83860705037937067009532981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55907136691958044673021987 83860705037937067009532981)
          ·
            refine ⟨7861941097306600032143717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83860705037937067009532981 7861941097306600032143717)
            ·
              refine ⟨1474113955744987506026947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7861941097306600032143717 1474113955744987506026947)
              ·
                refine ⟨2211170933617481259040421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474113955744987506026947 2211170933617481259040421)
                ·
                  refine ⟨414594550053277736070079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211170933617481259040421 414594550053277736070079)
                  ·
                    rfl

theorem cell21_1816695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 4].length) (baseStart_1816695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816695 prefixEnd_1816695 := by exact prefixLift 1816695
  have htrace : WordTrace (prefixWord ++ tailWord_1816695) baseStart_1816695 baseEnd_1816695 := by
    simpa [prefixWord, tailWord_1816695, baseEnd_1816695] using wordTrace_append hprefix tailTrace_1816695
  have hstable : (prefixWord ++ tailWord_1816695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816695).length < 2 ^ (prefixWord ++ tailWord_1816695).sum := by decide
  have hdescent : baseEnd_1816695 < baseStart_1816695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816743 : List Nat := [1, 1, 6, 2, 3, 1, 1, 6]
def baseStart_1816743 : Nat := 118140960795 + 1816743 * 2 ^ 59
def prefixEnd_1816743 : Nat := 4983230072969 + 3 ^ 40 * 1816743 * 2
def baseEnd_1816743 : Nat := 138201834769080106423327

theorem tailTrace_1816743 : CollatzResearch.WordTrace tailWord_1816743 prefixEnd_1816743 138201834769080106423327 := by
  unfold tailWord_1816743
  simp only [CollatzResearch.WordTrace]
  refine ⟨66262060857257860847254883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44174707238171907231503255 66262060857257860847254883)
  ·
    refine ⟨99393091285886791270882325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66262060857257860847254883 99393091285886791270882325)
    ·
      refine ⟨4659051154025943340822609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99393091285886791270882325 4659051154025943340822609)
      ·
        refine ⟨3494288365519457505616957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4659051154025943340822609 3494288365519457505616957)
        ·
          refine ⟨1310358137069796564606359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3494288365519457505616957 1310358137069796564606359)
          ·
            refine ⟨1965537205604694846909539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310358137069796564606359 1965537205604694846909539)
            ·
              refine ⟨2948305808407042270364309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965537205604694846909539 2948305808407042270364309)
              ·
                refine ⟨138201834769080106423327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2948305808407042270364309 138201834769080106423327)
                ·
                  rfl

theorem cell21_1816743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 6].length) (baseStart_1816743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816743 prefixEnd_1816743 := by exact prefixLift 1816743
  have htrace : WordTrace (prefixWord ++ tailWord_1816743) baseStart_1816743 baseEnd_1816743 := by
    simpa [prefixWord, tailWord_1816743, baseEnd_1816743] using wordTrace_append hprefix tailTrace_1816743
  have hstable : (prefixWord ++ tailWord_1816743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816743).length < 2 ^ (prefixWord ++ tailWord_1816743).sum := by decide
  have hdescent : baseEnd_1816743 < baseStart_1816743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816754 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1816754 : Nat := 118140960795 + 1816754 * 2 ^ 59
def prefixEnd_1816754 : Nat := 4983230072969 + 3 ^ 40 * 1816754 * 2
def baseEnd_1816754 : Nat := 414608014657106744586625

theorem tailTrace_1816754 : CollatzResearch.WordTrace tailWord_1816754 prefixEnd_1816754 414608014657106744586625 := by
  unfold tailWord_1816754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565615515054502431476329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44174974706812006483936877 16565615515054502431476329)
  ·
    refine ⟨12424211636290876823607247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16565615515054502431476329 12424211636290876823607247)
    ·
      refine ⟨18636317454436315235410871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12424211636290876823607247 18636317454436315235410871)
      ·
        refine ⟨27954476181654472853116307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18636317454436315235410871 27954476181654472853116307)
        ·
          refine ⟨41931714272481709279674461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27954476181654472853116307 41931714272481709279674461)
          ·
            refine ⟨15724392852180640979877923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41931714272481709279674461 15724392852180640979877923)
            ·
              refine ⟨23586589278270961469816885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724392852180640979877923 23586589278270961469816885)
              ·
                refine ⟨2211242744837902637795333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23586589278270961469816885 2211242744837902637795333)
                ·
                  refine ⟨414608014657106744586625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211242744837902637795333 414608014657106744586625)
                  ·
                    rfl

theorem cell21_1816754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1816754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816754 prefixEnd_1816754 := by exact prefixLift 1816754
  have htrace : WordTrace (prefixWord ++ tailWord_1816754) baseStart_1816754 baseEnd_1816754 := by
    simpa [prefixWord, tailWord_1816754, baseEnd_1816754] using wordTrace_append hprefix tailTrace_1816754
  have hstable : (prefixWord ++ tailWord_1816754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816754).length < 2 ^ (prefixWord ++ tailWord_1816754).sum := by decide
  have hdescent : baseEnd_1816754 < baseStart_1816754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816757 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1816757 : Nat := 118140960795 + 1816757 * 2 ^ 59
def prefixEnd_1816757 : Nat := 4983230072969 + 3 ^ 40 * 1816757 * 2
def baseEnd_1816757 : Nat := 414608699297979406036619

theorem tailTrace_1816757 : CollatzResearch.WordTrace tailWord_1816757 prefixEnd_1816757 414608699297979406036619 := by
  unfold tailWord_1816757
  simp only [CollatzResearch.WordTrace]
  refine ⟨66262571479207141238264525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44175047652804760825509683 66262571479207141238264525)
  ·
    refine ⟨24848464304702677964349197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66262571479207141238264525 24848464304702677964349197)
    ·
      refine ⟨9318174114263504236630949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24848464304702677964349197 9318174114263504236630949)
      ·
        refine ⟨1747157646424407044368303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9318174114263504236630949 1747157646424407044368303)
        ·
          refine ⟨2620736469636610566552455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747157646424407044368303 2620736469636610566552455)
          ·
            refine ⟨3931104704454915849828683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620736469636610566552455 3931104704454915849828683)
            ·
              refine ⟨5896657056682373774743025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931104704454915849828683 5896657056682373774743025)
              ·
                refine ⟨4422492792511780331057269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5896657056682373774743025 4422492792511780331057269)
                ·
                  refine ⟨414608699297979406036619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4422492792511780331057269 414608699297979406036619)
                  ·
                    rfl

theorem cell21_1816757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1816757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816757 prefixEnd_1816757 := by exact prefixLift 1816757
  have htrace : WordTrace (prefixWord ++ tailWord_1816757) baseStart_1816757 baseEnd_1816757 := by
    simpa [prefixWord, tailWord_1816757, baseEnd_1816757] using wordTrace_append hprefix tailTrace_1816757
  have hstable : (prefixWord ++ tailWord_1816757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816757).length < 2 ^ (prefixWord ++ tailWord_1816757).sum := by decide
  have hdescent : baseEnd_1816757 < baseStart_1816757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816830 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1816830 : Nat := 118140960795 + 1816830 * 2 ^ 59
def prefixEnd_1816830 : Nat := 4983230072969 + 3 ^ 40 * 1816830 * 2
def baseEnd_1816830 : Nat := 414625358892547501319803

theorem tailTrace_1816830 : CollatzResearch.WordTrace tailWord_1816830 prefixEnd_1816830 414625358892547501319803 := by
  unfold tailWord_1816830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283154250992834338208993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44176822671961783137114629 8283154250992834338208993)
  ·
    refine ⟨6212365688244625753656745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8283154250992834338208993 6212365688244625753656745)
    ·
      refine ⟨4659274266183469315242559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6212365688244625753656745 4659274266183469315242559)
      ·
        refine ⟨6988911399275203972863839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659274266183469315242559 6988911399275203972863839)
        ·
          refine ⟨10483367098912805959295759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988911399275203972863839 10483367098912805959295759)
          ·
            refine ⟨15725050648369208938943639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10483367098912805959295759 15725050648369208938943639)
            ·
              refine ⟨23587575972553813408415459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15725050648369208938943639 23587575972553813408415459)
              ·
                refine ⟨35381363958830720112623189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23587575972553813408415459 35381363958830720112623189)
                ·
                  refine ⟨414625358892547501319803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35381363958830720112623189 414625358892547501319803)
                  ·
                    rfl

theorem cell21_1816830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1816830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816830 prefixEnd_1816830 := by exact prefixLift 1816830
  have htrace : WordTrace (prefixWord ++ tailWord_1816830) baseStart_1816830 baseEnd_1816830 := by
    simpa [prefixWord, tailWord_1816830, baseEnd_1816830] using wordTrace_append hprefix tailTrace_1816830
  have hstable : (prefixWord ++ tailWord_1816830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816830).length < 2 ^ (prefixWord ++ tailWord_1816830).sum := by decide
  have hdescent : baseEnd_1816830 < baseStart_1816830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816864 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_1816864 : Nat := 118140960795 + 1816864 * 2 ^ 59
def prefixEnd_1816864 : Nat := 4983230072969 + 3 ^ 40 * 1816864 * 2
def baseEnd_1816864 : Nat := 414633118155770997753067

theorem tailTrace_1816864 : CollatzResearch.WordTrace tailWord_1816864 prefixEnd_1816864 414633118155770997753067 := by
  unfold tailWord_1816864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133237044909749256204823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44177649393212999008273097 33133237044909749256204823)
  ·
    refine ⟨49699855567364623884307235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33133237044909749256204823 49699855567364623884307235)
    ·
      refine ⟨74549783351046935826460853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49699855567364623884307235 74549783351046935826460853)
      ·
        refine ⟨6989042189160650233730705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74549783351046935826460853 6989042189160650233730705)
        ·
          refine ⟨5241781641870487675298029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6989042189160650233730705 5241781641870487675298029)
          ·
            refine ⟨1965668115701432878236761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5241781641870487675298029 1965668115701432878236761)
            ·
              refine ⟨1474251086776074658677571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965668115701432878236761 1474251086776074658677571)
              ·
                refine ⟨2211376630164111988016357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474251086776074658677571 2211376630164111988016357)
                ·
                  refine ⟨414633118155770997753067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211376630164111988016357 414633118155770997753067)
                  ·
                    rfl

theorem cell21_1816864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_1816864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816864 prefixEnd_1816864 := by exact prefixLift 1816864
  have htrace : WordTrace (prefixWord ++ tailWord_1816864) baseStart_1816864 baseEnd_1816864 := by
    simpa [prefixWord, tailWord_1816864, baseEnd_1816864] using wordTrace_append hprefix tailTrace_1816864
  have hstable : (prefixWord ++ tailWord_1816864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816864).length < 2 ^ (prefixWord ++ tailWord_1816864).sum := by decide
  have hdescent : baseEnd_1816864 < baseStart_1816864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
