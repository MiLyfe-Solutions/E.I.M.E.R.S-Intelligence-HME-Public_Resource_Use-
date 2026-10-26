import V185TrunkScan23Chunk0525

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3108884 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3108884 : Nat := 118140960795 + 3108884 * 2 ^ 59
def prefixEnd_3108884 : Nat := 4983230072969 + 3 ^ 40 * 3108884 * 2
def baseEnd_3108884 : Nat := 1596351791072519710752509

theorem tailTrace_3108884 : CollatzResearch.WordTrace tailWord_3108884 prefixEnd_3108884 1596351791072519710752509 := by
  unfold tailWord_3108884
  simp only [CollatzResearch.WordTrace]
  refine ⟨56695157434525848980406853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75593543246034465307209137 56695157434525848980406853)
  ·
    refine ⟨10630342018973596683826285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56695157434525848980406853 10630342018973596683826285)
    ·
      refine ⟨3986378257115098756434857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10630342018973596683826285 3986378257115098756434857)
      ·
        refine ⟨2989783692836324067326143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3986378257115098756434857 2989783692836324067326143)
        ·
          refine ⟨4484675539254486100989215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989783692836324067326143 4484675539254486100989215)
          ·
            refine ⟨6727013308881729151483823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484675539254486100989215 6727013308881729151483823)
            ·
              refine ⟨10090519963322593727225735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727013308881729151483823 10090519963322593727225735)
              ·
                refine ⟨15135779944983890590838603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090519963322593727225735 15135779944983890590838603)
                ·
                  refine ⟨22703669917475835886257905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15135779944983890590838603 22703669917475835886257905)
                  ·
                    refine ⟨17027752438106876914693429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22703669917475835886257905 17027752438106876914693429)
                    ·
                      refine ⟨1596351791072519710752509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17027752438106876914693429 1596351791072519710752509)
                      ·
                        rfl

theorem cell23_3108884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3108884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108884 prefixEnd_3108884 := by exact prefixLift 3108884
  have htrace : WordTrace (prefixWord ++ tailWord_3108884) baseStart_3108884 baseEnd_3108884 := by
    simpa [prefixWord, tailWord_3108884, baseEnd_3108884] using wordTrace_append hprefix tailTrace_3108884
  have hstable : (prefixWord ++ tailWord_3108884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108884).length < 2 ^ (prefixWord ++ tailWord_3108884).sum := by decide
  have hdescent : baseEnd_3108884 < baseStart_3108884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108934 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3108934 : Nat := 118140960795 + 3108934 * 2 ^ 59
def prefixEnd_3108934 : Nat := 4983230072969 + 3 ^ 40 * 3108934 * 2
def baseEnd_3108934 : Nat := 177375273900582723903031

theorem tailTrace_3108934 : CollatzResearch.WordTrace tailWord_3108934 prefixEnd_3108934 177375273900582723903031 := by
  unfold tailWord_3108934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543504328714704890629183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75594759012580371000089237 3543504328714704890629183)
  ·
    refine ⟨5315256493072057335943775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543504328714704890629183 5315256493072057335943775)
    ·
      refine ⟨7972884739608086003915663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5315256493072057335943775 7972884739608086003915663)
      ·
        refine ⟨11959327109412129005873495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972884739608086003915663 11959327109412129005873495)
        ·
          refine ⟨17938990664118193508810243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11959327109412129005873495 17938990664118193508810243)
          ·
            refine ⟨26908485996177290263215365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17938990664118193508810243 26908485996177290263215365)
            ·
              refine ⟨5045341124283241924352881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26908485996177290263215365 5045341124283241924352881)
              ·
                refine ⟨3784005843212431443264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045341124283241924352881 3784005843212431443264661)
                ·
                  refine ⟨177375273900582723903031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784005843212431443264661 177375273900582723903031)
                  ·
                    rfl

theorem cell23_3108934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3108934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108934 prefixEnd_3108934 := by exact prefixLift 3108934
  have htrace : WordTrace (prefixWord ++ tailWord_3108934) baseStart_3108934 baseEnd_3108934 := by
    simpa [prefixWord, tailWord_3108934, baseEnd_3108934] using wordTrace_append hprefix tailTrace_3108934
  have hstable : (prefixWord ++ tailWord_3108934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108934).length < 2 ^ (prefixWord ++ tailWord_3108934).sum := by decide
  have hdescent : baseEnd_3108934 < baseStart_3108934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108937 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 2, 3, 2]
def baseStart_3108937 : Nat := 118140960795 + 3108937 * 2 ^ 59
def prefixEnd_3108937 : Nat := 4983230072969 + 3 ^ 40 * 3108937 * 2
def baseEnd_3108937 : Nat := 1596379005547208003389765

theorem tailTrace_3108937 : CollatzResearch.WordTrace tailWord_3108937 prefixEnd_3108937 1596379005547208003389765 := by
  unfold tailWord_3108937
  simp only [CollatzResearch.WordTrace]
  refine ⟨113392247937859688012493065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75594831958573125341662043 113392247937859688012493065)
  ·
    refine ⟨85044185953394766009369799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113392247937859688012493065 85044185953394766009369799)
    ·
      refine ⟨127566278930092149014054699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85044185953394766009369799 127566278930092149014054699)
      ·
        refine ⟨191349418395138223521082049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127566278930092149014054699 191349418395138223521082049)
        ·
          refine ⟨143512063796353667640811537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191349418395138223521082049 143512063796353667640811537)
          ·
            refine ⟨107634047847265250730608653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143512063796353667640811537 107634047847265250730608653)
            ·
              refine ⟨40362767942724469023978245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107634047847265250730608653 40362767942724469023978245)
              ·
                refine ⟨7568018989260837941995921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40362767942724469023978245 7568018989260837941995921)
                ·
                  refine ⟨5676014241945628456496941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7568018989260837941995921 5676014241945628456496941)
                  ·
                    refine ⟨2128505340729610671186353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5676014241945628456496941 2128505340729610671186353)
                    ·
                      refine ⟨1596379005547208003389765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128505340729610671186353 1596379005547208003389765)
                      ·
                        rfl

theorem cell23_3108937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3, 2].length) (baseStart_3108937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108937 prefixEnd_3108937 := by exact prefixLift 3108937
  have htrace : WordTrace (prefixWord ++ tailWord_3108937) baseStart_3108937 baseEnd_3108937 := by
    simpa [prefixWord, tailWord_3108937, baseEnd_3108937] using wordTrace_append hprefix tailTrace_3108937
  have hstable : (prefixWord ++ tailWord_3108937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108937).length < 2 ^ (prefixWord ++ tailWord_3108937).sum := by decide
  have hdescent : baseEnd_3108937 < baseStart_3108937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108960 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_3108960 : Nat := 118140960795 + 3108960 * 2 ^ 59
def prefixEnd_3108960 : Nat := 4983230072969 + 3 ^ 40 * 3108960 * 2
def baseEnd_3108960 : Nat := 532130271867420471134053

theorem tailTrace_3108960 : CollatzResearch.WordTrace tailWord_3108960 prefixEnd_3108960 532130271867420471134053 := by
  unfold tailWord_3108960
  simp only [CollatzResearch.WordTrace]
  refine ⟨56696543408388181470290167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75595391211184241960386889 56696543408388181470290167)
  ·
    refine ⟨85044815112582272205435251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56696543408388181470290167 85044815112582272205435251)
    ·
      refine ⟨127567222668873408308152877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85044815112582272205435251 127567222668873408308152877)
      ·
        refine ⟨47837708500827528115557329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127567222668873408308152877 47837708500827528115557329)
        ·
          refine ⟨35878281375620646086667997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47837708500827528115557329 35878281375620646086667997)
          ·
            refine ⟨13454355515857742282500499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35878281375620646086667997 13454355515857742282500499)
            ·
              refine ⟨20181533273786613423750749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13454355515857742282500499 20181533273786613423750749)
              ·
                refine ⟨7568074977669980033906531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20181533273786613423750749 7568074977669980033906531)
                ·
                  refine ⟨11352112466504970050859797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7568074977669980033906531 11352112466504970050859797)
                  ·
                    refine ⟨532130271867420471134053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11352112466504970050859797 532130271867420471134053)
                    ·
                      rfl

theorem cell23_3108960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_3108960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108960 prefixEnd_3108960 := by exact prefixLift 3108960
  have htrace : WordTrace (prefixWord ++ tailWord_3108960) baseStart_3108960 baseEnd_3108960 := by
    simpa [prefixWord, tailWord_3108960, baseEnd_3108960] using wordTrace_append hprefix tailTrace_3108960
  have hstable : (prefixWord ++ tailWord_3108960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108960).length < 2 ^ (prefixWord ++ tailWord_3108960).sum := by decide
  have hdescent : baseEnd_3108960 < baseStart_3108960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108967 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3108967 : Nat := 118140960795 + 3108967 * 2 ^ 59
def prefixEnd_3108967 : Nat := 4983230072969 + 3 ^ 40 * 3108967 * 2
def baseEnd_3108967 : Nat := 1596394409966842886014627

theorem tailTrace_3108967 : CollatzResearch.WordTrace tailWord_3108967 prefixEnd_3108967 1596394409966842886014627 := by
  unfold tailWord_3108967
  simp only [CollatzResearch.WordTrace]
  refine ⟨113393342127751003136085155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75595561418500668757390103 113393342127751003136085155)
  ·
    refine ⟨170090013191626504704127733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113393342127751003136085155 170090013191626504704127733)
    ·
      refine ⟨15945938736714984816011975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170090013191626504704127733 15945938736714984816011975)
      ·
        refine ⟨23918908105072477224017963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15945938736714984816011975 23918908105072477224017963)
        ·
          refine ⟨35878362157608715836026945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23918908105072477224017963 35878362157608715836026945)
          ·
            refine ⟨26908771618206536877020209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35878362157608715836026945 26908771618206536877020209)
            ·
              refine ⟨20181578713654902657765157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26908771618206536877020209 20181578713654902657765157)
              ·
                refine ⟨3784046008810294248330967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20181578713654902657765157 3784046008810294248330967)
                ·
                  refine ⟨5676069013215441372496451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784046008810294248330967 5676069013215441372496451)
                  ·
                    refine ⟨8514103519823162058744677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5676069013215441372496451 8514103519823162058744677)
                    ·
                      refine ⟨1596394409966842886014627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8514103519823162058744677 1596394409966842886014627)
                      ·
                        rfl

theorem cell23_3108967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3108967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108967 prefixEnd_3108967 := by exact prefixLift 3108967
  have htrace : WordTrace (prefixWord ++ tailWord_3108967) baseStart_3108967 baseEnd_3108967 := by
    simpa [prefixWord, tailWord_3108967, baseEnd_3108967] using wordTrace_append hprefix tailTrace_3108967
  have hstable : (prefixWord ++ tailWord_3108967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108967).length < 2 ^ (prefixWord ++ tailWord_3108967).sum := by decide
  have hdescent : baseEnd_3108967 < baseStart_3108967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109001 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 1, 2, 2]
def baseStart_3109001 : Nat := 118140960795 + 3109001 * 2 ^ 59
def prefixEnd_3109001 : Nat := 4983230072969 + 3 ^ 40 * 3109001 * 2
def baseEnd_3109001 : Nat := 1596411868309095752989471

theorem tailTrace_3109001 : CollatzResearch.WordTrace tailWord_3109001 prefixEnd_3109001 1596411868309095752989471 := by
  unfold tailWord_3109001
  simp only [CollatzResearch.WordTrace]
  refine ⟨113394582209627826942822857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75596388139751884628548571 113394582209627826942822857)
  ·
    refine ⟨85045936657220870207117143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113394582209627826942822857 85045936657220870207117143)
    ·
      refine ⟨127568904985831305310675715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85045936657220870207117143 127568904985831305310675715)
      ·
        refine ⟨191353357478746957966013573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127568904985831305310675715 191353357478746957966013573)
        ·
          refine ⟨35878754527265054618627545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191353357478746957966013573 35878754527265054618627545)
          ·
            refine ⟨26909065895448790963970659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35878754527265054618627545 26909065895448790963970659)
            ·
              refine ⟨40363598843173186445955989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26909065895448790963970659 40363598843173186445955989)
              ·
                refine ⟨1892043695773743114654187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40363598843173186445955989 1892043695773743114654187)
                ·
                  refine ⟨2838065543660614671981281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892043695773743114654187 2838065543660614671981281)
                  ·
                    refine ⟨2128549157745461003985961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838065543660614671981281 2128549157745461003985961)
                    ·
                      refine ⟨1596411868309095752989471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128549157745461003985961 1596411868309095752989471)
                      ·
                        rfl

theorem cell23_3109001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 2, 2].length) (baseStart_3109001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109001 prefixEnd_3109001 := by exact prefixLift 3109001
  have htrace : WordTrace (prefixWord ++ tailWord_3109001) baseStart_3109001 baseEnd_3109001 := by
    simpa [prefixWord, tailWord_3109001, baseEnd_3109001] using wordTrace_append hprefix tailTrace_3109001
  have hstable : (prefixWord ++ tailWord_3109001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109001).length < 2 ^ (prefixWord ++ tailWord_3109001).sum := by decide
  have hdescent : baseEnd_3109001 < baseStart_3109001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109050 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3109050 : Nat := 118140960795 + 3109050 * 2 ^ 59
def prefixEnd_3109050 : Nat := 4983230072969 + 3 ^ 40 * 3109050 * 2
def baseEnd_3109050 : Nat := 532145676287055353758915

theorem tailTrace_3109050 : CollatzResearch.WordTrace tailWord_3109050 prefixEnd_3109050 532145676287055353758915 := by
  unfold tailWord_3109050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349092346612577077839151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75597579590966872207571069 28349092346612577077839151)
  ·
    refine ⟨42523638519918865616758727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28349092346612577077839151 42523638519918865616758727)
    ·
      refine ⟨63785457779878298425138091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42523638519918865616758727 63785457779878298425138091)
      ·
        refine ⟨95678186669817447637707137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63785457779878298425138091 95678186669817447637707137)
        ·
          refine ⟨71758640002363085728280353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95678186669817447637707137 71758640002363085728280353)
          ·
            refine ⟨53818980001772314296210265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71758640002363085728280353 53818980001772314296210265)
            ·
              refine ⟨40364235001329235722157699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53818980001772314296210265 40364235001329235722157699)
              ·
                refine ⟨60546352501993853583236549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40364235001329235722157699 60546352501993853583236549)
                ·
                  refine ⟨11352441094123847546856853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60546352501993853583236549 11352441094123847546856853)
                  ·
                    refine ⟨532145676287055353758915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11352441094123847546856853 532145676287055353758915)
                    ·
                      rfl

theorem cell23_3109050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3109050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109050 prefixEnd_3109050 := by exact prefixLift 3109050
  have htrace : WordTrace (prefixWord ++ tailWord_3109050) baseStart_3109050 baseEnd_3109050 := by
    simpa [prefixWord, tailWord_3109050, baseEnd_3109050] using wordTrace_append hprefix tailTrace_3109050
  have hstable : (prefixWord ++ tailWord_3109050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109050).length < 2 ^ (prefixWord ++ tailWord_3109050).sum := by decide
  have hdescent : baseEnd_3109050 < baseStart_3109050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109068 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3109068 : Nat := 118140960795 + 3109068 * 2 ^ 59
def prefixEnd_3109068 : Nat := 4983230072969 + 3 ^ 40 * 3109068 * 2
def baseEnd_3109068 : Nat := 1596446271512946990851663

theorem tailTrace_3109068 : CollatzResearch.WordTrace tailWord_3109068 prefixEnd_3109068 1596446271512946990851663 := by
  unfold tailWord_3109068
  simp only [CollatzResearch.WordTrace]
  refine ⟨56698512950192548692755929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75598017266923398257007905 56698512950192548692755929)
  ·
    refine ⟨42523884712644411519566947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56698512950192548692755929 42523884712644411519566947)
    ·
      refine ⟨63785827068966617279350421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42523884712644411519566947 63785827068966617279350421)
      ·
        refine ⟨2989960643857810184969551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63785827068966617279350421 2989960643857810184969551)
        ·
          refine ⟨4484940965786715277454327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989960643857810184969551 4484940965786715277454327)
          ·
            refine ⟨6727411448680072916181491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484940965786715277454327 6727411448680072916181491)
            ·
              refine ⟨10091117173020109374272237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727411448680072916181491 10091117173020109374272237)
              ·
                refine ⟨3784168939882541015352089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091117173020109374272237 3784168939882541015352089)
                ·
                  refine ⟨2838126704911905761514067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784168939882541015352089 2838126704911905761514067)
                  ·
                    refine ⟨4257190057367858642271101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2838126704911905761514067 4257190057367858642271101)
                    ·
                      refine ⟨1596446271512946990851663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4257190057367858642271101 1596446271512946990851663)
                      ·
                        rfl

theorem cell23_3109068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3109068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109068 prefixEnd_3109068 := by exact prefixLift 3109068
  have htrace : WordTrace (prefixWord ++ tailWord_3109068) baseStart_3109068 baseEnd_3109068 := by
    simpa [prefixWord, tailWord_3109068, baseEnd_3109068] using wordTrace_append hprefix tailTrace_3109068
  have hstable : (prefixWord ++ tailWord_3109068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109068).length < 2 ^ (prefixWord ++ tailWord_3109068).sum := by decide
  have hdescent : baseEnd_3109068 < baseStart_3109068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109078 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3109078 : Nat := 118140960795 + 3109078 * 2 ^ 59
def prefixEnd_3109078 : Nat := 4983230072969 + 3 ^ 40 * 3109078 * 2
def baseEnd_3109078 : Nat := 1596451406319491951726617

theorem tailTrace_3109078 : CollatzResearch.WordTrace tailWord_3109078 prefixEnd_3109078 1596451406319491951726617 := by
  unfold tailWord_3109078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7087336914396804318335993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75598260420232579395583925 7087336914396804318335993)
  ·
    refine ⟨5315502685797603238751995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7087336914396804318335993 5315502685797603238751995)
    ·
      refine ⟨7973254028696404858127993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5315502685797603238751995 7973254028696404858127993)
      ·
        refine ⟨5979940521522303643595995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7973254028696404858127993 5979940521522303643595995)
        ·
          refine ⟨8969910782283455465393993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979940521522303643595995 8969910782283455465393993)
          ·
            refine ⟨6727433086712591599045495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969910782283455465393993 6727433086712591599045495)
            ·
              refine ⟨10091149630068887398568243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727433086712591599045495 10091149630068887398568243)
              ·
                refine ⟨15136724445103331097852365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10091149630068887398568243 15136724445103331097852365)
                ·
                  refine ⟨5676271666913749161694637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15136724445103331097852365 5676271666913749161694637)
                  ·
                    refine ⟨2128601875092655935635489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5676271666913749161694637 2128601875092655935635489)
                    ·
                      refine ⟨1596451406319491951726617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128601875092655935635489 1596451406319491951726617)
                      ·
                        rfl

theorem cell23_3109078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3109078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109078 prefixEnd_3109078 := by exact prefixLift 3109078
  have htrace : WordTrace (prefixWord ++ tailWord_3109078) baseStart_3109078 baseEnd_3109078 := by
    simpa [prefixWord, tailWord_3109078, baseEnd_3109078] using wordTrace_append hprefix tailTrace_3109078
  have hstable : (prefixWord ++ tailWord_3109078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109078).length < 2 ^ (prefixWord ++ tailWord_3109078).sum := by decide
  have hdescent : baseEnd_3109078 < baseStart_3109078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109107 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3]
def baseStart_3109107 : Nat := 118140960795 + 3109107 * 2 ^ 59
def prefixEnd_3109107 : Nat := 4983230072969 + 3 ^ 40 * 3109107 * 2
def baseEnd_3109107 : Nat := 1596466297258472338263983

theorem tailTrace_3109107 : CollatzResearch.WordTrace tailWord_3109107 prefixEnd_3109107 1596466297258472338263983 := by
  unfold tailWord_3109107
  simp only [CollatzResearch.WordTrace]
  refine ⟨113398448347243807046181575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75598965564829204697454383 113398448347243807046181575)
  ·
    refine ⟨170097672520865710569272363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113398448347243807046181575 170097672520865710569272363)
    ·
      refine ⟨255146508781298565853908545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170097672520865710569272363 255146508781298565853908545)
      ·
        refine ⟨191359881585973924390431409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255146508781298565853908545 191359881585973924390431409)
        ·
          refine ⟨143519911189480443292823557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191359881585973924390431409 143519911189480443292823557)
          ·
            refine ⟨26909983348027583117404417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143519911189480443292823557 26909983348027583117404417)
            ·
              refine ⟨20182487511020687338053313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26909983348027583117404417 20182487511020687338053313)
              ·
                refine ⟨15136865633265515503539985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20182487511020687338053313 15136865633265515503539985)
                ·
                  refine ⟨11352649224949136627654989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15136865633265515503539985 11352649224949136627654989)
                  ·
                    refine ⟨4257243459355926235370621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11352649224949136627654989 4257243459355926235370621)
                    ·
                      refine ⟨1596466297258472338263983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4257243459355926235370621 1596466297258472338263983)
                      ·
                        rfl

theorem cell23_3109107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_3109107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109107 prefixEnd_3109107 := by exact prefixLift 3109107
  have htrace : WordTrace (prefixWord ++ tailWord_3109107) baseStart_3109107 baseEnd_3109107 := by
    simpa [prefixWord, tailWord_3109107, baseEnd_3109107] using wordTrace_append hprefix tailTrace_3109107
  have hstable : (prefixWord ++ tailWord_3109107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109107).length < 2 ^ (prefixWord ++ tailWord_3109107).sum := by decide
  have hdescent : baseEnd_3109107 < baseStart_3109107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109114 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_3109114 : Nat := 118140960795 + 3109114 * 2 ^ 59
def prefixEnd_3109114 : Nat := 4983230072969 + 3 ^ 40 * 3109114 * 2
def baseEnd_3109114 : Nat := 177385543513672645652939

theorem tailTrace_3109114 : CollatzResearch.WordTrace tailWord_3109114 prefixEnd_3109114 177385543513672645652939 := by
  unfold tailWord_3109114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349675914554611810421599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75599135772145631494457597 28349675914554611810421599)
  ·
    refine ⟨42524513871831917715632399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28349675914554611810421599 42524513871831917715632399)
    ·
      refine ⟨63786770807747876573448599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42524513871831917715632399 63786770807747876573448599)
      ·
        refine ⟨95680156211621814860172899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63786770807747876573448599 95680156211621814860172899)
        ·
          refine ⟨143520234317432722290259349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95680156211621814860172899 143520234317432722290259349)
          ·
            refine ⟨6727510983629658857355907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143520234317432722290259349 6727510983629658857355907)
            ·
              refine ⟨10091266475444488286033861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727510983629658857355907 10091266475444488286033861)
              ·
                refine ⟨1892112464145841553631349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10091266475444488286033861 1892112464145841553631349)
                ·
                  refine ⟨177385543513672645652939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1892112464145841553631349 177385543513672645652939)
                  ·
                    rfl

theorem cell23_3109114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_3109114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109114 prefixEnd_3109114 := by exact prefixLift 3109114
  have htrace : WordTrace (prefixWord ++ tailWord_3109114) baseStart_3109114 baseEnd_3109114 := by
    simpa [prefixWord, tailWord_3109114, baseEnd_3109114] using wordTrace_append hprefix tailTrace_3109114
  have hstable : (prefixWord ++ tailWord_3109114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109114).length < 2 ^ (prefixWord ++ tailWord_3109114).sum := by decide
  have hdescent : baseEnd_3109114 < baseStart_3109114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109134 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_3109134 : Nat := 118140960795 + 3109134 * 2 ^ 59
def prefixEnd_3109134 : Nat := 4983230072969 + 3 ^ 40 * 3109134 * 2
def baseEnd_3109134 : Nat := 1596480161236143732626359

theorem tailTrace_3109134 : CollatzResearch.WordTrace tailWord_3109134 prefixEnd_3109134 1596480161236143732626359 := by
  unfold tailWord_3109134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174929139768248832176807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75599622078763993771609637 14174929139768248832176807)
  ·
    refine ⟨21262393709652373248265211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14174929139768248832176807 21262393709652373248265211)
    ·
      refine ⟨31893590564478559872397817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21262393709652373248265211 31893590564478559872397817)
      ·
        refine ⟨23920192923358919904298363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31893590564478559872397817 23920192923358919904298363)
        ·
          refine ⟨35880289385038379856447545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23920192923358919904298363 35880289385038379856447545)
          ·
            refine ⟨26910217038778784892335659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35880289385038379856447545 26910217038778784892335659)
            ·
              refine ⟨40365325558168177338503489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26910217038778784892335659 40365325558168177338503489)
              ·
                refine ⟨30273994168626133003877617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40365325558168177338503489 30273994168626133003877617)
                ·
                  refine ⟨22705495626469599752908213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30273994168626133003877617 22705495626469599752908213)
                  ·
                    refine ⟨2128640214981524976835145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22705495626469599752908213 2128640214981524976835145)
                    ·
                      refine ⟨1596480161236143732626359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128640214981524976835145 1596480161236143732626359)
                      ·
                        rfl

theorem cell23_3109134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_3109134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109134 prefixEnd_3109134 := by exact prefixLift 3109134
  have htrace : WordTrace (prefixWord ++ tailWord_3109134) baseStart_3109134 baseEnd_3109134 := by
    simpa [prefixWord, tailWord_3109134, baseEnd_3109134] using wordTrace_append hprefix tailTrace_3109134
  have hstable : (prefixWord ++ tailWord_3109134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109134).length < 2 ^ (prefixWord ++ tailWord_3109134).sum := by decide
  have hdescent : baseEnd_3109134 < baseStart_3109134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109159 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3109159 : Nat := 118140960795 + 3109159 * 2 ^ 59
def prefixEnd_3109159 : Nat := 4983230072969 + 3 ^ 40 * 3109159 * 2
def baseEnd_3109159 : Nat := 1596492998252506134813745

theorem tailTrace_3109159 : CollatzResearch.WordTrace tailWord_3109159 prefixEnd_3109159 1596492998252506134813745 := by
  unfold tailWord_3109159
  simp only [CollatzResearch.WordTrace]
  refine ⟨113400344943055419927074531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75600229962036946618049687 113400344943055419927074531)
  ·
    refine ⟨170100517414583129890611797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113400344943055419927074531 170100517414583129890611797)
    ·
      refine ⟨1993365438452146053405607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 170100517414583129890611797 1993365438452146053405607)
      ·
        refine ⟨2990048157678219080108411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993365438452146053405607 2990048157678219080108411)
        ·
          refine ⟨4485072236517328620162617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990048157678219080108411 4485072236517328620162617)
          ·
            refine ⟨3363804177387996465121963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4485072236517328620162617 3363804177387996465121963)
            ·
              refine ⟨5045706266081994697682945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363804177387996465121963 5045706266081994697682945)
              ·
                refine ⟨3784279699561496023262209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045706266081994697682945 3784279699561496023262209)
                ·
                  refine ⟨2838209774671122017446657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784279699561496023262209 2838209774671122017446657)
                  ·
                    refine ⟨2128657331003341513084993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838209774671122017446657 2128657331003341513084993)
                    ·
                      refine ⟨1596492998252506134813745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128657331003341513084993 1596492998252506134813745)
                      ·
                        rfl

theorem cell23_3109159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3109159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109159 prefixEnd_3109159 := by exact prefixLift 3109159
  have htrace : WordTrace (prefixWord ++ tailWord_3109159) baseStart_3109159 baseEnd_3109159 := by
    simpa [prefixWord, tailWord_3109159, baseEnd_3109159] using wordTrace_append hprefix tailTrace_3109159
  have hstable : (prefixWord ++ tailWord_3109159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109159).length < 2 ^ (prefixWord ++ tailWord_3109159).sum := by decide
  have hdescent : baseEnd_3109159 < baseStart_3109159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109164 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_3109164 : Nat := 118140960795 + 3109164 * 2 ^ 59
def prefixEnd_3109164 : Nat := 4983230072969 + 3 ^ 40 * 3109164 * 2
def baseEnd_3109164 : Nat := 1596495565655778615251221

theorem tailTrace_3109164 : CollatzResearch.WordTrace tailWord_3109164 prefixEnd_3109164 1596495565655778615251221 := by
  unfold tailWord_3109164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56700263654018652890503273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75600351538691537187337697 56700263654018652890503273)
  ·
    refine ⟨42525197740513989667877455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56700263654018652890503273 42525197740513989667877455)
    ·
      refine ⟨63787796610770984501816183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42525197740513989667877455 63787796610770984501816183)
      ·
        refine ⟨95681694916156476752724275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63787796610770984501816183 95681694916156476752724275)
        ·
          refine ⟨143522542374234715129086413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95681694916156476752724275 143522542374234715129086413)
          ·
            refine ⟨53820953390338018173407405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143522542374234715129086413 53820953390338018173407405)
            ·
              refine ⟨20182857521376756815027777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53820953390338018173407405 20182857521376756815027777)
              ·
                refine ⟨15137143141032567611270833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20182857521376756815027777 15137143141032567611270833)
                ·
                  refine ⟨11352857355774425708453125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15137143141032567611270833 11352857355774425708453125)
                  ·
                    refine ⟨2128660754207704820334961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11352857355774425708453125 2128660754207704820334961)
                    ·
                      refine ⟨1596495565655778615251221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128660754207704820334961 1596495565655778615251221)
                      ·
                        rfl

theorem cell23_3109164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_3109164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109164 prefixEnd_3109164 := by exact prefixLift 3109164
  have htrace : WordTrace (prefixWord ++ tailWord_3109164) baseStart_3109164 baseEnd_3109164 := by
    simpa [prefixWord, tailWord_3109164, baseEnd_3109164] using wordTrace_append hprefix tailTrace_3109164
  have hstable : (prefixWord ++ tailWord_3109164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109164).length < 2 ^ (prefixWord ++ tailWord_3109164).sum := by decide
  have hdescent : baseEnd_3109164 < baseStart_3109164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109187 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 6]
def baseStart_3109187 : Nat := 118140960795 + 3109187 * 2 ^ 59
def prefixEnd_3109187 : Nat := 4983230072969 + 3 ^ 40 * 3109187 * 2
def baseEnd_3109187 : Nat := 177389708412314669473735

theorem tailTrace_3109187 : CollatzResearch.WordTrace tailWord_3109187 prefixEnd_3109187 177389708412314669473735 := by
  unfold tailWord_3109187
  simp only [CollatzResearch.WordTrace]
  refine ⟨113401366186953980709093815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75600910791302653806062543 113401366186953980709093815)
  ·
    refine ⟨170102049280430971063640723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113401366186953980709093815 170102049280430971063640723)
    ·
      refine ⟨255153073920646456595461085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170102049280430971063640723 255153073920646456595461085)
      ·
        refine ⟨95682402720242421223297907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255153073920646456595461085 95682402720242421223297907)
        ·
          refine ⟨143523604080363631834946861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95682402720242421223297907 143523604080363631834946861)
          ·
            refine ⟨53821351530136361938105073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143523604080363631834946861 53821351530136361938105073)
            ·
              refine ⟨40366013647602271453578805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53821351530136361938105073 40366013647602271453578805)
              ·
                refine ⟨3784313779462712948773013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40366013647602271453578805 3784313779462712948773013)
                ·
                  refine ⟨177389708412314669473735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784313779462712948773013 177389708412314669473735)
                  ·
                    rfl

theorem cell23_3109187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6].length) (baseStart_3109187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109187 prefixEnd_3109187 := by exact prefixLift 3109187
  have htrace : WordTrace (prefixWord ++ tailWord_3109187) baseStart_3109187 baseEnd_3109187 := by
    simpa [prefixWord, tailWord_3109187, baseEnd_3109187] using wordTrace_append hprefix tailTrace_3109187
  have hstable : (prefixWord ++ tailWord_3109187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109187).length < 2 ^ (prefixWord ++ tailWord_3109187).sum := by decide
  have hdescent : baseEnd_3109187 < baseStart_3109187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109217 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3109217 : Nat := 118140960795 + 3109217 * 2 ^ 59
def prefixEnd_3109217 : Nat := 4983230072969 + 3 ^ 40 * 3109217 * 2
def baseEnd_3109217 : Nat := 532174260043488969296159

theorem tailTrace_3109217 : CollatzResearch.WordTrace tailWord_3109217 prefixEnd_3109217 532174260043488969296159 := by
  unfold tailWord_3109217
  simp only [CollatzResearch.WordTrace]
  refine ⟨113402460376845295832685905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75601640251230197221790603 113402460376845295832685905)
  ·
    refine ⟨85051845282633971874514429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113402460376845295832685905 85051845282633971874514429)
    ·
      refine ⟨31894441980987739452942911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85051845282633971874514429 31894441980987739452942911)
      ·
        refine ⟨47841662971481609179414367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31894441980987739452942911 47841662971481609179414367)
        ·
          refine ⟨71762494457222413769121551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47841662971481609179414367 71762494457222413769121551)
          ·
            refine ⟨107643741685833620653682327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71762494457222413769121551 107643741685833620653682327)
            ·
              refine ⟨161465612528750430980523491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107643741685833620653682327 161465612528750430980523491)
              ·
                refine ⟨242198418793125646470785237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161465612528750430980523491 242198418793125646470785237)
                ·
                  refine ⟨5676525440463882339159029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242198418793125646470785237 5676525440463882339159029)
                  ·
                    refine ⟨532174260043488969296159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5676525440463882339159029 532174260043488969296159)
                    ·
                      rfl

theorem cell23_3109217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3109217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109217 prefixEnd_3109217 := by exact prefixLift 3109217
  have htrace : WordTrace (prefixWord ++ tailWord_3109217) baseStart_3109217 baseEnd_3109217 := by
    simpa [prefixWord, tailWord_3109217, baseEnd_3109217] using wordTrace_append hprefix tailTrace_3109217
  have hstable : (prefixWord ++ tailWord_3109217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109217).length < 2 ^ (prefixWord ++ tailWord_3109217).sum := by decide
  have hdescent : baseEnd_3109217 < baseStart_3109217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109238 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_3109238 : Nat := 118140960795 + 3109238 * 2 ^ 59
def prefixEnd_3109238 : Nat := 4983230072969 + 3 ^ 40 * 3109238 * 2
def baseEnd_3109238 : Nat := 177392618136023480636209

theorem tailTrace_3109238 : CollatzResearch.WordTrace tailWord_3109238 prefixEnd_3109238 177392618136023480636209 := by
  unfold tailWord_3109238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7087701644360576026200023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75602150873179477612800245 7087701644360576026200023)
  ·
    refine ⟨10631552466540864039300035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7087701644360576026200023 10631552466540864039300035)
    ·
      refine ⟨15947328699811296058950053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631552466540864039300035 15947328699811296058950053)
      ·
        refine ⟨2990124131214618011053135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15947328699811296058950053 2990124131214618011053135)
        ·
          refine ⟨4485186196821927016579703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990124131214618011053135 4485186196821927016579703)
          ·
            refine ⟨6727779295232890524869555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485186196821927016579703 6727779295232890524869555)
            ·
              refine ⟨10091668942849335787304333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727779295232890524869555 10091668942849335787304333)
              ·
                refine ⟨3784375853568500920239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091668942849335787304333 3784375853568500920239125)
                ·
                  refine ⟨177392618136023480636209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784375853568500920239125 177392618136023480636209)
                  ·
                    rfl

theorem cell23_3109238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_3109238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109238 prefixEnd_3109238 := by exact prefixLift 3109238
  have htrace : WordTrace (prefixWord ++ tailWord_3109238) baseStart_3109238 baseEnd_3109238 := by
    simpa [prefixWord, tailWord_3109238, baseEnd_3109238] using wordTrace_append hprefix tailTrace_3109238
  have hstable : (prefixWord ++ tailWord_3109238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109238).length < 2 ^ (prefixWord ++ tailWord_3109238).sum := by decide
  have hdescent : baseEnd_3109238 < baseStart_3109238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109277 : List Nat := [1, 4, 2, 1, 15]
def baseStart_3109277 : Nat := 118140960795 + 3109277 * 2 ^ 59
def prefixEnd_3109277 : Nat := 4983230072969 + 3 ^ 40 * 3109277 * 2
def baseEnd_3109277 : Nat := 2190059792825427535169

theorem tailTrace_3109277 : CollatzResearch.WordTrace tailWord_3109277 prefixEnd_3109277 2190059792825427535169 := by
  unfold tailWord_3109277
  simp only [CollatzResearch.WordTrace]
  refine ⟨113404648756627926079870085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75603099171085284053246723 113404648756627926079870085)
  ·
    refine ⟨21263371641867736139975641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113404648756627926079870085 21263371641867736139975641)
    ·
      refine ⟨15947528731400802104981731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21263371641867736139975641 15947528731400802104981731)
      ·
        refine ⟨23921293097101203157472597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15947528731400802104981731 23921293097101203157472597)
        ·
          refine ⟨2190059792825427535169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 23921293097101203157472597 2190059792825427535169)
          ·
            rfl

theorem cell23_3109277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 15].length) (baseStart_3109277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109277 prefixEnd_3109277 := by exact prefixLift 3109277
  have htrace : WordTrace (prefixWord ++ tailWord_3109277) baseStart_3109277 baseEnd_3109277 := by
    simpa [prefixWord, tailWord_3109277, baseEnd_3109277] using wordTrace_append hprefix tailTrace_3109277
  have hstable : (prefixWord ++ tailWord_3109277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109277).length < 2 ^ (prefixWord ++ tailWord_3109277).sum := by decide
  have hdescent : baseEnd_3109277 < baseStart_3109277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109431 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 2, 5]
def baseStart_3109431 : Nat := 118140960795 + 3109431 * 2 ^ 59
def prefixEnd_3109431 : Nat := 4983230072969 + 3 ^ 40 * 3109431 * 2
def baseEnd_3109431 : Nat := 532210888330176356870831

theorem tailTrace_3109431 : CollatzResearch.WordTrace tailWord_3109431 prefixEnd_3109431 532210888330176356870831 := by
  unfold tailWord_3109431
  simp only [CollatzResearch.WordTrace]
  refine ⟨113410265598070010380976147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75606843732046673587317431 113410265598070010380976147)
  ·
    refine ⟨170115398397105015571464221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113410265598070010380976147 170115398397105015571464221)
    ·
      refine ⟨63793274398914380839299083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170115398397105015571464221 63793274398914380839299083)
      ·
        refine ⟨95689911598371571258948625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63793274398914380839299083 95689911598371571258948625)
        ·
          refine ⟨71767433698778678444211469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95689911598371571258948625 71767433698778678444211469)
          ·
            refine ⟨26912787637042004416579301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71767433698778678444211469 26912787637042004416579301)
            ·
              refine ⟨5046147681945375828108619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26912787637042004416579301 5046147681945375828108619)
              ·
                refine ⟨7569221522918063742162929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046147681945375828108619 7569221522918063742162929)
                ·
                  refine ⟨5676916142188547806622197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7569221522918063742162929 5676916142188547806622197)
                  ·
                    refine ⟨532210888330176356870831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5676916142188547806622197 532210888330176356870831)
                    ·
                      rfl

theorem cell23_3109431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_3109431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109431 prefixEnd_3109431 := by exact prefixLift 3109431
  have htrace : WordTrace (prefixWord ++ tailWord_3109431) baseStart_3109431 baseEnd_3109431 := by
    simpa [prefixWord, tailWord_3109431, baseEnd_3109431] using wordTrace_append hprefix tailTrace_3109431
  have hstable : (prefixWord ++ tailWord_3109431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109431).length < 2 ^ (prefixWord ++ tailWord_3109431).sum := by decide
  have hdescent : baseEnd_3109431 < baseStart_3109431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109441 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3109441 : Nat := 118140960795 + 3109441 * 2 ^ 59
def prefixEnd_3109441 : Nat := 4983230072969 + 3 ^ 40 * 3109441 * 2
def baseEnd_3109441 : Nat := 1596637799797074031487447

theorem tailTrace_3109441 : CollatzResearch.WordTrace tailWord_3109441 prefixEnd_3109441 1596637799797074031487447 := by
  unfold tailWord_3109441
  simp only [CollatzResearch.WordTrace]
  refine ⟨113410630328033782088840177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75607086885355854725893451 113410630328033782088840177)
  ·
    refine ⟨85057972746025336566630133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113410630328033782088840177 85057972746025336566630133)
    ·
      refine ⟨7974184944939875303121575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85057972746025336566630133 7974184944939875303121575)
      ·
        refine ⟨11961277417409812954682363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974184944939875303121575 11961277417409812954682363)
        ·
          refine ⟨17941916126114719432023545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961277417409812954682363 17941916126114719432023545)
          ·
            refine ⟨13456437094586039574017659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17941916126114719432023545 13456437094586039574017659)
            ·
              refine ⟨20184655641879059361026489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13456437094586039574017659 20184655641879059361026489)
              ·
                refine ⟨15138491731409294520769867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20184655641879059361026489 15138491731409294520769867)
                ·
                  refine ⟨22707737597113941781154801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15138491731409294520769867 22707737597113941781154801)
                  ·
                    refine ⟨17030803197835456335866101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22707737597113941781154801 17030803197835456335866101)
                    ·
                      refine ⟨1596637799797074031487447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17030803197835456335866101 1596637799797074031487447)
                      ·
                        rfl

theorem cell23_3109441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3109441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109441 prefixEnd_3109441 := by exact prefixLift 3109441
  have htrace : WordTrace (prefixWord ++ tailWord_3109441) baseStart_3109441 baseEnd_3109441 := by
    simpa [prefixWord, tailWord_3109441, baseEnd_3109441] using wordTrace_append hprefix tailTrace_3109441
  have hstable : (prefixWord ++ tailWord_3109441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109441).length < 2 ^ (prefixWord ++ tailWord_3109441).sum := by decide
  have hdescent : baseEnd_3109441 < baseStart_3109441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109451 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4]
def baseStart_3109451 : Nat := 118140960795 + 3109451 * 2 ^ 59
def prefixEnd_3109451 : Nat := 4983230072969 + 3 ^ 40 * 3109451 * 2
def baseEnd_3109451 : Nat := 1596642934603618992362401

theorem tailTrace_3109451 : CollatzResearch.WordTrace tailWord_3109451 prefixEnd_3109451 1596642934603618992362401 := by
  unfold tailWord_3109451
  simp only [CollatzResearch.WordTrace]
  refine ⟨113410995057997553796704207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75607330038665035864469471 113410995057997553796704207)
  ·
    refine ⟨170116492586996330695056311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113410995057997553796704207 170116492586996330695056311)
    ·
      refine ⟨255174738880494496042584467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170116492586996330695056311 255174738880494496042584467)
      ·
        refine ⟨382762108320741744063876701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255174738880494496042584467 382762108320741744063876701)
        ·
          refine ⟨143535790620278154023953763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382762108320741744063876701 143535790620278154023953763)
          ·
            refine ⟨215303685930417231035930645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143535790620278154023953763 215303685930417231035930645)
            ·
              refine ⟨10092360277988307704809249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215303685930417231035930645 10092360277988307704809249)
              ·
                refine ⟨7569270208491230778606937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10092360277988307704809249 7569270208491230778606937)
                ·
                  refine ⟨5676952656368423083955203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7569270208491230778606937 5676952656368423083955203)
                  ·
                    refine ⟨8515428984552634625932805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5676952656368423083955203 8515428984552634625932805)
                    ·
                      refine ⟨1596642934603618992362401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8515428984552634625932805 1596642934603618992362401)
                      ·
                        rfl

theorem cell23_3109451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4].length) (baseStart_3109451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109451 prefixEnd_3109451 := by exact prefixLift 3109451
  have htrace : WordTrace (prefixWord ++ tailWord_3109451) baseStart_3109451 baseEnd_3109451 := by
    simpa [prefixWord, tailWord_3109451, baseEnd_3109451] using wordTrace_append hprefix tailTrace_3109451
  have hstable : (prefixWord ++ tailWord_3109451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109451).length < 2 ^ (prefixWord ++ tailWord_3109451).sum := by decide
  have hdescent : baseEnd_3109451 < baseStart_3109451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109471 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3109471 : Nat := 118140960795 + 3109471 * 2 ^ 59
def prefixEnd_3109471 : Nat := 4983230072969 + 3 ^ 40 * 3109471 * 2
def baseEnd_3109471 : Nat := 1596653204216708914112309

theorem tailTrace_3109471 : CollatzResearch.WordTrace tailWord_3109471 prefixEnd_3109471 1596653204216708914112309 := by
  unfold tailWord_3109471
  simp only [CollatzResearch.WordTrace]
  refine ⟨113411724517925097212432267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75607816345283398141621511 113411724517925097212432267)
  ·
    refine ⟨170117586776887645818648401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113411724517925097212432267 170117586776887645818648401)
    ·
      refine ⟨127588190082665734363986301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170117586776887645818648401 127588190082665734363986301)
      ·
        refine ⟨47845571280999650386494863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127588190082665734363986301 47845571280999650386494863)
        ·
          refine ⟨71768356921499475579742295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47845571280999650386494863 71768356921499475579742295)
          ·
            refine ⟨107652535382249213369613443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71768356921499475579742295 107652535382249213369613443)
            ·
              refine ⟨161478803073373820054420165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107652535382249213369613443 161478803073373820054420165)
              ·
                refine ⟨30277275576257591260203781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161478803073373820054420165 30277275576257591260203781)
                ·
                  refine ⟨5676989170548298361288209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30277275576257591260203781 5676989170548298361288209)
                  ·
                    refine ⟨4257741877911223770966157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676989170548298361288209 4257741877911223770966157)
                    ·
                      refine ⟨1596653204216708914112309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4257741877911223770966157 1596653204216708914112309)
                      ·
                        rfl

theorem cell23_3109471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3109471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109471 prefixEnd_3109471 := by exact prefixLift 3109471
  have htrace : WordTrace (prefixWord ++ tailWord_3109471) baseStart_3109471 baseEnd_3109471 := by
    simpa [prefixWord, tailWord_3109471, baseEnd_3109471] using wordTrace_append hprefix tailTrace_3109471
  have hstable : (prefixWord ++ tailWord_3109471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109471).length < 2 ^ (prefixWord ++ tailWord_3109471).sum := by decide
  have hdescent : baseEnd_3109471 < baseStart_3109471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109485 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3109485 : Nat := 118140960795 + 3109485 * 2 ^ 59
def prefixEnd_3109485 : Nat := 4983230072969 + 3 ^ 40 * 3109485 * 2
def baseEnd_3109485 : Nat := 1596660392945871859337245

theorem tailTrace_3109485 : CollatzResearch.WordTrace tailWord_3109485 prefixEnd_3109485 1596660392945871859337245 := by
  unfold tailWord_3109485
  simp only [CollatzResearch.WordTrace]
  refine ⟨113412235139874377603441909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75608156759916251735627939 113412235139874377603441909)
  ·
    refine ⟨10632397044363222900322679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113412235139874377603441909 10632397044363222900322679)
    ·
      refine ⟨15948595566544834350484019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10632397044363222900322679 15948595566544834350484019)
      ·
        refine ⟨23922893349817251525726029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15948595566544834350484019 23922893349817251525726029)
        ·
          refine ⟨8971085006181469322147261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23922893349817251525726029 8971085006181469322147261)
          ·
            refine ⟨3364156877318050995805223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8971085006181469322147261 3364156877318050995805223)
            ·
              refine ⟨5046235315977076493707835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364156877318050995805223 5046235315977076493707835)
              ·
                refine ⟨7569352973965614740561753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046235315977076493707835 7569352973965614740561753)
                ·
                  refine ⟨5677014730474211055421315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7569352973965614740561753 5677014730474211055421315)
                  ·
                    refine ⟨8515522095711316583131973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5677014730474211055421315 8515522095711316583131973)
                    ·
                      refine ⟨1596660392945871859337245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8515522095711316583131973 1596660392945871859337245)
                      ·
                        rfl

theorem cell23_3109485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3109485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109485 prefixEnd_3109485 := by exact prefixLift 3109485
  have htrace : WordTrace (prefixWord ++ tailWord_3109485) baseStart_3109485 baseEnd_3109485 := by
    simpa [prefixWord, tailWord_3109485, baseEnd_3109485] using wordTrace_append hprefix tailTrace_3109485
  have hstable : (prefixWord ++ tailWord_3109485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109485).length < 2 ^ (prefixWord ++ tailWord_3109485).sum := by decide
  have hdescent : baseEnd_3109485 < baseStart_3109485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109488 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_3109488 : Nat := 118140960795 + 3109488 * 2 ^ 59
def prefixEnd_3109488 : Nat := 4983230072969 + 3 ^ 40 * 3109488 * 2
def baseEnd_3109488 : Nat := 1596661933387835347599731

theorem tailTrace_3109488 : CollatzResearch.WordTrace tailWord_3109488 prefixEnd_3109488 1596661933387835347599731 := by
  unfold tailWord_3109488
  simp only [CollatzResearch.WordTrace]
  refine ⟨56706172279431754557900559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75608229705909006077200745 56706172279431754557900559)
  ·
    refine ⟨85059258419147631836850839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56706172279431754557900559 85059258419147631836850839)
    ·
      refine ⟨127588887628721447755276259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85059258419147631836850839 127588887628721447755276259)
      ·
        refine ⟨191383331443082171632914389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127588887628721447755276259 191383331443082171632914389)
        ·
          refine ⟨4485546830697238397646431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 191383331443082171632914389 4485546830697238397646431)
          ·
            refine ⟨6728320246045857596469647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485546830697238397646431 6728320246045857596469647)
            ·
              refine ⟨10092480369068786394704471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728320246045857596469647 10092480369068786394704471)
              ·
                refine ⟨15138720553603179592056707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10092480369068786394704471 15138720553603179592056707)
                ·
                  refine ⟨22708080830404769388085061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15138720553603179592056707 22708080830404769388085061)
                  ·
                    refine ⟨4257765155700894260265949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22708080830404769388085061 4257765155700894260265949)
                    ·
                      refine ⟨1596661933387835347599731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4257765155700894260265949 1596661933387835347599731)
                      ·
                        rfl

theorem cell23_3109488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_3109488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109488 prefixEnd_3109488 := by exact prefixLift 3109488
  have htrace : WordTrace (prefixWord ++ tailWord_3109488) baseStart_3109488 baseEnd_3109488 := by
    simpa [prefixWord, tailWord_3109488, baseEnd_3109488] using wordTrace_append hprefix tailTrace_3109488
  have hstable : (prefixWord ++ tailWord_3109488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109488).length < 2 ^ (prefixWord ++ tailWord_3109488).sum := by decide
  have hdescent : baseEnd_3109488 < baseStart_3109488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109508 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 6]
def baseStart_3109508 : Nat := 118140960795 + 3109508 * 2 ^ 59
def prefixEnd_3109508 : Nat := 4983230072969 + 3 ^ 40 * 3109508 * 2
def baseEnd_3109508 : Nat := 177408022555658363261071

theorem tailTrace_3109508 : CollatzResearch.WordTrace tailWord_3109508 prefixEnd_3109508 177408022555658363261071 := by
  unfold tailWord_3109508
  simp only [CollatzResearch.WordTrace]
  refine ⟨56706537009395526265764589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75608716012527368354352785 56706537009395526265764589)
  ·
    refine ⟨21264951378523322349661721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56706537009395526265764589 21264951378523322349661721)
    ·
      refine ⟨15948713533892491762246291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21264951378523322349661721 15948713533892491762246291)
      ·
        refine ⟨23923070300838737643369437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15948713533892491762246291 23923070300838737643369437)
        ·
          refine ⟨8971151362814526616263539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23923070300838737643369437 8971151362814526616263539)
          ·
            refine ⟨13456727044221789924395309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8971151362814526616263539 13456727044221789924395309)
            ·
              refine ⟨5046272641583171221648241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13456727044221789924395309 5046272641583171221648241)
              ·
                refine ⟨3784704481187378416236181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046272641583171221648241 3784704481187378416236181)
                ·
                  refine ⟨177408022555658363261071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3784704481187378416236181 177408022555658363261071)
                  ·
                    rfl

theorem cell23_3109508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_3109508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109508 prefixEnd_3109508 := by exact prefixLift 3109508
  have htrace : WordTrace (prefixWord ++ tailWord_3109508) baseStart_3109508 baseEnd_3109508 := by
    simpa [prefixWord, tailWord_3109508, baseEnd_3109508] using wordTrace_append hprefix tailTrace_3109508
  have hstable : (prefixWord ++ tailWord_3109508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109508).length < 2 ^ (prefixWord ++ tailWord_3109508).sum := by decide
  have hdescent : baseEnd_3109508 < baseStart_3109508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109528 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3109528 : Nat := 118140960795 + 3109528 * 2 ^ 59
def prefixEnd_3109528 : Nat := 4983230072969 + 3 ^ 40 * 3109528 * 2
def baseEnd_3109528 : Nat := 1596682472614015191099547

theorem tailTrace_3109528 : CollatzResearch.WordTrace tailWord_3109528 prefixEnd_3109528 1596682472614015191099547 := by
  unfold tailWord_3109528
  simp only [CollatzResearch.WordTrace]
  refine ⟨56706901739359297973628619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75609202319145730631504825 56706901739359297973628619)
  ·
    refine ⟨85060352609038946960442929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56706901739359297973628619 85060352609038946960442929)
    ·
      refine ⟨63795264456779210220332197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85060352609038946960442929 63795264456779210220332197)
      ·
        refine ⟨11961612085646101916312287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63795264456779210220332197 11961612085646101916312287)
        ·
          refine ⟨17942418128469152874468431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961612085646101916312287 17942418128469152874468431)
          ·
            refine ⟨26913627192703729311702647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17942418128469152874468431 26913627192703729311702647)
            ·
              refine ⟨40370440789055593967553971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26913627192703729311702647 40370440789055593967553971)
              ·
                refine ⟨60555661183583390951330957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40370440789055593967553971 60555661183583390951330957)
                ·
                  refine ⟨22708372943843771606749109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60555661183583390951330957 22708372943843771606749109)
                  ·
                    refine ⟨2128909963485353588132729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22708372943843771606749109 2128909963485353588132729)
                    ·
                      refine ⟨1596682472614015191099547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128909963485353588132729 1596682472614015191099547)
                      ·
                        rfl

theorem cell23_3109528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3109528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109528 prefixEnd_3109528 := by exact prefixLift 3109528
  have htrace : WordTrace (prefixWord ++ tailWord_3109528) baseStart_3109528 baseEnd_3109528 := by
    simpa [prefixWord, tailWord_3109528, baseEnd_3109528] using wordTrace_append hprefix tailTrace_3109528
  have hstable : (prefixWord ++ tailWord_3109528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109528).length < 2 ^ (prefixWord ++ tailWord_3109528).sum := by decide
  have hdescent : baseEnd_3109528 < baseStart_3109528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109546 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3109546 : Nat := 118140960795 + 3109546 * 2 ^ 59
def prefixEnd_3109546 : Nat := 4983230072969 + 3 ^ 40 * 3109546 * 2
def baseEnd_3109546 : Nat := 532230571755265373558155

theorem tailTrace_3109546 : CollatzResearch.WordTrace tailWord_3109546 prefixEnd_3109546 532230571755265373558155 := by
  unfold tailWord_3109546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353614998163346255353123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75609639995102256680941661 28353614998163346255353123)
  ·
    refine ⟨42530422497245019383029685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28353614998163346255353123 42530422497245019383029685)
    ·
      refine ⟨3987227109116720567159033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42530422497245019383029685 3987227109116720567159033)
      ·
        refine ⟨2990420331837540425369275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3987227109116720567159033 2990420331837540425369275)
        ·
          refine ⟨4485630497756310638053913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990420331837540425369275 4485630497756310638053913)
          ·
            refine ⟨3364222873317232978540435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4485630497756310638053913 3364222873317232978540435)
            ·
              refine ⟨5046334309975849467810653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364222873317232978540435 5046334309975849467810653)
              ·
                refine ⟨1892375366240943550428995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5046334309975849467810653 1892375366240943550428995)
                ·
                  refine ⟨2838563049361415325643493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892375366240943550428995 2838563049361415325643493)
                  ·
                    refine ⟨532230571755265373558155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2838563049361415325643493 532230571755265373558155)
                    ·
                      rfl

theorem cell23_3109546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3109546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109546 prefixEnd_3109546 := by exact prefixLift 3109546
  have htrace : WordTrace (prefixWord ++ tailWord_3109546) baseStart_3109546 baseEnd_3109546 := by
    simpa [prefixWord, tailWord_3109546, baseEnd_3109546] using wordTrace_append hprefix tailTrace_3109546
  have hstable : (prefixWord ++ tailWord_3109546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109546).length < 2 ^ (prefixWord ++ tailWord_3109546).sum := by decide
  have hdescent : baseEnd_3109546 < baseStart_3109546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109568 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_3109568 : Nat := 118140960795 + 3109568 * 2 ^ 59
def prefixEnd_3109568 : Nat := 4983230072969 + 3 ^ 40 * 3109568 * 2
def baseEnd_3109568 : Nat := 532234337280065011533121

theorem tailTrace_3109568 : CollatzResearch.WordTrace tailWord_3109568 prefixEnd_3109568 532234337280065011533121 := by
  unfold tailWord_3109568
  simp only [CollatzResearch.WordTrace]
  refine ⟨56707631199286841389356679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75610174932382455185808905 56707631199286841389356679)
  ·
    refine ⟨85061446798930262084035019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56707631199286841389356679 85061446798930262084035019)
    ·
      refine ⟨127592170198395393126052529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85061446798930262084035019 127592170198395393126052529)
      ·
        refine ⟨95694127648796544844539397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127592170198395393126052529 95694127648796544844539397)
        ·
          refine ⟨17942648934149352158351137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95694127648796544844539397 17942648934149352158351137)
          ·
            refine ⟨13456986700612014118763353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17942648934149352158351137 13456986700612014118763353)
            ·
              refine ⟨10092740025459010589072515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13456986700612014118763353 10092740025459010589072515)
              ·
                refine ⟨15139110038188515883608773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10092740025459010589072515 15139110038188515883608773)
                ·
                  refine ⟨2838583132160346728176645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15139110038188515883608773 2838583132160346728176645)
                  ·
                    refine ⟨532234337280065011533121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2838583132160346728176645 532234337280065011533121)
                    ·
                      rfl

theorem cell23_3109568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_3109568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109568 prefixEnd_3109568 := by exact prefixLift 3109568
  have htrace : WordTrace (prefixWord ++ tailWord_3109568) baseStart_3109568 baseEnd_3109568 := by
    simpa [prefixWord, tailWord_3109568, baseEnd_3109568] using wordTrace_append hprefix tailTrace_3109568
  have hstable : (prefixWord ++ tailWord_3109568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109568).length < 2 ^ (prefixWord ++ tailWord_3109568).sum := by decide
  have hdescent : baseEnd_3109568 < baseStart_3109568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109575 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_3109575 : Nat := 118140960795 + 3109575 * 2 ^ 59
def prefixEnd_3109575 : Nat := 4983230072969 + 3 ^ 40 * 3109575 * 2
def baseEnd_3109575 : Nat := 1596706606204776507211831

theorem tailTrace_3109575 : CollatzResearch.WordTrace tailWord_3109575 prefixEnd_3109575 1596706606204776507211831 := by
  unfold tailWord_3109575
  simp only [CollatzResearch.WordTrace]
  refine ⟨113415517709548322974218179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75610345139698881982812119 113415517709548322974218179)
  ·
    refine ⟨170123276564322484461327269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113415517709548322974218179 170123276564322484461327269)
    ·
      refine ⟨31898114355810465836498863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170123276564322484461327269 31898114355810465836498863)
      ·
        refine ⟨47847171533715698754748295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31898114355810465836498863 47847171533715698754748295)
        ·
          refine ⟨71770757300573548132122443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47847171533715698754748295 71770757300573548132122443)
          ·
            refine ⟨107656135950860322198183665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71770757300573548132122443 107656135950860322198183665)
            ·
              refine ⟨80742101963145241648637749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107656135950860322198183665 80742101963145241648637749)
              ·
                refine ⟨7569572059044866404559789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80742101963145241648637749 7569572059044866404559789)
                ·
                  refine ⟨2838589522141824901709921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7569572059044866404559789 2838589522141824901709921)
                  ·
                    refine ⟨2128942141606368676282441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838589522141824901709921 2128942141606368676282441)
                    ·
                      refine ⟨1596706606204776507211831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128942141606368676282441 1596706606204776507211831)
                      ·
                        rfl

theorem cell23_3109575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_3109575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109575 prefixEnd_3109575 := by exact prefixLift 3109575
  have htrace : WordTrace (prefixWord ++ tailWord_3109575) baseStart_3109575 baseEnd_3109575 := by
    simpa [prefixWord, tailWord_3109575, baseEnd_3109575] using wordTrace_append hprefix tailTrace_3109575
  have hstable : (prefixWord ++ tailWord_3109575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109575).length < 2 ^ (prefixWord ++ tailWord_3109575).sum := by decide
  have hdescent : baseEnd_3109575 < baseStart_3109575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109578 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3109578 : Nat := 118140960795 + 3109578 * 2 ^ 59
def prefixEnd_3109578 : Nat := 4983230072969 + 3 ^ 40 * 3109578 * 2
def baseEnd_3109578 : Nat := 1596708146646739995474317

theorem tailTrace_3109578 : CollatzResearch.WordTrace tailWord_3109578 prefixEnd_3109578 1596708146646739995474317 := by
  unfold tailWord_3109578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353906782134363621644347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75610418085691636324384925 28353906782134363621644347)
  ·
    refine ⟨42530860173201545432466521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28353906782134363621644347 42530860173201545432466521)
    ·
      refine ⟨31898145129901159074349891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42530860173201545432466521 31898145129901159074349891)
      ·
        refine ⟨47847217694851738611524837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31898145129901159074349891 47847217694851738611524837)
        ·
          refine ⟨8971353317784700989660907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47847217694851738611524837 8971353317784700989660907)
          ·
            refine ⟨13457029976677051484491361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8971353317784700989660907 13457029976677051484491361)
            ·
              refine ⟨10092772482507788613368521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13457029976677051484491361 10092772482507788613368521)
              ·
                refine ⟨7569579361880841460026391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10092772482507788613368521 7569579361880841460026391)
                ·
                  refine ⟨11354369042821262190039587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569579361880841460026391 11354369042821262190039587)
                  ·
                    refine ⟨17031553564231893285059381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11354369042821262190039587 17031553564231893285059381)
                    ·
                      refine ⟨1596708146646739995474317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17031553564231893285059381 1596708146646739995474317)
                      ·
                        rfl

theorem cell23_3109578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3109578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109578 prefixEnd_3109578 := by exact prefixLift 3109578
  have htrace : WordTrace (prefixWord ++ tailWord_3109578) baseStart_3109578 baseEnd_3109578 := by
    simpa [prefixWord, tailWord_3109578, baseEnd_3109578] using wordTrace_append hprefix tailTrace_3109578
  have hstable : (prefixWord ++ tailWord_3109578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109578).length < 2 ^ (prefixWord ++ tailWord_3109578).sum := by decide
  have hdescent : baseEnd_3109578 < baseStart_3109578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109589 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_3109589 : Nat := 118140960795 + 3109589 * 2 ^ 59
def prefixEnd_3109589 : Nat := 4983230072969 + 3 ^ 40 * 3109589 * 2
def baseEnd_3109589 : Nat := 532237931644646484145589

theorem tailTrace_3109589 : CollatzResearch.WordTrace tailWord_3109589 prefixEnd_3109589 532237931644646484145589 := by
  unfold tailWord_3109589
  simp only [CollatzResearch.WordTrace]
  refine ⟨113416028331497603365227821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75610685554331735576818547 113416028331497603365227821)
  ·
    refine ⟨42531010624311601261960433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113416028331497603365227821 42531010624311601261960433)
    ·
      refine ⟨31898257968233700946470325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42531010624311601261960433 31898257968233700946470325)
      ·
        refine ⟨2990461684521909463731593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31898257968233700946470325 2990461684521909463731593)
        ·
          refine ⟨2242846263391432097798695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990461684521909463731593 2242846263391432097798695)
          ·
            refine ⟨3364269395087148146698043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242846263391432097798695 3364269395087148146698043)
            ·
              refine ⟨5046404092630722220047065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364269395087148146698043 5046404092630722220047065)
              ·
                refine ⟨3784803069473041665035299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046404092630722220047065 3784803069473041665035299)
                ·
                  refine ⟨5677204604209562497552949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784803069473041665035299 5677204604209562497552949)
                  ·
                    refine ⟨532237931644646484145589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5677204604209562497552949 532237931644646484145589)
                    ·
                      rfl

theorem cell23_3109589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_3109589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109589 prefixEnd_3109589 := by exact prefixLift 3109589
  have htrace : WordTrace (prefixWord ++ tailWord_3109589) baseStart_3109589 baseEnd_3109589 := by
    simpa [prefixWord, tailWord_3109589, baseEnd_3109589] using wordTrace_append hprefix tailTrace_3109589
  have hstable : (prefixWord ++ tailWord_3109589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109589).length < 2 ^ (prefixWord ++ tailWord_3109589).sum := by decide
  have hdescent : baseEnd_3109589 < baseStart_3109589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109620 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3109620 : Nat := 118140960795 + 3109620 * 2 ^ 59
def prefixEnd_3109620 : Nat := 4983230072969 + 3 ^ 40 * 3109620 * 2
def baseEnd_3109620 : Nat := 1596729712834228831149125

theorem tailTrace_3109620 : CollatzResearch.WordTrace tailWord_3109620 prefixEnd_3109620 1596729712834228831149125 := by
  unfold tailWord_3109620
  simp only [CollatzResearch.WordTrace]
  refine ⟨56708579497192647829803157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75611439329590197106404209 56708579497192647829803157)
  ·
    refine ⟨2658214663930905367022023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56708579497192647829803157 2658214663930905367022023)
    ·
      refine ⟨3987321995896358050533035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658214663930905367022023 3987321995896358050533035)
      ·
        refine ⟨5980982993844537075799553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987321995896358050533035 5980982993844537075799553)
        ·
          refine ⟨4485737245383402806849665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5980982993844537075799553 4485737245383402806849665)
          ·
            refine ⟨3364302934037552105137249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4485737245383402806849665 3364302934037552105137249)
            ·
              refine ⟨2523227200528164078852937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3364302934037552105137249 2523227200528164078852937)
              ·
                refine ⟨1892420400396123059139703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2523227200528164078852937 1892420400396123059139703)
                ·
                  refine ⟨2838630600594184588709555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892420400396123059139703 2838630600594184588709555)
                  ·
                    refine ⟨4257945900891276883064333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2838630600594184588709555 4257945900891276883064333)
                    ·
                      refine ⟨1596729712834228831149125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4257945900891276883064333 1596729712834228831149125)
                      ·
                        rfl

theorem cell23_3109620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3109620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109620 prefixEnd_3109620 := by exact prefixLift 3109620
  have htrace : WordTrace (prefixWord ++ tailWord_3109620) baseStart_3109620 baseEnd_3109620 := by
    simpa [prefixWord, tailWord_3109620, baseEnd_3109620] using wordTrace_append hprefix tailTrace_3109620
  have hstable : (prefixWord ++ tailWord_3109620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109620).length < 2 ^ (prefixWord ++ tailWord_3109620).sum := by decide
  have hdescent : baseEnd_3109620 < baseStart_3109620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109641 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_3109641 : Nat := 118140960795 + 3109641 * 2 ^ 59
def prefixEnd_3109641 : Nat := 4983230072969 + 3 ^ 40 * 3109641 * 2
def baseEnd_3109641 : Nat := 532246831975991082995509

theorem tailTrace_3109641 : CollatzResearch.WordTrace tailWord_3109641 prefixEnd_3109641 532246831975991082995509 := by
  unfold tailWord_3109641
  simp only [CollatzResearch.WordTrace]
  refine ⟨113417924927309216246120777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75611949951539477497413851 113417924927309216246120777)
  ·
    refine ⟨85063443695481912184590583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113417924927309216246120777 85063443695481912184590583)
    ·
      refine ⟨127595165543222868276885875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85063443695481912184590583 127595165543222868276885875)
      ·
        refine ⟨191392748314834302415328813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127595165543222868276885875 191392748314834302415328813)
        ·
          refine ⟨71772280618062863405748305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191392748314834302415328813 71772280618062863405748305)
          ·
            refine ⟨53829210463547147554311229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71772280618062863405748305 53829210463547147554311229)
            ·
              refine ⟨20185953923830180332866711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53829210463547147554311229 20185953923830180332866711)
              ·
                refine ⟨30278930885745270499300067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20185953923830180332866711 30278930885745270499300067)
                ·
                  refine ⟨45418396328617905748950101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30278930885745270499300067 45418396328617905748950101)
                  ·
                    refine ⟨532246831975991082995509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45418396328617905748950101 532246831975991082995509)
                    ·
                      rfl

theorem cell23_3109641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_3109641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109641 prefixEnd_3109641 := by exact prefixLift 3109641
  have htrace : WordTrace (prefixWord ++ tailWord_3109641) baseStart_3109641 baseEnd_3109641 := by
    simpa [prefixWord, tailWord_3109641, baseEnd_3109641] using wordTrace_append hprefix tailTrace_3109641
  have hstable : (prefixWord ++ tailWord_3109641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109641).length < 2 ^ (prefixWord ++ tailWord_3109641).sum := by decide
  have hdescent : baseEnd_3109641 < baseStart_3109641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109665 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3109665 : Nat := 118140960795 + 3109665 * 2 ^ 59
def prefixEnd_3109665 : Nat := 4983230072969 + 3 ^ 40 * 3109665 * 2
def baseEnd_3109665 : Nat := 1596752819463681155086417

theorem tailTrace_3109665 : CollatzResearch.WordTrace tailWord_3109665 prefixEnd_3109665 1596752819463681155086417 := by
  unfold tailWord_3109665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113418800279222268344994449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75612533519481512229996299 113418800279222268344994449)
  ·
    refine ⟨85064100209416701258745837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113418800279222268344994449 85064100209416701258745837)
    ·
      refine ⟨31899037578531262972029689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85064100209416701258745837 31899037578531262972029689)
      ·
        refine ⟨23924278183898447229022267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31899037578531262972029689 23924278183898447229022267)
        ·
          refine ⟨35886417275847670843533401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23924278183898447229022267 35886417275847670843533401)
          ·
            refine ⟨26914812956885753132650051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35886417275847670843533401 26914812956885753132650051)
            ·
              refine ⟨40372219435328629698975077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26914812956885753132650051 40372219435328629698975077)
              ·
                refine ⟨7569791144124118068557827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40372219435328629698975077 7569791144124118068557827)
                ·
                  refine ⟨11354686716186177102836741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569791144124118068557827 11354686716186177102836741)
                  ·
                    refine ⟨2129003759284908206781889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11354686716186177102836741 2129003759284908206781889)
                    ·
                      refine ⟨1596752819463681155086417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129003759284908206781889 1596752819463681155086417)
                      ·
                        rfl

theorem cell23_3109665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3109665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109665 prefixEnd_3109665 := by exact prefixLift 3109665
  have htrace : WordTrace (prefixWord ++ tailWord_3109665) baseStart_3109665 baseEnd_3109665 := by
    simpa [prefixWord, tailWord_3109665, baseEnd_3109665] using wordTrace_append hprefix tailTrace_3109665
  have hstable : (prefixWord ++ tailWord_3109665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109665).length < 2 ^ (prefixWord ++ tailWord_3109665).sum := by decide
  have hdescent : baseEnd_3109665 < baseStart_3109665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109682 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_3109682 : Nat := 118140960795 + 3109682 * 2 ^ 59
def prefixEnd_3109682 : Nat := 4983230072969 + 3 ^ 40 * 3109682 * 2
def baseEnd_3109682 : Nat := 1596761548634807588573839

theorem tailTrace_3109682 : CollatzResearch.WordTrace tailWord_3109682 prefixEnd_3109682 1596761548634807588573839 := by
  unfold tailWord_3109682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28354855080040170062090825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75612946880107120165575533 28354855080040170062090825)
  ·
    refine ⟨21266141310030127546568119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28354855080040170062090825 21266141310030127546568119)
    ·
      refine ⟨31899211965045191319852179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21266141310030127546568119 31899211965045191319852179)
      ·
        refine ⟨47848817947567786979778269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31899211965045191319852179 47848817947567786979778269)
        ·
          refine ⟨17943306730337920117416851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47848817947567786979778269 17943306730337920117416851)
          ·
            refine ⟨26914960095506880176125277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17943306730337920117416851 26914960095506880176125277)
            ·
              refine ⟨10093110035815080066046979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26914960095506880176125277 10093110035815080066046979)
              ·
                refine ⟨15139665053722620099070469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093110035815080066046979 15139665053722620099070469)
                ·
                  refine ⟨2838687197572991268575713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15139665053722620099070469 2838687197572991268575713)
                  ·
                    refine ⟨2129015398179743451431785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838687197572991268575713 2129015398179743451431785)
                    ·
                      refine ⟨1596761548634807588573839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129015398179743451431785 1596761548634807588573839)
                      ·
                        rfl

theorem cell23_3109682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_3109682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109682 prefixEnd_3109682 := by exact prefixLift 3109682
  have htrace : WordTrace (prefixWord ++ tailWord_3109682) baseStart_3109682 baseEnd_3109682 := by
    simpa [prefixWord, tailWord_3109682, baseEnd_3109682] using wordTrace_append hprefix tailTrace_3109682
  have hstable : (prefixWord ++ tailWord_3109682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109682).length < 2 ^ (prefixWord ++ tailWord_3109682).sum := by decide
  have hdescent : baseEnd_3109682 < baseStart_3109682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109688 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 7]
def baseStart_3109688 : Nat := 118140960795 + 3109688 * 2 ^ 59
def prefixEnd_3109688 : Nat := 4983230072969 + 3 ^ 40 * 3109688 * 2
def baseEnd_3109688 : Nat := 177418292168748285010979

theorem tailTrace_3109688 : CollatzResearch.WordTrace tailWord_3109688 prefixEnd_3109688 177418292168748285010979 := by
  unfold tailWord_3109688
  simp only [CollatzResearch.WordTrace]
  refine ⟨56709819579069471636540859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75613092772092628848721145 56709819579069471636540859)
  ·
    refine ⟨85064729368604207454811289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56709819579069471636540859 85064729368604207454811289)
    ·
      refine ⟨63798547026453155591108467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85064729368604207454811289 63798547026453155591108467)
      ·
        refine ⟨95697820539679733386662701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63798547026453155591108467 95697820539679733386662701)
        ·
          refine ⟨35886682702379900019998513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95697820539679733386662701 35886682702379900019998513)
          ·
            refine ⟨26915012026784925014998885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35886682702379900019998513 26915012026784925014998885)
            ·
              refine ⟨5046564755022173440312291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26915012026784925014998885 5046564755022173440312291)
              ·
                refine ⟨7569847132533260160468437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046564755022173440312291 7569847132533260160468437)
                ·
                  refine ⟨177418292168748285010979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7569847132533260160468437 177418292168748285010979)
                  ·
                    rfl

theorem cell23_3109688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_3109688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109688 prefixEnd_3109688 := by exact prefixLift 3109688
  have htrace : WordTrace (prefixWord ++ tailWord_3109688) baseStart_3109688 baseEnd_3109688 := by
    simpa [prefixWord, tailWord_3109688, baseEnd_3109688] using wordTrace_append hprefix tailTrace_3109688
  have hstable : (prefixWord ++ tailWord_3109688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109688).length < 2 ^ (prefixWord ++ tailWord_3109688).sum := by decide
  have hdescent : baseEnd_3109688 < baseStart_3109688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109699 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 2, 2, 2]
def baseStart_3109699 : Nat := 118140960795 + 3109699 * 2 ^ 59
def prefixEnd_3109699 : Nat := 4983230072969 + 3 ^ 40 * 3109699 * 2
def baseEnd_3109699 : Nat := 1596770277805934022061261

theorem tailTrace_3109699 : CollatzResearch.WordTrace tailWord_3109699 prefixEnd_3109699 1596770277805934022061261 := by
  unfold tailWord_3109699
  simp only [CollatzResearch.WordTrace]
  refine ⟨113420040361099092151732151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75613360240732728101154767 113420040361099092151732151)
  ·
    refine ⟨170130060541648638227598227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113420040361099092151732151 170130060541648638227598227)
    ·
      refine ⟨255195090812472957341397341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170130060541648638227598227 255195090812472957341397341)
      ·
        refine ⟨95698159054677359003024003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255195090812472957341397341 95698159054677359003024003)
        ·
          refine ⟨143547238582016038504536005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95698159054677359003024003 143547238582016038504536005)
          ·
            refine ⟨26915107234128007219600501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143547238582016038504536005 26915107234128007219600501)
            ·
              refine ⟨2523291303199500676837547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26915107234128007219600501 2523291303199500676837547)
              ·
                refine ⟨3784936954799251015256321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523291303199500676837547 3784936954799251015256321)
                ·
                  refine ⟨2838702716099438261442241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784936954799251015256321 2838702716099438261442241)
                  ·
                    refine ⟨2129027037074578696081681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838702716099438261442241 2129027037074578696081681)
                    ·
                      refine ⟨1596770277805934022061261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129027037074578696081681 1596770277805934022061261)
                      ·
                        rfl

theorem cell23_3109699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_3109699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109699 prefixEnd_3109699 := by exact prefixLift 3109699
  have htrace : WordTrace (prefixWord ++ tailWord_3109699) baseStart_3109699 baseEnd_3109699 := by
    simpa [prefixWord, tailWord_3109699, baseEnd_3109699] using wordTrace_append hprefix tailTrace_3109699
  have hstable : (prefixWord ++ tailWord_3109699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109699).length < 2 ^ (prefixWord ++ tailWord_3109699).sum := by decide
  have hdescent : baseEnd_3109699 < baseStart_3109699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109722 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_3109722 : Nat := 118140960795 + 3109722 * 2 ^ 59
def prefixEnd_3109722 : Nat := 4983230072969 + 3 ^ 40 * 3109722 * 2
def baseEnd_3109722 : Nat := 177420231984554159119295

theorem tailTrace_3109722 : CollatzResearch.WordTrace tailWord_3109722 prefixEnd_3109722 177420231984554159119295 := by
  unfold tailWord_3109722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28355219810003941769954855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75613919493343844719879613 28355219810003941769954855)
  ·
    refine ⟨42532829715005912654932283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28355219810003941769954855 42532829715005912654932283)
    ·
      refine ⟨63799244572508868982398425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42532829715005912654932283 63799244572508868982398425)
      ·
        refine ⟨47849433429381651736798819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63799244572508868982398425 47849433429381651736798819)
        ·
          refine ⟨71774150144072477605198229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47849433429381651736798819 71774150144072477605198229)
          ·
            refine ⟨3364413288003397387743667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71774150144072477605198229 3364413288003397387743667)
            ·
              refine ⟨5046619932005096081615501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364413288003397387743667 5046619932005096081615501)
              ·
                refine ⟨1892482474501911030605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5046619932005096081615501 1892482474501911030605813)
                ·
                  refine ⟨177420231984554159119295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1892482474501911030605813 177420231984554159119295)
                  ·
                    rfl

theorem cell23_3109722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_3109722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109722 prefixEnd_3109722 := by exact prefixLift 3109722
  have htrace : WordTrace (prefixWord ++ tailWord_3109722) baseStart_3109722 baseEnd_3109722 := by
    simpa [prefixWord, tailWord_3109722, baseEnd_3109722] using wordTrace_append hprefix tailTrace_3109722
  have hstable : (prefixWord ++ tailWord_3109722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109722).length < 2 ^ (prefixWord ++ tailWord_3109722).sum := by decide
  have hdescent : baseEnd_3109722 < baseStart_3109722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109728 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3109728 : Nat := 118140960795 + 3109728 * 2 ^ 59
def prefixEnd_3109728 : Nat := 4983230072969 + 3 ^ 40 * 3109728 * 2
def baseEnd_3109728 : Nat := 1596785168744914408598627

theorem tailTrace_3109728 : CollatzResearch.WordTrace tailWord_3109728 prefixEnd_3109728 1596785168744914408598627 := by
  unfold tailWord_3109728
  simp only [CollatzResearch.WordTrace]
  refine ⟨56710549038997015052268919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75614065385329353403025225 56710549038997015052268919)
  ·
    refine ⟨85065823558495522578403379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56710549038997015052268919 85065823558495522578403379)
    ·
      refine ⟨127598735337743283867605069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85065823558495522578403379 127598735337743283867605069)
      ·
        refine ⟨47849525751653731450351901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127598735337743283867605069 47849525751653731450351901)
        ·
          refine ⟨17943572156870149293881963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47849525751653731450351901 17943572156870149293881963)
          ·
            refine ⟨26915358235305223940822945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17943572156870149293881963 26915358235305223940822945)
            ·
              refine ⟨20186518676478917955617209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26915358235305223940822945 20186518676478917955617209)
              ·
                refine ⟨15139889007359188466712907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20186518676478917955617209 15139889007359188466712907)
                ·
                  refine ⟨22709833511038782700069361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15139889007359188466712907 22709833511038782700069361)
                  ·
                    refine ⟨17032375133279087025052021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22709833511038782700069361 17032375133279087025052021)
                    ·
                      refine ⟨1596785168744914408598627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17032375133279087025052021 1596785168744914408598627)
                      ·
                        rfl

theorem cell23_3109728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3109728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109728 prefixEnd_3109728 := by exact prefixLift 3109728
  have htrace : WordTrace (prefixWord ++ tailWord_3109728) baseStart_3109728 baseEnd_3109728 := by
    simpa [prefixWord, tailWord_3109728, baseEnd_3109728] using wordTrace_append hprefix tailTrace_3109728
  have hstable : (prefixWord ++ tailWord_3109728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109728).length < 2 ^ (prefixWord ++ tailWord_3109728).sum := by decide
  have hdescent : baseEnd_3109728 < baseStart_3109728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109735 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3109735 : Nat := 118140960795 + 3109735 * 2 ^ 59
def prefixEnd_3109735 : Nat := 4983230072969 + 3 ^ 40 * 3109735 * 2
def baseEnd_3109735 : Nat := 532262921036498627070365

theorem tailTrace_3109735 : CollatzResearch.WordTrace tailWord_3109735 prefixEnd_3109735 532262921036498627070365 := by
  unfold tailWord_3109735
  simp only [CollatzResearch.WordTrace]
  refine ⟨113421353388968670300042659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75614235592645780200028439 113421353388968670300042659)
  ·
    refine ⟨170132030083453005450063989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113421353388968670300042659 170132030083453005450063989)
    ·
      refine ⟨15949877820323719260943499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170132030083453005450063989 15949877820323719260943499)
      ·
        refine ⟨23924816730485578891415249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15949877820323719260943499 23924816730485578891415249)
        ·
          refine ⟨17943612547864184168561437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23924816730485578891415249 17943612547864184168561437)
          ·
            refine ⟨6728854705449069063210539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17943612547864184168561437 6728854705449069063210539)
            ·
              refine ⟨10093282058173603594815809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728854705449069063210539 10093282058173603594815809)
              ·
                refine ⟨7569961543630202696111857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10093282058173603594815809 7569961543630202696111857)
                ·
                  refine ⟨5677471157722652022083893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7569961543630202696111857 5677471157722652022083893)
                  ·
                    refine ⟨532262921036498627070365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5677471157722652022083893 532262921036498627070365)
                    ·
                      rfl

theorem cell23_3109735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3109735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109735 prefixEnd_3109735 := by exact prefixLift 3109735
  have htrace : WordTrace (prefixWord ++ tailWord_3109735) baseStart_3109735 baseEnd_3109735 := by
    simpa [prefixWord, tailWord_3109735, baseEnd_3109735] using wordTrace_append hprefix tailTrace_3109735
  have hstable : (prefixWord ++ tailWord_3109735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109735).length < 2 ^ (prefixWord ++ tailWord_3109735).sum := by decide
  have hdescent : baseEnd_3109735 < baseStart_3109735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109755 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 2, 4, 2]
def baseStart_3109755 : Nat := 118140960795 + 3109755 * 2 ^ 59
def prefixEnd_3109755 : Nat := 4983230072969 + 3 ^ 40 * 3109755 * 2
def baseEnd_3109755 : Nat := 1596799032722585802961003

theorem tailTrace_3109755 : CollatzResearch.WordTrace tailWord_3109755 prefixEnd_3109755 1596799032722585802961003 := by
  unfold tailWord_3109755
  simp only [CollatzResearch.WordTrace]
  refine ⟨113422082848896213715770719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75614721899264142477180479 113422082848896213715770719)
  ·
    refine ⟨170133124273344320573656079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113422082848896213715770719 170133124273344320573656079)
    ·
      refine ⟨255199686410016480860484119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170133124273344320573656079 255199686410016480860484119)
      ·
        refine ⟨382799529615024721290726179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255199686410016480860484119 382799529615024721290726179)
        ·
          refine ⟨574199294422537081936089269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382799529615024721290726179 574199294422537081936089269)
          ·
            refine ⟨53831183852112851431508369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 574199294422537081936089269 53831183852112851431508369)
            ·
              refine ⟨40373387889084638573631277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53831183852112851431508369 40373387889084638573631277)
              ·
                refine ⟨15140020458406739465111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40373387889084638573631277 15140020458406739465111729)
                ·
                  refine ⟨11355015343805054598833797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15140020458406739465111729 11355015343805054598833797)
                  ·
                    refine ⟨2129065376963447737281337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11355015343805054598833797 2129065376963447737281337)
                    ·
                      refine ⟨1596799032722585802961003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129065376963447737281337 1596799032722585802961003)
                      ·
                        rfl

theorem cell23_3109755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4, 2].length) (baseStart_3109755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109755 prefixEnd_3109755 := by exact prefixLift 3109755
  have htrace : WordTrace (prefixWord ++ tailWord_3109755) baseStart_3109755 baseEnd_3109755 := by
    simpa [prefixWord, tailWord_3109755, baseEnd_3109755] using wordTrace_append hprefix tailTrace_3109755
  have hstable : (prefixWord ++ tailWord_3109755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109755).length < 2 ^ (prefixWord ++ tailWord_3109755).sum := by decide
  have hdescent : baseEnd_3109755 < baseStart_3109755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109818 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_3109818 : Nat := 118140960795 + 3109818 * 2 ^ 59
def prefixEnd_3109818 : Nat := 4983230072969 + 3 ^ 40 * 3109818 * 2
def baseEnd_3109818 : Nat := 1596831382003819056473213

theorem tailTrace_3109818 : CollatzResearch.WordTrace tailWord_3109818 prefixEnd_3109818 1596831382003819056473213 := by
  unfold tailWord_3109818
  simp only [CollatzResearch.WordTrace]
  refine ⟨28356095161916993868828527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75616253765111983650209405 28356095161916993868828527)
  ·
    refine ⟨42534142742875490803242791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28356095161916993868828527 42534142742875490803242791)
    ·
      refine ⟨63801214114313236204864187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42534142742875490803242791 63801214114313236204864187)
      ·
        refine ⟨95701821171469854307296281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63801214114313236204864187 95701821171469854307296281)
        ·
          refine ⟨71776365878602390730472211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95701821171469854307296281 71776365878602390730472211)
          ·
            refine ⟨107664548817903586095708317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71776365878602390730472211 107664548817903586095708317)
            ·
              refine ⟨40374205806713844785890619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107664548817903586095708317 40374205806713844785890619)
              ·
                refine ⟨60561308710070767178835929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40374205806713844785890619 60561308710070767178835929)
                ·
                  refine ⟨45420981532553075384126947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60561308710070767178835929 45420981532553075384126947)
                  ·
                    refine ⟨68131472298829613076190421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45420981532553075384126947 68131472298829613076190421)
                    ·
                      refine ⟨1596831382003819056473213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68131472298829613076190421 1596831382003819056473213)
                      ·
                        rfl

theorem cell23_3109818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_3109818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109818 prefixEnd_3109818 := by exact prefixLift 3109818
  have htrace : WordTrace (prefixWord ++ tailWord_3109818) baseStart_3109818 baseEnd_3109818 := by
    simpa [prefixWord, tailWord_3109818, baseEnd_3109818] using wordTrace_append hprefix tailTrace_3109818
  have hstable : (prefixWord ++ tailWord_3109818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109818).length < 2 ^ (prefixWord ++ tailWord_3109818).sum := by decide
  have hdescent : baseEnd_3109818 < baseStart_3109818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109839 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 1, 1, 3]
def baseStart_3109839 : Nat := 118140960795 + 3109839 * 2 ^ 59
def prefixEnd_3109839 : Nat := 4983230072969 + 3 ^ 40 * 3109839 * 2
def baseEnd_3109839 : Nat := 1596842165097563474310617

theorem tailTrace_3109839 : CollatzResearch.WordTrace tailWord_3109839 prefixEnd_3109839 1596842165097563474310617 := by
  unfold tailWord_3109839
  simp only [CollatzResearch.WordTrace]
  refine ⟨113425146580591896061828571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75616764387061264041219047 113425146580591896061828571)
  ·
    refine ⟨170137719870887844092742857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113425146580591896061828571 170137719870887844092742857)
    ·
      refine ⟨127603289903165883069557143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170137719870887844092742857 127603289903165883069557143)
      ·
        refine ⟨191404934854748824604335715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127603289903165883069557143 191404934854748824604335715)
        ·
          refine ⟨287107402282123236906503573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191404934854748824604335715 287107402282123236906503573)
          ·
            refine ⟨13458159481974526729992355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287107402282123236906503573 13458159481974526729992355)
            ·
              refine ⟨20187239222961790094988533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13458159481974526729992355 20187239222961790094988533)
              ·
                refine ⟨1892553677152667821405175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20187239222961790094988533 1892553677152667821405175)
                ·
                  refine ⟨2838830515729001732107763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892553677152667821405175 2838830515729001732107763)
                  ·
                    refine ⟨4258245773593502598161645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2838830515729001732107763 4258245773593502598161645)
                    ·
                      refine ⟨1596842165097563474310617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4258245773593502598161645 1596842165097563474310617)
                      ·
                        rfl

theorem cell23_3109839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 1, 3].length) (baseStart_3109839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109839 prefixEnd_3109839 := by exact prefixLift 3109839
  have htrace : WordTrace (prefixWord ++ tailWord_3109839) baseStart_3109839 baseEnd_3109839 := by
    simpa [prefixWord, tailWord_3109839, baseEnd_3109839] using wordTrace_append hprefix tailTrace_3109839
  have hstable : (prefixWord ++ tailWord_3109839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109839).length < 2 ^ (prefixWord ++ tailWord_3109839).sum := by decide
  have hdescent : baseEnd_3109839 < baseStart_3109839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109955 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_3109955 : Nat := 118140960795 + 3109955 * 2 ^ 59
def prefixEnd_3109955 : Nat := 4983230072969 + 3 ^ 40 * 3109955 * 2
def baseEnd_3109955 : Nat := 1596901728853485020460083

theorem tailTrace_3109955 : CollatzResearch.WordTrace tailWord_3109955 prefixEnd_3109955 1596901728853485020460083 := by
  unfold tailWord_3109955
  simp only [CollatzResearch.WordTrace]
  refine ⟨113429377448171647873051319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75619584965447765248700879 113429377448171647873051319)
  ·
    refine ⟨170144066172257471809576979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113429377448171647873051319 170144066172257471809576979)
    ·
      refine ⟨255216099258386207714365469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170144066172257471809576979 255216099258386207714365469)
      ·
        refine ⟨95706037221894827892887051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255216099258386207714365469 95706037221894827892887051)
        ·
          refine ⟨143559055832842241839330577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95706037221894827892887051 143559055832842241839330577)
          ·
            refine ⟨107669291874631681379497933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143559055832842241839330577 107669291874631681379497933)
            ·
              refine ⟨40375984452986880517311725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107669291874631681379497933 40375984452986880517311725)
              ·
                refine ⟨15140994169870080193991897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40375984452986880517311725 15140994169870080193991897)
                ·
                  refine ⟨11355745627402560145493923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15140994169870080193991897 11355745627402560145493923)
                  ·
                    refine ⟨17033618441103840218240885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11355745627402560145493923 17033618441103840218240885)
                    ·
                      refine ⟨1596901728853485020460083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17033618441103840218240885 1596901728853485020460083)
                      ·
                        rfl

theorem cell23_3109955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_3109955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109955 prefixEnd_3109955 := by exact prefixLift 3109955
  have htrace : WordTrace (prefixWord ++ tailWord_3109955) baseStart_3109955 baseEnd_3109955 := by
    simpa [prefixWord, tailWord_3109955, baseEnd_3109955] using wordTrace_append hprefix tailTrace_3109955
  have hstable : (prefixWord ++ tailWord_3109955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109955).length < 2 ^ (prefixWord ++ tailWord_3109955).sum := by decide
  have hdescent : baseEnd_3109955 < baseStart_3109955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109969 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_3109969 : Nat := 118140960795 + 3109969 * 2 ^ 59
def prefixEnd_3109969 : Nat := 4983230072969 + 3 ^ 40 * 3109969 * 2
def baseEnd_3109969 : Nat := 1596908917582647965685019

theorem tailTrace_3109969 : CollatzResearch.WordTrace tailWord_3109969 prefixEnd_3109969 1596908917582647965685019 := by
  unfold tailWord_3109969
  simp only [CollatzResearch.WordTrace]
  refine ⟨113429888070120928264060961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75619925380080618842707307 113429888070120928264060961)
  ·
    refine ⟨85072416052590696198045721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113429888070120928264060961 85072416052590696198045721)
    ·
      refine ⟨63804312039443022148534291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85072416052590696198045721 63804312039443022148534291)
      ·
        refine ⟨95706468059164533222801437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63804312039443022148534291 95706468059164533222801437)
        ·
          refine ⟨35889925522186699958550539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95706468059164533222801437 35889925522186699958550539)
          ·
            refine ⟨53834888283280049937825809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35889925522186699958550539 53834888283280049937825809)
            ·
              refine ⟨40376166212460037453369357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53834888283280049937825809 40376166212460037453369357)
              ·
                refine ⟨15141062329672514045013509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40376166212460037453369357 15141062329672514045013509)
                ·
                  refine ⟨2838949186813596383440033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15141062329672514045013509 2838949186813596383440033)
                  ·
                    refine ⟨2129211890110197287580025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2838949186813596383440033 2129211890110197287580025)
                    ·
                      refine ⟨1596908917582647965685019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129211890110197287580025 1596908917582647965685019)
                      ·
                        rfl

theorem cell23_3109969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_3109969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109969 prefixEnd_3109969 := by exact prefixLift 3109969
  have htrace : WordTrace (prefixWord ++ tailWord_3109969) baseStart_3109969 baseEnd_3109969 := by
    simpa [prefixWord, tailWord_3109969, baseEnd_3109969] using wordTrace_append hprefix tailTrace_3109969
  have hstable : (prefixWord ++ tailWord_3109969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109969).length < 2 ^ (prefixWord ++ tailWord_3109969).sum := by decide
  have hdescent : baseEnd_3109969 < baseStart_3109969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109972 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3109972 : Nat := 118140960795 + 3109972 * 2 ^ 59
def prefixEnd_3109972 : Nat := 4983230072969 + 3 ^ 40 * 3109972 * 2
def baseEnd_3109972 : Nat := 1596910458024611453947505

theorem tailTrace_3109972 : CollatzResearch.WordTrace tailWord_3109972 prefixEnd_3109972 1596910458024611453947505 := by
  unfold tailWord_3109972
  simp only [CollatzResearch.WordTrace]
  refine ⟨56714998744555029888210085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75619998326073373184280113 56714998744555029888210085)
  ·
    refine ⟨10634062264604068104039391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56714998744555029888210085 10634062264604068104039391)
    ·
      refine ⟨15951093396906102156059087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10634062264604068104039391 15951093396906102156059087)
      ·
        refine ⟨23926640095359153234088631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15951093396906102156059087 23926640095359153234088631)
        ·
          refine ⟨35889960143038729851132947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23926640095359153234088631 35889960143038729851132947)
          ·
            refine ⟨53834940214558094776699421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35889960143038729851132947 53834940214558094776699421)
            ·
              refine ⟨20188102580459285541262283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53834940214558094776699421 20188102580459285541262283)
              ·
                refine ⟨30282153870688928311893425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20188102580459285541262283 30282153870688928311893425)
                ·
                  refine ⟨22711615403016696233920069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30282153870688928311893425 22711615403016696233920069)
                  ·
                    refine ⟨4258427888065630543860013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22711615403016696233920069 4258427888065630543860013)
                    ·
                      refine ⟨1596910458024611453947505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4258427888065630543860013 1596910458024611453947505)
                      ·
                        rfl

theorem cell23_3109972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3109972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109972 prefixEnd_3109972 := by exact prefixLift 3109972
  have htrace : WordTrace (prefixWord ++ tailWord_3109972) baseStart_3109972 baseEnd_3109972 := by
    simpa [prefixWord, tailWord_3109972, baseEnd_3109972] using wordTrace_append hprefix tailTrace_3109972
  have hstable : (prefixWord ++ tailWord_3109972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109972).length < 2 ^ (prefixWord ++ tailWord_3109972).sum := by decide
  have hdescent : baseEnd_3109972 < baseStart_3109972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109975 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 7]
def baseStart_3109975 : Nat := 118140960795 + 3109975 * 2 ^ 59
def prefixEnd_3109975 : Nat := 4983230072969 + 3 ^ 40 * 3109975 * 2
def baseEnd_3109975 : Nat := 177434666496286104689999

theorem tailTrace_3109975 : CollatzResearch.WordTrace tailWord_3109975 prefixEnd_3109975 177434666496286104689999 := by
  unfold tailWord_3109975
  simp only [CollatzResearch.WordTrace]
  refine ⟨113430106908099191288779379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75620071272066127525852919 113430106908099191288779379)
  ·
    refine ⟨170145160362148786933169069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113430106908099191288779379 170145160362148786933169069)
    ·
      refine ⟨63804435135805795099938401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170145160362148786933169069 63804435135805795099938401)
      ·
        refine ⟨47853326351854346324953801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63804435135805795099938401 47853326351854346324953801)
        ·
          refine ⟨35889994763890759743715351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47853326351854346324953801 35889994763890759743715351)
          ·
            refine ⟨53834992145836139615573027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35889994763890759743715351 53834992145836139615573027)
            ·
              refine ⟨80752488218754209423359541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53834992145836139615573027 80752488218754209423359541)
              ·
                refine ⟨7570545770508207133439957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80752488218754209423359541 7570545770508207133439957)
                ·
                  refine ⟨177434666496286104689999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7570545770508207133439957 177434666496286104689999)
                  ·
                    rfl

theorem cell23_3109975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 7].length) (baseStart_3109975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109975 prefixEnd_3109975 := by exact prefixLift 3109975
  have htrace : WordTrace (prefixWord ++ tailWord_3109975) baseStart_3109975 baseEnd_3109975 := by
    simpa [prefixWord, tailWord_3109975, baseEnd_3109975] using wordTrace_append hprefix tailTrace_3109975
  have hstable : (prefixWord ++ tailWord_3109975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109975).length < 2 ^ (prefixWord ++ tailWord_3109975).sum := by decide
  have hdescent : baseEnd_3109975 < baseStart_3109975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109986 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3109986 : Nat := 118140960795 + 3109986 * 2 ^ 59
def prefixEnd_3109986 : Nat := 4983230072969 + 3 ^ 40 * 3109986 * 2
def baseEnd_3109986 : Nat := 1596917646753774399172441

theorem tailTrace_3109986 : CollatzResearch.WordTrace tailWord_3109986 prefixEnd_3109986 1596917646753774399172441 := by
  unfold tailWord_3109986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28357627027764835041857453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75620338740706226778286541 28357627027764835041857453)
  ·
    refine ⟨10634110135411813140696545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28357627027764835041857453 10634110135411813140696545)
    ·
      refine ⟨7975582601558859855522409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10634110135411813140696545 7975582601558859855522409)
      ·
        refine ⟨5981686951169144891641807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7975582601558859855522409 5981686951169144891641807)
        ·
          refine ⟨8972530426753717337462711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981686951169144891641807 8972530426753717337462711)
          ·
            refine ⟨13458795640130576006194067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972530426753717337462711 13458795640130576006194067)
            ·
              refine ⟨20188193460195864009291101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13458795640130576006194067 20188193460195864009291101)
              ·
                refine ⟨7570572547573449003484163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20188193460195864009291101 7570572547573449003484163)
                ·
                  refine ⟨11355858821360173505226245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570572547573449003484163 11355858821360173505226245)
                  ·
                    refine ⟨2129223529005032532229921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11355858821360173505226245 2129223529005032532229921)
                    ·
                      refine ⟨1596917646753774399172441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129223529005032532229921 1596917646753774399172441)
                      ·
                        rfl

theorem cell23_3109986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3109986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3109986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3109986 prefixEnd_3109986 := by exact prefixLift 3109986
  have htrace : WordTrace (prefixWord ++ tailWord_3109986) baseStart_3109986 baseEnd_3109986 := by
    simpa [prefixWord, tailWord_3109986, baseEnd_3109986] using wordTrace_append hprefix tailTrace_3109986
  have hstable : (prefixWord ++ tailWord_3109986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109986).length < 2 ^ (prefixWord ++ tailWord_3109986).sum := by decide
  have hdescent : baseEnd_3109986 < baseStart_3109986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110002 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3110002 : Nat := 118140960795 + 3110002 * 2 ^ 59
def prefixEnd_3110002 : Nat := 4983230072969 + 3 ^ 40 * 3110002 * 2
def baseEnd_3110002 : Nat := 1596925862444246336572367

theorem tailTrace_3110002 : CollatzResearch.WordTrace tailWord_3110002 prefixEnd_3110002 1596925862444246336572367 := by
  unfold tailWord_3110002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28357772919750343725003065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75620727786000916600008173 28357772919750343725003065)
  ·
    refine ⟨21268329689812757793752299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28357772919750343725003065 21268329689812757793752299)
    ·
      refine ⟨31902494534719136690628449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21268329689812757793752299 31902494534719136690628449)
      ·
        refine ⟨23926870901039352517971337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31902494534719136690628449 23926870901039352517971337)
        ·
          refine ⟨17945153175779514388478503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23926870901039352517971337 17945153175779514388478503)
          ·
            refine ⟨26917729763669271582717755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945153175779514388478503 26917729763669271582717755)
            ·
              refine ⟨40376594645503907374076633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26917729763669271582717755 40376594645503907374076633)
              ·
                refine ⟨30282445984127930530557475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40376594645503907374076633 30282445984127930530557475)
                ·
                  refine ⟨45423668976191895795836213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30282445984127930530557475 45423668976191895795836213)
                  ·
                    refine ⟨4258468966517990230859645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45423668976191895795836213 4258468966517990230859645)
                    ·
                      refine ⟨1596925862444246336572367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4258468966517990230859645 1596925862444246336572367)
                      ·
                        rfl

theorem cell23_3110002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3110002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110002 prefixEnd_3110002 := by exact prefixLift 3110002
  have htrace : WordTrace (prefixWord ++ tailWord_3110002) baseStart_3110002 baseEnd_3110002 := by
    simpa [prefixWord, tailWord_3110002, baseEnd_3110002] using wordTrace_append hprefix tailTrace_3110002
  have hstable : (prefixWord ++ tailWord_3110002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110002).length < 2 ^ (prefixWord ++ tailWord_3110002).sum := by decide
  have hdescent : baseEnd_3110002 < baseStart_3110002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110014 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3110014 : Nat := 118140960795 + 3110014 * 2 ^ 59
def prefixEnd_3110014 : Nat := 4983230072969 + 3 ^ 40 * 3110014 * 2
def baseEnd_3110014 : Nat := 1596932024212100289622313

theorem tailTrace_3110014 : CollatzResearch.WordTrace tailWord_3110014 prefixEnd_3110014 1596932024212100289622313 := by
  unfold tailWord_3110014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178941169369737618681137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75621019569971933966299397 14178941169369737618681137)
  ·
    refine ⟨10634205877027303214010853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14178941169369737618681137 10634205877027303214010853)
    ·
      refine ⟨1993913601942619352627035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10634205877027303214010853 1993913601942619352627035)
      ·
        refine ⟨2990870402913929028940553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993913601942619352627035 2990870402913929028940553)
        ·
          refine ⟨2243152802185446771705415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990870402913929028940553 2243152802185446771705415)
          ·
            refine ⟨3364729203278170157558123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243152802185446771705415 3364729203278170157558123)
            ·
              refine ⟨5047093804917255236337185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364729203278170157558123 5047093804917255236337185)
              ·
                refine ⟨3785320353687941427252889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5047093804917255236337185 3785320353687941427252889)
                ·
                  refine ⟨2838990265265956070439667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3785320353687941427252889 2838990265265956070439667)
                  ·
                    refine ⟨4258485397898934105659501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2838990265265956070439667 4258485397898934105659501)
                    ·
                      refine ⟨1596932024212100289622313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4258485397898934105659501 1596932024212100289622313)
                      ·
                        rfl

theorem cell23_3110014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3110014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110014 prefixEnd_3110014 := by exact prefixLift 3110014
  have htrace : WordTrace (prefixWord ++ tailWord_3110014) baseStart_3110014 baseEnd_3110014 := by
    simpa [prefixWord, tailWord_3110014, baseEnd_3110014] using wordTrace_append hprefix tailTrace_3110014
  have hstable : (prefixWord ++ tailWord_3110014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110014).length < 2 ^ (prefixWord ++ tailWord_3110014).sum := by decide
  have hdescent : baseEnd_3110014 < baseStart_3110014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110143 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 1, 1, 3]
def baseStart_3110143 : Nat := 118140960795 + 3110143 * 2 ^ 59
def prefixEnd_3110143 : Nat := 4983230072969 + 3 ^ 40 * 3110143 * 2
def baseEnd_3110143 : Nat := 1596998263216530284909219

theorem tailTrace_3110143 : CollatzResearch.WordTrace tailWord_3110143 prefixEnd_3110143 1596998263216530284909219 := by
  unfold tailWord_3110143
  simp only [CollatzResearch.WordTrace]
  refine ⟨113436234371490555980895083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75624156247660370653930055 113436234371490555980895083)
  ·
    refine ⟨170154351557235833971342625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113436234371490555980895083 170154351557235833971342625)
    ·
      refine ⟨127615763667926875478506969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170154351557235833971342625 127615763667926875478506969)
      ·
        refine ⟨95711822750945156608880227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127615763667926875478506969 95711822750945156608880227)
        ·
          refine ⟨143567734126417734913320341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95711822750945156608880227 143567734126417734913320341)
          ·
            refine ⟨6729737537175831324061891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143567734126417734913320341 6729737537175831324061891)
            ·
              refine ⟨10094606305763746986092837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6729737537175831324061891 10094606305763746986092837)
              ·
                refine ⟨1892738682330702559892407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10094606305763746986092837 1892738682330702559892407)
                ·
                  refine ⟨2839108023496053839838611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892738682330702559892407 2839108023496053839838611)
                  ·
                    refine ⟨4258662035244080759757917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2839108023496053839838611 4258662035244080759757917)
                    ·
                      refine ⟨1596998263216530284909219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4258662035244080759757917 1596998263216530284909219)
                      ·
                        rfl

theorem cell23_3110143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_3110143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110143 prefixEnd_3110143 := by exact prefixLift 3110143
  have htrace : WordTrace (prefixWord ++ tailWord_3110143) baseStart_3110143 baseEnd_3110143 := by
    simpa [prefixWord, tailWord_3110143, baseEnd_3110143] using wordTrace_append hprefix tailTrace_3110143
  have hstable : (prefixWord ++ tailWord_3110143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110143).length < 2 ^ (prefixWord ++ tailWord_3110143).sum := by decide
  have hdescent : baseEnd_3110143 < baseStart_3110143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110172 : List Nat := [2, 2, 3, 1, 1, 1, 2, 11]
def baseStart_3110172 : Nat := 118140960795 + 3110172 * 2 ^ 59
def prefixEnd_3110172 : Nat := 4983230072969 + 3 ^ 40 * 3110172 * 2
def baseEnd_3110172 : Nat := 59148635339092987831355

theorem tailTrace_3110172 : CollatzResearch.WordTrace tailWord_3110172 prefixEnd_3110172 59148635339092987831355 := by
  unfold tailWord_3110172
  simp only [CollatzResearch.WordTrace]
  refine ⟨56718646044192746966850385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75624861392256995955800513 56718646044192746966850385)
  ·
    refine ⟨42538984533144560225137789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56718646044192746966850385 42538984533144560225137789)
    ·
      refine ⟨15952119199929210084426671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42538984533144560225137789 15952119199929210084426671)
      ·
        refine ⟨23928178799893815126640007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15952119199929210084426671 23928178799893815126640007)
        ·
          refine ⟨35892268199840722689960011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23928178799893815126640007 35892268199840722689960011)
          ·
            refine ⟨53838402299761084034940017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35892268199840722689960011 53838402299761084034940017)
            ·
              refine ⟨40378801724820813026205013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53838402299761084034940017 40378801724820813026205013)
              ·
                refine ⟨59148635339092987831355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40378801724820813026205013 59148635339092987831355)
                ·
                  rfl

theorem cell23_3110172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 11].length) (baseStart_3110172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110172 prefixEnd_3110172 := by exact prefixLift 3110172
  have htrace : WordTrace (prefixWord ++ tailWord_3110172) baseStart_3110172 baseEnd_3110172 := by
    simpa [prefixWord, tailWord_3110172, baseEnd_3110172] using wordTrace_append hprefix tailTrace_3110172
  have hstable : (prefixWord ++ tailWord_3110172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110172).length < 2 ^ (prefixWord ++ tailWord_3110172).sum := by decide
  have hdescent : baseEnd_3110172 < baseStart_3110172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110179 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3110179 : Nat := 118140960795 + 3110179 * 2 ^ 59
def prefixEnd_3110179 : Nat := 4983230072969 + 3 ^ 40 * 3110179 * 2
def baseEnd_3110179 : Nat := 1597016748520092144059053

theorem tailTrace_3110179 : CollatzResearch.WordTrace tailWord_3110179 prefixEnd_3110179 1597016748520092144059053 := by
  unfold tailWord_3110179
  simp only [CollatzResearch.WordTrace]
  refine ⟨113437547399360134129205591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75625031599573422752803727 113437547399360134129205591)
  ·
    refine ⟨170156321099040201193808387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113437547399360134129205591 170156321099040201193808387)
    ·
      refine ⟨255234481648560301790712581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170156321099040201193808387 255234481648560301790712581)
      ·
        refine ⟨47856465309105056585758609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255234481648560301790712581 47856465309105056585758609)
        ·
          refine ⟨35892348981828792439318957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47856465309105056585758609 35892348981828792439318957)
          ·
            refine ⟨13459630868185797164744609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35892348981828792439318957 13459630868185797164744609)
            ·
              refine ⟨10094723151139347873558457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13459630868185797164744609 10094723151139347873558457)
              ·
                refine ⟨7571042363354510905168843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10094723151139347873558457 7571042363354510905168843)
                ·
                  refine ⟨11356563545031766357753265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571042363354510905168843 11356563545031766357753265)
                  ·
                    refine ⟨8517422658773824768314949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11356563545031766357753265 8517422658773824768314949)
                    ·
                      refine ⟨1597016748520092144059053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8517422658773824768314949 1597016748520092144059053)
                      ·
                        rfl

theorem cell23_3110179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3110179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110179 prefixEnd_3110179 := by exact prefixLift 3110179
  have htrace : WordTrace (prefixWord ++ tailWord_3110179) baseStart_3110179 baseEnd_3110179 := by
    simpa [prefixWord, tailWord_3110179, baseEnd_3110179] using wordTrace_append hprefix tailTrace_3110179
  have hstable : (prefixWord ++ tailWord_3110179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110179).length < 2 ^ (prefixWord ++ tailWord_3110179).sum := by decide
  have hdescent : baseEnd_3110179 < baseStart_3110179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110193 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_3110193 : Nat := 118140960795 + 3110193 * 2 ^ 59
def prefixEnd_3110193 : Nat := 4983230072969 + 3 ^ 40 * 3110193 * 2
def baseEnd_3110193 : Nat := 532341312416418363094663

theorem tailTrace_3110193 : CollatzResearch.WordTrace tailWord_3110193 prefixEnd_3110193 532341312416418363094663 := by
  unfold tailWord_3110193
  simp only [CollatzResearch.WordTrace]
  refine ⟨113438058021309414520215233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75625372014206276346810155 113438058021309414520215233)
  ·
    refine ⟨85078543515982060890161425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113438058021309414520215233 85078543515982060890161425)
    ·
      refine ⟨63808907636986545667621069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85078543515982060890161425 63808907636986545667621069)
      ·
        refine ⟨23928340363869954625357901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63808907636986545667621069 23928340363869954625357901)
        ·
          refine ⟨8973127636451232984509213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23928340363869954625357901 8973127636451232984509213)
          ·
            refine ⟨3364922863669212369190955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8973127636451232984509213 3364922863669212369190955)
            ·
              refine ⟨5047384295503818553786433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364922863669212369190955 5047384295503818553786433)
              ·
                refine ⟨3785538221627863915339825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5047384295503818553786433 3785538221627863915339825)
                ·
                  refine ⟨2839153666220897936504869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3785538221627863915339825 2839153666220897936504869)
                  ·
                    refine ⟨532341312416418363094663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839153666220897936504869 532341312416418363094663)
                    ·
                      rfl

theorem cell23_3110193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_3110193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110193 prefixEnd_3110193 := by exact prefixLift 3110193
  have htrace : WordTrace (prefixWord ++ tailWord_3110193) baseStart_3110193 baseEnd_3110193 := by
    simpa [prefixWord, tailWord_3110193, baseEnd_3110193] using wordTrace_append hprefix tailTrace_3110193
  have hstable : (prefixWord ++ tailWord_3110193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110193).length < 2 ^ (prefixWord ++ tailWord_3110193).sum := by decide
  have hdescent : baseEnd_3110193 < baseStart_3110193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110229 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3110229 : Nat := 118140960795 + 3110229 * 2 ^ 59
def prefixEnd_3110229 : Nat := 4983230072969 + 3 ^ 40 * 3110229 * 2
def baseEnd_3110229 : Nat := 1597042422552816948433823

theorem tailTrace_3110229 : CollatzResearch.WordTrace tailWord_3110229 prefixEnd_3110229 1597042422552816948433823 := by
  unfold tailWord_3110229
  simp only [CollatzResearch.WordTrace]
  refine ⟨113439371049178992668525741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75626247366119328445683827 113439371049178992668525741)
  ·
    refine ⟨42539764143442122250697153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113439371049178992668525741 42539764143442122250697153)
    ·
      refine ⟨31904823107581591688022865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42539764143442122250697153 31904823107581591688022865)
      ·
        refine ⟨23928617330686193766017149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31904823107581591688022865 23928617330686193766017149)
        ·
          refine ⟨8973231499007322662256431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23928617330686193766017149 8973231499007322662256431)
          ·
            refine ⟨13459847248510983993384647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973231499007322662256431 13459847248510983993384647)
            ·
              refine ⟨20189770872766475990076971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13459847248510983993384647 20189770872766475990076971)
              ·
                refine ⟨30284656309149713985115457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20189770872766475990076971 30284656309149713985115457)
                ·
                  refine ⟨22713492231862285488836593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30284656309149713985115457 22713492231862285488836593)
                  ·
                    refine ⟨17035119173896714116627445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22713492231862285488836593 17035119173896714116627445)
                    ·
                      refine ⟨1597042422552816948433823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17035119173896714116627445 1597042422552816948433823)
                      ·
                        rfl

theorem cell23_3110229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3110229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110229 prefixEnd_3110229 := by exact prefixLift 3110229
  have htrace : WordTrace (prefixWord ++ tailWord_3110229) baseStart_3110229 baseEnd_3110229 := by
    simpa [prefixWord, tailWord_3110229, baseEnd_3110229] using wordTrace_append hprefix tailTrace_3110229
  have hstable : (prefixWord ++ tailWord_3110229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110229).length < 2 ^ (prefixWord ++ tailWord_3110229).sum := by decide
  have hdescent : baseEnd_3110229 < baseStart_3110229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110243 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 1, 3, 2]
def baseStart_3110243 : Nat := 118140960795 + 3110243 * 2 ^ 59
def prefixEnd_3110243 : Nat := 4983230072969 + 3 ^ 40 * 3110243 * 2
def baseEnd_3110243 : Nat := 1597049611281979893658759

theorem tailTrace_3110243 : CollatzResearch.WordTrace tailWord_3110243 prefixEnd_3110243 1597049611281979893658759 := by
  unfold tailWord_3110243
  simp only [CollatzResearch.WordTrace]
  refine ⟨113439881671128273059535383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75626587780752182039690255 113439881671128273059535383)
  ·
    refine ⟨170159822506692409589303075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113439881671128273059535383 170159822506692409589303075)
    ·
      refine ⟨255239733760038614383954613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170159822506692409589303075 255239733760038614383954613)
      ·
        refine ⟨23928725040003620098495745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255239733760038614383954613 23928725040003620098495745)
        ·
          refine ⟨17946543780002715073871809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23928725040003620098495745 17946543780002715073871809)
          ·
            refine ⟨13459907835002036305403857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17946543780002715073871809 13459907835002036305403857)
            ·
              refine ⟨10094930876251527229052893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13459907835002036305403857 10094930876251527229052893)
              ·
                refine ⟨3785599078594322710894835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10094930876251527229052893 3785599078594322710894835)
                ·
                  refine ⟨5678398617891484066342253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785599078594322710894835 5678398617891484066342253)
                  ·
                    refine ⟨2129399481709306524878345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5678398617891484066342253 2129399481709306524878345)
                    ·
                      refine ⟨1597049611281979893658759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129399481709306524878345 1597049611281979893658759)
                      ·
                        rfl

theorem cell23_3110243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_3110243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110243 prefixEnd_3110243 := by exact prefixLift 3110243
  have htrace : WordTrace (prefixWord ++ tailWord_3110243) baseStart_3110243 baseEnd_3110243 := by
    simpa [prefixWord, tailWord_3110243, baseEnd_3110243] using wordTrace_append hprefix tailTrace_3110243
  have hstable : (prefixWord ++ tailWord_3110243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110243).length < 2 ^ (prefixWord ++ tailWord_3110243).sum := by decide
  have hdescent : baseEnd_3110243 < baseStart_3110243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110269 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_3110269 : Nat := 118140960795 + 3110269 * 2 ^ 59
def prefixEnd_3110269 : Nat := 4983230072969 + 3 ^ 40 * 3110269 * 2
def baseEnd_3110269 : Nat := 1597062961778996791933639

theorem tailTrace_3110269 : CollatzResearch.WordTrace tailWord_3110269 prefixEnd_3110269 1597062961778996791933639 := by
  unfold tailWord_3110269
  simp only [CollatzResearch.WordTrace]
  refine ⟨113440829969034079499981861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75627219979356052999987907 113440829969034079499981861)
  ·
    refine ⟨21270155619193889906246599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113440829969034079499981861 21270155619193889906246599)
    ·
      refine ⟨31905233428790834859369899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21270155619193889906246599 31905233428790834859369899)
      ·
        refine ⟨47857850143186252289054849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31905233428790834859369899 47857850143186252289054849)
        ·
          refine ⟨35893387607389689216791137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47857850143186252289054849 35893387607389689216791137)
          ·
            refine ⟨26920040705542266912593353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35893387607389689216791137 26920040705542266912593353)
            ·
              refine ⟨20190030529156700184445015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26920040705542266912593353 20190030529156700184445015)
              ·
                refine ⟨30285045793735050276667523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190030529156700184445015 30285045793735050276667523)
                ·
                  refine ⟨45427568690602575415001285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30285045793735050276667523 45427568690602575415001285)
                  ·
                    refine ⟨8517669129487982890312741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45427568690602575415001285 8517669129487982890312741)
                    ·
                      refine ⟨1597062961778996791933639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8517669129487982890312741 1597062961778996791933639)
                      ·
                        rfl

theorem cell23_3110269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_3110269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110269 prefixEnd_3110269 := by exact prefixLift 3110269
  have htrace : WordTrace (prefixWord ++ tailWord_3110269) baseStart_3110269 baseEnd_3110269 := by
    simpa [prefixWord, tailWord_3110269, baseEnd_3110269] using wordTrace_append hprefix tailTrace_3110269
  have hstable : (prefixWord ++ tailWord_3110269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110269).length < 2 ^ (prefixWord ++ tailWord_3110269).sum := by decide
  have hdescent : baseEnd_3110269 < baseStart_3110269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110289 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_3110289 : Nat := 118140960795 + 3110289 * 2 ^ 59
def prefixEnd_3110289 : Nat := 4983230072969 + 3 ^ 40 * 3110289 * 2
def baseEnd_3110289 : Nat := 1597073231392086713683547

theorem tailTrace_3110289 : CollatzResearch.WordTrace tailWord_3110289 prefixEnd_3110289 1597073231392086713683547 := by
  unfold tailWord_3110289
  simp only [CollatzResearch.WordTrace]
  refine ⟨113441559428961622915709921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75627706285974415277139947 113441559428961622915709921)
  ·
    refine ⟨85081169571721217186782441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113441559428961622915709921 85081169571721217186782441)
    ·
      refine ⟨63810877178790912890086831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85081169571721217186782441 63810877178790912890086831)
      ·
        refine ⟨95716315768186369335130247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63810877178790912890086831 95716315768186369335130247)
        ·
          refine ⟨143574473652279554002695371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95716315768186369335130247 143574473652279554002695371)
          ·
            refine ⟨215361710478419331004043057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143574473652279554002695371 215361710478419331004043057)
            ·
              refine ⟨161521282858814498253032293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215361710478419331004043057 161521282858814498253032293)
              ·
                refine ⟨30285240536027718422443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161521282858814498253032293 30285240536027718422443555)
                ·
                  refine ⟨45427860804041577633665333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30285240536027718422443555 45427860804041577633665333)
                  ·
                    refine ⟨4258861950378897903156125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45427860804041577633665333 4258861950378897903156125)
                    ·
                      refine ⟨1597073231392086713683547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4258861950378897903156125 1597073231392086713683547)
                      ·
                        rfl

theorem cell23_3110289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_3110289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110289 prefixEnd_3110289 := by exact prefixLift 3110289
  have htrace : WordTrace (prefixWord ++ tailWord_3110289) baseStart_3110289 baseEnd_3110289 := by
    simpa [prefixWord, tailWord_3110289, baseEnd_3110289] using wordTrace_append hprefix tailTrace_3110289
  have hstable : (prefixWord ++ tailWord_3110289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110289).length < 2 ^ (prefixWord ++ tailWord_3110289).sum := by decide
  have hdescent : baseEnd_3110289 < baseStart_3110289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110309 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_3110309 : Nat := 118140960795 + 3110309 * 2 ^ 59
def prefixEnd_3110309 : Nat := 4983230072969 + 3 ^ 40 * 3110309 * 2
def baseEnd_3110309 : Nat := 532361167001725545144485

theorem tailTrace_3110309 : CollatzResearch.WordTrace tailWord_3110309 prefixEnd_3110309 532361167001725545144485 := by
  unfold tailWord_3110309
  simp only [CollatzResearch.WordTrace]
  refine ⟨113442288888889166331437981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75628192592592777554291987 113442288888889166331437981)
  ·
    refine ⟨42540858333333437374289243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113442288888889166331437981 42540858333333437374289243)
    ·
      refine ⟨63811287500000156061433865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42540858333333437374289243 63811287500000156061433865)
      ·
        refine ⟨47858465625000117046075399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63811287500000156061433865 47858465625000117046075399)
        ·
          refine ⟨71787698437500175569113099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47858465625000117046075399 71787698437500175569113099)
          ·
            refine ⟨107681547656250263353669649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71787698437500175569113099 107681547656250263353669649)
            ·
              refine ⟨80761160742187697515252237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107681547656250263353669649 80761160742187697515252237)
              ·
                refine ⟨30285435278320386568219589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80761160742187697515252237 30285435278320386568219589)
                ·
                  refine ⟨5678519114685072481541173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30285435278320386568219589 5678519114685072481541173)
                  ·
                    refine ⟨532361167001725545144485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5678519114685072481541173 532361167001725545144485)
                    ·
                      rfl

theorem cell23_3110309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_3110309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110309 prefixEnd_3110309 := by exact prefixLift 3110309
  have htrace : WordTrace (prefixWord ++ tailWord_3110309) baseStart_3110309 baseEnd_3110309 := by
    simpa [prefixWord, tailWord_3110309, baseEnd_3110309] using wordTrace_append hprefix tailTrace_3110309
  have hstable : (prefixWord ++ tailWord_3110309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110309).length < 2 ^ (prefixWord ++ tailWord_3110309).sum := by decide
  have hdescent : baseEnd_3110309 < baseStart_3110309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110316 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_3110316 : Nat := 118140960795 + 3110316 * 2 ^ 59
def prefixEnd_3110316 : Nat := 4983230072969 + 3 ^ 40 * 3110316 * 2
def baseEnd_3110316 : Nat := 1597087095369758108045923

theorem tailTrace_3110316 : CollatzResearch.WordTrace tailWord_3110316 prefixEnd_3110316 1597087095369758108045923 := by
  unfold tailWord_3110316
  simp only [CollatzResearch.WordTrace]
  refine ⟨56721272099931903263471401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75628362799909204351295201 56721272099931903263471401)
  ·
    refine ⟨42540954074948927447603551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56721272099931903263471401 42540954074948927447603551)
    ·
      refine ⟨63811431112423391171405327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42540954074948927447603551 63811431112423391171405327)
      ·
        refine ⟨95717146668635086757107991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63811431112423391171405327 95717146668635086757107991)
        ·
          refine ⟨143575720002952630135661987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95717146668635086757107991 143575720002952630135661987)
          ·
            refine ⟨215363580004428945203492981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143575720002952630135661987 215363580004428945203492981)
            ·
              refine ⟨20190335625415213612827467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215363580004428945203492981 20190335625415213612827467)
              ·
                refine ⟨30285503438122820419241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190335625415213612827467 30285503438122820419241201)
                ·
                  refine ⟨22714127578592115314430901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30285503438122820419241201 22714127578592115314430901)
                  ·
                    refine ⟨2129449460493010810727897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22714127578592115314430901 2129449460493010810727897)
                    ·
                      refine ⟨1597087095369758108045923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129449460493010810727897 1597087095369758108045923)
                      ·
                        rfl

theorem cell23_3110316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_3110316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110316 prefixEnd_3110316 := by exact prefixLift 3110316
  have htrace : WordTrace (prefixWord ++ tailWord_3110316) baseStart_3110316 baseEnd_3110316 := by
    simpa [prefixWord, tailWord_3110316, baseEnd_3110316] using wordTrace_append hprefix tailTrace_3110316
  have hstable : (prefixWord ++ tailWord_3110316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110316).length < 2 ^ (prefixWord ++ tailWord_3110316).sum := by decide
  have hdescent : baseEnd_3110316 < baseStart_3110316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110346 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3110346 : Nat := 118140960795 + 3110346 * 2 ^ 59
def prefixEnd_3110346 : Nat := 4983230072969 + 3 ^ 40 * 3110346 * 2
def baseEnd_3110346 : Nat := 1597102499789392990670785

theorem tailTrace_3110346 : CollatzResearch.WordTrace tailWord_3110346 prefixEnd_3110346 1597102499789392990670785 := by
  unfold tailWord_3110346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28360909597438780412633723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75629092259836747767023261 28360909597438780412633723)
  ·
    refine ⟨42541364396158170618950585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28360909597438780412633723 42541364396158170618950585)
    ·
      refine ⟨31906023297118627964212939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42541364396158170618950585 31906023297118627964212939)
      ·
        refine ⟨47859034945677941946319409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31906023297118627964212939 47859034945677941946319409)
        ·
          refine ⟨35894276209258456459739557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47859034945677941946319409 35894276209258456459739557)
          ·
            refine ⟨6730176789235960586201167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35894276209258456459739557 6730176789235960586201167)
            ·
              refine ⟨10095265183853940879301751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730176789235960586201167 10095265183853940879301751)
              ·
                refine ⟨15142897775780911318952627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10095265183853940879301751 15142897775780911318952627)
                ·
                  refine ⟨22714346663671366978428941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15142897775780911318952627 22714346663671366978428941)
                  ·
                    refine ⟨8517879998876762616910853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22714346663671366978428941 8517879998876762616910853)
                    ·
                      refine ⟨1597102499789392990670785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8517879998876762616910853 1597102499789392990670785)
                      ·
                        rfl

theorem cell23_3110346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3110346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110346 prefixEnd_3110346 := by exact prefixLift 3110346
  have htrace : WordTrace (prefixWord ++ tailWord_3110346) baseStart_3110346 baseEnd_3110346 := by
    simpa [prefixWord, tailWord_3110346, baseEnd_3110346] using wordTrace_append hprefix tailTrace_3110346
  have hstable : (prefixWord ++ tailWord_3110346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110346).length < 2 ^ (prefixWord ++ tailWord_3110346).sum := by decide
  have hdescent : baseEnd_3110346 < baseStart_3110346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110359 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3110359 : Nat := 118140960795 + 3110359 * 2 ^ 59
def prefixEnd_3110359 : Nat := 4983230072969 + 3 ^ 40 * 3110359 * 2
def baseEnd_3110359 : Nat := 1597109175037901439808225

theorem tailTrace_3110359 : CollatzResearch.WordTrace tailWord_3110359 prefixEnd_3110359 1597109175037901439808225 := by
  unfold tailWord_3110359
  simp only [CollatzResearch.WordTrace]
  refine ⟨113444112538708024870758131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75629408359138683247172087 113444112538708024870758131)
  ·
    refine ⟨170166168808062037306137197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113444112538708024870758131 170166168808062037306137197)
    ·
      refine ⟨63812313303023263989801449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170166168808062037306137197 63812313303023263989801449)
      ·
        refine ⟨47859234977267447992351087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63812313303023263989801449 47859234977267447992351087)
        ·
          refine ⟨71788852465901171988526631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47859234977267447992351087 71788852465901171988526631)
          ·
            refine ⟨107683278698851757982789947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71788852465901171988526631 107683278698851757982789947)
            ·
              refine ⟨161524918048277636974184921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107683278698851757982789947 161524918048277636974184921)
              ·
                refine ⟨121143688536208227730638691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161524918048277636974184921 121143688536208227730638691)
                ·
                  refine ⟨181715532804312341595958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121143688536208227730638691 181715532804312341595958037)
                  ·
                    refine ⟨8517915600202141012310533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181715532804312341595958037 8517915600202141012310533)
                    ·
                      refine ⟨1597109175037901439808225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8517915600202141012310533 1597109175037901439808225)
                      ·
                        rfl

theorem cell23_3110359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3110359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110359 prefixEnd_3110359 := by exact prefixLift 3110359
  have htrace : WordTrace (prefixWord ++ tailWord_3110359) baseStart_3110359 baseEnd_3110359 := by
    simpa [prefixWord, tailWord_3110359, baseEnd_3110359] using wordTrace_append hprefix tailTrace_3110359
  have hstable : (prefixWord ++ tailWord_3110359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110359).length < 2 ^ (prefixWord ++ tailWord_3110359).sum := by decide
  have hdescent : baseEnd_3110359 < baseStart_3110359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110373 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_3110373 : Nat := 118140960795 + 3110373 * 2 ^ 59
def prefixEnd_3110373 : Nat := 4983230072969 + 3 ^ 40 * 3110373 * 2
def baseEnd_3110373 : Nat := 532372121255688128344387

theorem tailTrace_3110373 : CollatzResearch.WordTrace tailWord_3110373 prefixEnd_3110373 532372121255688128344387 := by
  unfold tailWord_3110373
  simp only [CollatzResearch.WordTrace]
  refine ⟨113444623160657305261767773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75629748773771536841178515 113444623160657305261767773)
  ·
    refine ⟨42541733685246489473162915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113444623160657305261767773 42541733685246489473162915)
    ·
      refine ⟨63812600527869734209744373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42541733685246489473162915 63812600527869734209744373)
      ·
        refine ⟨5982431299487787582163535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63812600527869734209744373 5982431299487787582163535)
        ·
          refine ⟨8973646949231681373245303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5982431299487787582163535 8973646949231681373245303)
          ·
            refine ⟨13460470423847522059867955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973646949231681373245303 13460470423847522059867955)
            ·
              refine ⟨20190705635771283089801933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460470423847522059867955 20190705635771283089801933)
              ·
                refine ⟨7571514613414231158675725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20190705635771283089801933 7571514613414231158675725)
                ·
                  refine ⟨2839317980030336684503397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7571514613414231158675725 2839317980030336684503397)
                  ·
                    refine ⟨532372121255688128344387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839317980030336684503397 532372121255688128344387)
                    ·
                      rfl

theorem cell23_3110373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_3110373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110373 prefixEnd_3110373 := by exact prefixLift 3110373
  have htrace : WordTrace (prefixWord ++ tailWord_3110373) baseStart_3110373 baseEnd_3110373 := by
    simpa [prefixWord, tailWord_3110373, baseEnd_3110373] using wordTrace_append hprefix tailTrace_3110373
  have hstable : (prefixWord ++ tailWord_3110373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110373).length < 2 ^ (prefixWord ++ tailWord_3110373).sum := by decide
  have hdescent : baseEnd_3110373 < baseStart_3110373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110407 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 1, 4]
def baseStart_3110407 : Nat := 118140960795 + 3110407 * 2 ^ 59
def prefixEnd_3110407 : Nat := 4983230072969 + 3 ^ 40 * 3110407 * 2
def baseEnd_3110407 : Nat := 532377940703105750669335

theorem tailTrace_3110407 : CollatzResearch.WordTrace tailWord_3110407 prefixEnd_3110407 532377940703105750669335 := by
  unfold tailWord_3110407
  simp only [CollatzResearch.WordTrace]
  refine ⟨113445863242534129068505475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75630575495022752712336983 113445863242534129068505475)
  ·
    refine ⟨170168794863801193602758213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113445863242534129068505475 170168794863801193602758213)
    ·
      refine ⟨31906649036962723800517165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170168794863801193602758213 31906649036962723800517165)
      ·
        refine ⟨11964993388861021425193937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31906649036962723800517165 11964993388861021425193937)
        ·
          refine ⟨8973745041645766068895453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11964993388861021425193937 8973745041645766068895453)
          ·
            refine ⟨3365154390617162275835795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8973745041645766068895453 3365154390617162275835795)
            ·
              refine ⟨5047731585925743413753693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365154390617162275835795 5047731585925743413753693)
              ·
                refine ⟨1892899344722153780157635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5047731585925743413753693 1892899344722153780157635)
                ·
                  refine ⟨2839349017083230670236453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892899344722153780157635 2839349017083230670236453)
                  ·
                    refine ⟨532377940703105750669335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839349017083230670236453 532377940703105750669335)
                    ·
                      rfl

theorem cell23_3110407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_3110407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110407 prefixEnd_3110407 := by exact prefixLift 3110407
  have htrace : WordTrace (prefixWord ++ tailWord_3110407) baseStart_3110407 baseEnd_3110407 := by
    simpa [prefixWord, tailWord_3110407, baseEnd_3110407] using wordTrace_append hprefix tailTrace_3110407
  have hstable : (prefixWord ++ tailWord_3110407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110407).length < 2 ^ (prefixWord ++ tailWord_3110407).sum := by decide
  have hdescent : baseEnd_3110407 < baseStart_3110407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110453 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3110453 : Nat := 118140960795 + 3110453 * 2 ^ 59
def prefixEnd_3110453 : Nat := 4983230072969 + 3 ^ 40 * 3110453 * 2
def baseEnd_3110453 : Nat := 1597157442219424072032793

theorem tailTrace_3110453 : CollatzResearch.WordTrace tailWord_3110453 prefixEnd_3110453 1597157442219424072032793 := by
  unfold tailWord_3110453
  simp only [CollatzResearch.WordTrace]
  refine ⟨113447541000367478924680013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75631694000244985949786675 113447541000367478924680013)
  ·
    refine ⟨42542827875137804596755005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113447541000367478924680013 42542827875137804596755005)
    ·
      refine ⟨15953560453176676723783127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42542827875137804596755005 15953560453176676723783127)
      ·
        refine ⟨23930340679765015085674691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15953560453176676723783127 23930340679765015085674691)
        ·
          refine ⟨35895511019647522628512037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23930340679765015085674691 35895511019647522628512037)
          ·
            refine ⟨6730408316183910492846007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35895511019647522628512037 6730408316183910492846007)
            ·
              refine ⟨10095612474275865739269011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730408316183910492846007 10095612474275865739269011)
              ·
                refine ⟨15143418711413798608903517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10095612474275865739269011 15143418711413798608903517)
                ·
                  refine ⟨5678782016780174478338819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15143418711413798608903517 5678782016780174478338819)
                  ·
                    refine ⟨8518173025170261717508229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5678782016780174478338819 8518173025170261717508229)
                    ·
                      refine ⟨1597157442219424072032793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8518173025170261717508229 1597157442219424072032793)
                      ·
                        rfl

theorem cell23_3110453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3110453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110453 prefixEnd_3110453 := by exact prefixLift 3110453
  have htrace : WordTrace (prefixWord ++ tailWord_3110453) baseStart_3110453 baseEnd_3110453 := by
    simpa [prefixWord, tailWord_3110453, baseEnd_3110453] using wordTrace_append hprefix tailTrace_3110453
  have hstable : (prefixWord ++ tailWord_3110453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110453).length < 2 ^ (prefixWord ++ tailWord_3110453).sum := by decide
  have hdescent : baseEnd_3110453 < baseStart_3110453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110473 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_3110473 : Nat := 118140960795 + 3110473 * 2 ^ 59
def prefixEnd_3110473 : Nat := 4983230072969 + 3 ^ 40 * 3110473 * 2
def baseEnd_3110473 : Nat := 1597167711832513993782701

theorem tailTrace_3110473 : CollatzResearch.WordTrace tailWord_3110473 prefixEnd_3110473 1597167711832513993782701 := by
  unfold tailWord_3110473
  simp only [CollatzResearch.WordTrace]
  refine ⟨113448270460295022340408073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75632180306863348226938715 113448270460295022340408073)
  ·
    refine ⟨85086202845221266755306055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113448270460295022340408073 85086202845221266755306055)
    ·
      refine ⟨127629304267831900132959083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85086202845221266755306055 127629304267831900132959083)
      ·
        refine ⟨191443956401747850199438625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127629304267831900132959083 191443956401747850199438625)
        ·
          refine ⟨143582967301310887649578969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191443956401747850199438625 143582967301310887649578969)
          ·
            refine ⟨107687225475983165737184227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143582967301310887649578969 107687225475983165737184227)
            ·
              refine ⟨161530838213974748605776341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107687225475983165737184227 161530838213974748605776341)
              ·
                refine ⟨3785879020640033170447883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161530838213974748605776341 3785879020640033170447883)
                ·
                  refine ⟨5678818530960049755671825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785879020640033170447883 5678818530960049755671825)
                  ·
                    refine ⟨4259113898220037316753869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5678818530960049755671825 4259113898220037316753869)
                    ·
                      refine ⟨1597167711832513993782701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259113898220037316753869 1597167711832513993782701)
                      ·
                        rfl

theorem cell23_3110473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_3110473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110473 prefixEnd_3110473 := by exact prefixLift 3110473
  have htrace : WordTrace (prefixWord ++ tailWord_3110473) baseStart_3110473 baseEnd_3110473 := by
    simpa [prefixWord, tailWord_3110473, baseEnd_3110473] using wordTrace_append hprefix tailTrace_3110473
  have hstable : (prefixWord ++ tailWord_3110473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110473).length < 2 ^ (prefixWord ++ tailWord_3110473).sum := by decide
  have hdescent : baseEnd_3110473 < baseStart_3110473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110503 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3110503 : Nat := 118140960795 + 3110503 * 2 ^ 59
def prefixEnd_3110503 : Nat := 4983230072969 + 3 ^ 40 * 3110503 * 2
def baseEnd_3110503 : Nat := 1597183116252148876407563

theorem tailTrace_3110503 : CollatzResearch.WordTrace tailWord_3110503 prefixEnd_3110503 1597183116252148876407563 := by
  unfold tailWord_3110503
  simp only [CollatzResearch.WordTrace]
  refine ⟨113449364650186337464000163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75632909766790891642666775 113449364650186337464000163)
  ·
    refine ⟨170174046975279506196000245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113449364650186337464000163 170174046975279506196000245)
    ·
      refine ⟨15953816903932453705875023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170174046975279506196000245 15953816903932453705875023)
      ·
        refine ⟨23930725355898680558812535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15953816903932453705875023 23930725355898680558812535)
        ·
          refine ⟨35896088033848020838218803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23930725355898680558812535 35896088033848020838218803)
          ·
            refine ⟨53844132050772031257328205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35896088033848020838218803 53844132050772031257328205)
            ·
              refine ⟨20191549519039511721498077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53844132050772031257328205 20191549519039511721498077)
              ·
                refine ⟨7571831069639816895561779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20191549519039511721498077 7571831069639816895561779)
                ·
                  refine ⟨11357746604459725343342669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571831069639816895561779 11357746604459725343342669)
                  ·
                    refine ⟨4259154976672397003753501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11357746604459725343342669 4259154976672397003753501)
                    ·
                      refine ⟨1597183116252148876407563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259154976672397003753501 1597183116252148876407563)
                      ·
                        rfl

theorem cell23_3110503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3110503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110503 prefixEnd_3110503 := by exact prefixLift 3110503
  have htrace : WordTrace (prefixWord ++ tailWord_3110503) baseStart_3110503 baseEnd_3110503 := by
    simpa [prefixWord, tailWord_3110503, baseEnd_3110503] using wordTrace_append hprefix tailTrace_3110503
  have hstable : (prefixWord ++ tailWord_3110503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110503).length < 2 ^ (prefixWord ++ tailWord_3110503).sum := by decide
  have hdescent : baseEnd_3110503 < baseStart_3110503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110510 : List Nat := [4, 1, 2, 2, 3, 1, 3, 7]
def baseStart_3110510 : Nat := 118140960795 + 3110510 * 2 ^ 59
def prefixEnd_3110510 : Nat := 4983230072969 + 3 ^ 40 * 3110510 * 2
def baseEnd_3110510 : Nat := 59155063356175198111853

theorem tailTrace_3110510 : CollatzResearch.WordTrace tailWord_3110510 prefixEnd_3110510 59155063356175198111853 := by
  unfold tailWord_3110510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181202495145122207438123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75633079974107318439669989 14181202495145122207438123)
  ·
    refine ⟨21271803742717683311157185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14181202495145122207438123 21271803742717683311157185)
    ·
      refine ⟨15953852807038262483367889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21271803742717683311157185 15953852807038262483367889)
      ·
        refine ⟨11965389605278696862525917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15953852807038262483367889 11965389605278696862525917)
        ·
          refine ⟨4487021101979511323447219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11965389605278696862525917 4487021101979511323447219)
          ·
            refine ⟨6730531652969266985170829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487021101979511323447219 6730531652969266985170829)
            ·
              refine ⟨2523949369863475119439061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6730531652969266985170829 2523949369863475119439061)
              ·
                refine ⟨59155063356175198111853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2523949369863475119439061 59155063356175198111853)
                ·
                  rfl

theorem cell23_3110510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_3110510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110510 prefixEnd_3110510 := by exact prefixLift 3110510
  have htrace : WordTrace (prefixWord ++ tailWord_3110510) baseStart_3110510 baseEnd_3110510 := by
    simpa [prefixWord, tailWord_3110510, baseEnd_3110510] using wordTrace_append hprefix tailTrace_3110510
  have hstable : (prefixWord ++ tailWord_3110510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110510).length < 2 ^ (prefixWord ++ tailWord_3110510).sum := by decide
  have hdescent : baseEnd_3110510 < baseStart_3110510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110650 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_3110650 : Nat := 118140960795 + 3110650 * 2 ^ 59
def prefixEnd_3110650 : Nat := 4983230072969 + 3 ^ 40 * 3110650 * 2
def baseEnd_3110650 : Nat := 1597258597908359801269387

theorem tailTrace_3110650 : CollatzResearch.WordTrace tailWord_3110650 prefixEnd_3110650 1597258597908359801269387 := by
  unfold tailWord_3110650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28363681545163445392400351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75636484120435854379734269 28363681545163445392400351)
  ·
    refine ⟨42545522317745168088600527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28363681545163445392400351 42545522317745168088600527)
    ·
      refine ⟨63818283476617752132900791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42545522317745168088600527 63818283476617752132900791)
      ·
        refine ⟨95727425214926628199351187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63818283476617752132900791 95727425214926628199351187)
        ·
          refine ⟨143591137822389942299026781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95727425214926628199351187 143591137822389942299026781)
          ·
            refine ⟨53846676683396228362135043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143591137822389942299026781 53846676683396228362135043)
            ·
              refine ⟨80770015025094342543202565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53846676683396228362135043 80770015025094342543202565)
              ·
                refine ⟨15144377817205189226850481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80770015025094342543202565 15144377817205189226850481)
                ·
                  refine ⟨11358283362903891920137861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15144377817205189226850481 11358283362903891920137861)
                  ·
                    refine ⟨2129678130544479735025849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11358283362903891920137861 2129678130544479735025849)
                    ·
                      refine ⟨1597258597908359801269387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129678130544479735025849 1597258597908359801269387)
                      ·
                        rfl

theorem cell23_3110650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_3110650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110650 prefixEnd_3110650 := by exact prefixLift 3110650
  have htrace : WordTrace (prefixWord ++ tailWord_3110650) baseStart_3110650 baseEnd_3110650 := by
    simpa [prefixWord, tailWord_3110650, baseEnd_3110650] using wordTrace_append hprefix tailTrace_3110650
  have hstable : (prefixWord ++ tailWord_3110650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110650).length < 2 ^ (prefixWord ++ tailWord_3110650).sum := by decide
  have hdescent : baseEnd_3110650 < baseStart_3110650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110670 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3110670 : Nat := 118140960795 + 3110670 * 2 ^ 59
def prefixEnd_3110670 : Nat := 4983230072969 + 3 ^ 40 * 3110670 * 2
def baseEnd_3110670 : Nat := 1597268867521449723019295

theorem tailTrace_3110670 : CollatzResearch.WordTrace tailWord_3110670 prefixEnd_3110670 1597268867521449723019295 := by
  unfold tailWord_3110670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181931955072665623166183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75636970427054216656886309 14181931955072665623166183)
  ·
    refine ⟨21272897932608998434749275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14181931955072665623166183 21272897932608998434749275)
    ·
      refine ⟨31909346898913497652123913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21272897932608998434749275 31909346898913497652123913)
      ·
        refine ⟨23932010174185123239092935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31909346898913497652123913 23932010174185123239092935)
        ·
          refine ⟨35898015261277684858639403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23932010174185123239092935 35898015261277684858639403)
          ·
            refine ⟨53847022891916527287959105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35898015261277684858639403 53847022891916527287959105)
            ·
              refine ⟨40385267168937395465969329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53847022891916527287959105 40385267168937395465969329)
              ·
                refine ⟨30288950376703046599476997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40385267168937395465969329 30288950376703046599476997)
                ·
                  refine ⟨5679178195631821237401937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30288950376703046599476997 5679178195631821237401937)
                  ·
                    refine ⟨4259383646723865928051453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679178195631821237401937 4259383646723865928051453)
                    ·
                      refine ⟨1597268867521449723019295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259383646723865928051453 1597268867521449723019295)
                      ·
                        rfl

theorem cell23_3110670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3110670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110670 prefixEnd_3110670 := by exact prefixLift 3110670
  have htrace : WordTrace (prefixWord ++ tailWord_3110670) baseStart_3110670 baseEnd_3110670 := by
    simpa [prefixWord, tailWord_3110670, baseEnd_3110670] using wordTrace_append hprefix tailTrace_3110670
  have hstable : (prefixWord ++ tailWord_3110670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110670).length < 2 ^ (prefixWord ++ tailWord_3110670).sum := by decide
  have hdescent : baseEnd_3110670 < baseStart_3110670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110683 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3]
def baseStart_3110683 : Nat := 118140960795 + 3110683 * 2 ^ 59
def prefixEnd_3110683 : Nat := 4983230072969 + 3 ^ 40 * 3110683 * 2
def baseEnd_3110683 : Nat := 1597275542769958172156735

theorem tailTrace_3110683 : CollatzResearch.WordTrace tailWord_3110683 prefixEnd_3110683 1597275542769958172156735 := by
  unfold tailWord_3110683
  simp only [CollatzResearch.WordTrace]
  refine ⟨113455929789534228205552703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75637286526356152137035135 113455929789534228205552703)
  ·
    refine ⟨170183894684301342308329055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113455929789534228205552703 170183894684301342308329055)
    ·
      refine ⟨255275842026452013462493583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170183894684301342308329055 255275842026452013462493583)
      ·
        refine ⟨382913763039678020193740375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255275842026452013462493583 382913763039678020193740375)
        ·
          refine ⟨574370644559517030290610563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382913763039678020193740375 574370644559517030290610563)
          ·
            refine ⟨861555966839275545435915845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574370644559517030290610563 861555966839275545435915845)
            ·
              refine ⟨161541743782364164769234221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 861555966839275545435915845 161541743782364164769234221)
              ·
                refine ⟨60578153918386561788462833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161541743782364164769234221 60578153918386561788462833)
                ·
                  refine ⟨45433615438789921341347125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60578153918386561788462833 45433615438789921341347125)
                  ·
                    refine ⟨4259401447386555125751293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45433615438789921341347125 4259401447386555125751293)
                    ·
                      refine ⟨1597275542769958172156735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259401447386555125751293 1597275542769958172156735)
                      ·
                        rfl

theorem cell23_3110683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3].length) (baseStart_3110683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110683 prefixEnd_3110683 := by exact prefixLift 3110683
  have htrace : WordTrace (prefixWord ++ tailWord_3110683) baseStart_3110683 baseEnd_3110683 := by
    simpa [prefixWord, tailWord_3110683, baseEnd_3110683] using wordTrace_append hprefix tailTrace_3110683
  have hstable : (prefixWord ++ tailWord_3110683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110683).length < 2 ^ (prefixWord ++ tailWord_3110683).sum := by decide
  have hdescent : baseEnd_3110683 < baseStart_3110683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110707 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 6]
def baseStart_3110707 : Nat := 118140960795 + 3110707 * 2 ^ 59
def prefixEnd_3110707 : Nat := 4983230072969 + 3 ^ 40 * 3110707 * 2
def baseEnd_3110707 : Nat := 177476429589518453139625

theorem tailTrace_3110707 : CollatzResearch.WordTrace tailWord_3110707 prefixEnd_3110707 177476429589518453139625 := by
  unfold tailWord_3110707
  simp only [CollatzResearch.WordTrace]
  refine ⟨113456805141447280304426375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75637870094298186869617583 113456805141447280304426375)
  ·
    refine ⟨170185207712170920456639563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113456805141447280304426375 170185207712170920456639563)
    ·
      refine ⟨255277811568256380684959345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170185207712170920456639563 255277811568256380684959345)
      ·
        refine ⟨191458358676192285513719509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255277811568256380684959345 191458358676192285513719509)
        ·
          refine ⟨4487305281473256691727801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 191458358676192285513719509 4487305281473256691727801)
          ·
            refine ⟨3365478961104942518795851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487305281473256691727801 3365478961104942518795851)
            ·
              refine ⟨5048218441657413778193777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365478961104942518795851 5048218441657413778193777)
              ·
                refine ⟨3786163831243060333645333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048218441657413778193777 3786163831243060333645333)
                ·
                  refine ⟨177476429589518453139625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3786163831243060333645333 177476429589518453139625)
                  ·
                    rfl

theorem cell23_3110707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 6].length) (baseStart_3110707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110707 prefixEnd_3110707 := by exact prefixLift 3110707
  have htrace : WordTrace (prefixWord ++ tailWord_3110707) baseStart_3110707 baseEnd_3110707 := by
    simpa [prefixWord, tailWord_3110707, baseEnd_3110707] using wordTrace_append hprefix tailTrace_3110707
  have hstable : (prefixWord ++ tailWord_3110707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110707).length < 2 ^ (prefixWord ++ tailWord_3110707).sum := by decide
  have hdescent : baseEnd_3110707 < baseStart_3110707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110737 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_3110737 : Nat := 118140960795 + 3110737 * 2 ^ 59
def prefixEnd_3110737 : Nat := 4983230072969 + 3 ^ 40 * 3110737 * 2
def baseEnd_3110737 : Nat := 532434423575100320293829

theorem tailTrace_3110737 : CollatzResearch.WordTrace tailWord_3110737 prefixEnd_3110737 532434423575100320293829 := by
  unfold tailWord_3110737
  simp only [CollatzResearch.WordTrace]
  refine ⟨113457899331338595428018465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75638599554225730285345643 113457899331338595428018465)
  ·
    refine ⟨85093424498503946571013849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113457899331338595428018465 85093424498503946571013849)
    ·
      refine ⟨63820068373877959928260387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85093424498503946571013849 63820068373877959928260387)
      ·
        refine ⟨95730102560816939892390581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63820068373877959928260387 95730102560816939892390581)
        ·
          refine ⟨8974697115076588114911617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95730102560816939892390581 8974697115076588114911617)
          ·
            refine ⟨6731022836307441086183713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8974697115076588114911617 6731022836307441086183713)
            ·
              refine ⟨5048267127230580814637785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6731022836307441086183713 5048267127230580814637785)
              ·
                refine ⟨3786200345422935610978339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048267127230580814637785 3786200345422935610978339)
                ·
                  refine ⟨5679300518134403416467509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786200345422935610978339 5679300518134403416467509)
                  ·
                    refine ⟨532434423575100320293829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5679300518134403416467509 532434423575100320293829)
                    ·
                      rfl

theorem cell23_3110737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_3110737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110737 prefixEnd_3110737 := by exact prefixLift 3110737
  have htrace : WordTrace (prefixWord ++ tailWord_3110737) baseStart_3110737 baseEnd_3110737 := by
    simpa [prefixWord, tailWord_3110737, baseEnd_3110737] using wordTrace_append hprefix tailTrace_3110737
  have hstable : (prefixWord ++ tailWord_3110737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110737).length < 2 ^ (prefixWord ++ tailWord_3110737).sum := by decide
  have hdescent : baseEnd_3110737 < baseStart_3110737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110751 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 1, 1, 3]
def baseStart_3110751 : Nat := 118140960795 + 3110751 * 2 ^ 59
def prefixEnd_3110751 : Nat := 4983230072969 + 3 ^ 40 * 3110751 * 2
def baseEnd_3110751 : Nat := 1597310459454463906106423

theorem tailTrace_3110751 : CollatzResearch.WordTrace tailWord_3110751 prefixEnd_3110751 1597310459454463906106423 := by
  unfold tailWord_3110751
  simp only [CollatzResearch.WordTrace]
  refine ⟨113458409953287875819028107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75638939968858583879352071 113458409953287875819028107)
  ·
    refine ⟨170187614929931813728542161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113458409953287875819028107 170187614929931813728542161)
    ·
      refine ⟨127640711197448860296406621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170187614929931813728542161 127640711197448860296406621)
      ·
        refine ⟨47865266699043322611152483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127640711197448860296406621 47865266699043322611152483)
        ·
          refine ⟨71797900048564983916728725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47865266699043322611152483 71797900048564983916728725)
          ·
            refine ⟨3365526564776483621096659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71797900048564983916728725 3365526564776483621096659)
            ·
              refine ⟨5048289847164725431644989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365526564776483621096659 5048289847164725431644989)
              ·
                refine ⟨1893108692686772036866871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5048289847164725431644989 1893108692686772036866871)
                ·
                  refine ⟨2839663039030158055300307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893108692686772036866871 2839663039030158055300307)
                  ·
                    refine ⟨4259494558545237082950461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2839663039030158055300307 4259494558545237082950461)
                    ·
                      refine ⟨1597310459454463906106423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259494558545237082950461 1597310459454463906106423)
                      ·
                        rfl

theorem cell23_3110751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_3110751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110751 prefixEnd_3110751 := by exact prefixLift 3110751
  have htrace : WordTrace (prefixWord ++ tailWord_3110751) baseStart_3110751 baseEnd_3110751 := by
    simpa [prefixWord, tailWord_3110751, baseEnd_3110751] using wordTrace_append hprefix tailTrace_3110751
  have hstable : (prefixWord ++ tailWord_3110751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110751).length < 2 ^ (prefixWord ++ tailWord_3110751).sum := by decide
  have hdescent : baseEnd_3110751 < baseStart_3110751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110783 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3110783 : Nat := 118140960795 + 3110783 * 2 ^ 59
def prefixEnd_3110783 : Nat := 4983230072969 + 3 ^ 40 * 3110783 * 2
def baseEnd_3110783 : Nat := 1597326890835407780906275

theorem tailTrace_3110783 : CollatzResearch.WordTrace tailWord_3110783 prefixEnd_3110783 1597326890835407780906275 := by
  unfold tailWord_3110783
  simp only [CollatzResearch.WordTrace]
  refine ⟨113459577089171945284193003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75639718059447963522795335 113459577089171945284193003)
  ·
    refine ⟨170189365633757917926289505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113459577089171945284193003 170189365633757917926289505)
    ·
      refine ⟨127642024225318438444717129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170189365633757917926289505 127642024225318438444717129)
      ·
        refine ⟨95731518168988828833537847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127642024225318438444717129 95731518168988828833537847)
        ·
          refine ⟨143597277253483243250306771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95731518168988828833537847 143597277253483243250306771)
          ·
            refine ⟨215395915880224864875460157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143597277253483243250306771 215395915880224864875460157)
            ·
              refine ⟨80773468455084324328297559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215395915880224864875460157 80773468455084324328297559)
              ·
                refine ⟨121160202682626486492446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80773468455084324328297559 121160202682626486492446339)
                ·
                  refine ⟨181740304023939729738669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121160202682626486492446339 181740304023939729738669509)
                  ·
                    refine ⟨34076307004488699326000533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181740304023939729738669509 34076307004488699326000533)
                    ·
                      refine ⟨1597326890835407780906275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34076307004488699326000533 1597326890835407780906275)
                      ·
                        rfl

theorem cell23_3110783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3110783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110783 prefixEnd_3110783 := by exact prefixLift 3110783
  have htrace : WordTrace (prefixWord ++ tailWord_3110783) baseStart_3110783 baseEnd_3110783 := by
    simpa [prefixWord, tailWord_3110783, baseEnd_3110783] using wordTrace_append hprefix tailTrace_3110783
  have hstable : (prefixWord ++ tailWord_3110783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110783).length < 2 ^ (prefixWord ++ tailWord_3110783).sum := by decide
  have hdescent : baseEnd_3110783 < baseStart_3110783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110791 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_3110791 : Nat := 118140960795 + 3110791 * 2 ^ 59
def prefixEnd_3110791 : Nat := 4983230072969 + 3 ^ 40 * 3110791 * 2
def baseEnd_3110791 : Nat := 1597330998680643749606239

theorem tailTrace_3110791 : CollatzResearch.WordTrace tailWord_3110791 prefixEnd_3110791 1597330998680643749606239 := by
  unfold tailWord_3110791
  simp only [CollatzResearch.WordTrace]
  refine ⟨113459868873142962650484227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75639912582095308433656151 113459868873142962650484227)
  ·
    refine ⟨170189803309714443975726341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113459868873142962650484227 170189803309714443975726341)
    ·
      refine ⟨31910588120571458245448689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170189803309714443975726341 31910588120571458245448689)
      ·
        refine ⟨23932941090428593684086517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31910588120571458245448689 23932941090428593684086517)
        ·
          refine ⟨2243713227227680657883111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23932941090428593684086517 2243713227227680657883111)
          ·
            refine ⟨3365569840841520986824667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243713227227680657883111 3365569840841520986824667)
            ·
              refine ⟨5048354761262281480237001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365569840841520986824667 5048354761262281480237001)
              ·
                refine ⟨3786266070946711110177751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048354761262281480237001 3786266070946711110177751)
                ·
                  refine ⟨5679399106420066665266627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786266070946711110177751 5679399106420066665266627)
                  ·
                    refine ⟨8519098659630099997899941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5679399106420066665266627 8519098659630099997899941)
                    ·
                      refine ⟨1597330998680643749606239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8519098659630099997899941 1597330998680643749606239)
                      ·
                        rfl

theorem cell23_3110791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_3110791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110791 prefixEnd_3110791 := by exact prefixLift 3110791
  have htrace : WordTrace (prefixWord ++ tailWord_3110791) baseStart_3110791 baseEnd_3110791 := by
    simpa [prefixWord, tailWord_3110791, baseEnd_3110791] using wordTrace_append hprefix tailTrace_3110791
  have hstable : (prefixWord ++ tailWord_3110791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110791).length < 2 ^ (prefixWord ++ tailWord_3110791).sum := by decide
  have hdescent : baseEnd_3110791 < baseStart_3110791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110794 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3110794 : Nat := 118140960795 + 3110794 * 2 ^ 59
def prefixEnd_3110794 : Nat := 4983230072969 + 3 ^ 40 * 3110794 * 2
def baseEnd_3110794 : Nat := 1597332539122607237868725

theorem tailTrace_3110794 : CollatzResearch.WordTrace tailWord_3110794 prefixEnd_3110794 1597332539122607237868725 := by
  unfold tailWord_3110794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28364994573033023540710859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75639985528088062775228957 28364994573033023540710859)
  ·
    refine ⟨42547491859549535311066289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28364994573033023540710859 42547491859549535311066289)
    ·
      refine ⟨31910618894662151483299717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42547491859549535311066289 31910618894662151483299717)
      ·
        refine ⟨5983241042749153403118697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31910618894662151483299717 5983241042749153403118697)
        ·
          refine ⟨4487430782061865052339023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5983241042749153403118697 4487430782061865052339023)
          ·
            refine ⟨6731146173092797578508535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487430782061865052339023 6731146173092797578508535)
            ·
              refine ⟨10096719259639196367762803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731146173092797578508535 10096719259639196367762803)
              ·
                refine ⟨15145078889458794551644205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096719259639196367762803 15145078889458794551644205)
                ·
                  refine ⟨5679404583547047956866577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15145078889458794551644205 5679404583547047956866577)
                  ·
                    refine ⟨4259553437660285967649933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679404583547047956866577 4259553437660285967649933)
                    ·
                      refine ⟨1597332539122607237868725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259553437660285967649933 1597332539122607237868725)
                      ·
                        rfl

theorem cell23_3110794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3110794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110794 prefixEnd_3110794 := by exact prefixLift 3110794
  have htrace : WordTrace (prefixWord ++ tailWord_3110794) baseStart_3110794 baseEnd_3110794 := by
    simpa [prefixWord, tailWord_3110794, baseEnd_3110794] using wordTrace_append hprefix tailTrace_3110794
  have hstable : (prefixWord ++ tailWord_3110794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110794).length < 2 ^ (prefixWord ++ tailWord_3110794).sum := by decide
  have hdescent : baseEnd_3110794 < baseStart_3110794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110803 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_3110803 : Nat := 118140960795 + 3110803 * 2 ^ 59
def prefixEnd_3110803 : Nat := 4983230072969 + 3 ^ 40 * 3110803 * 2
def baseEnd_3110803 : Nat := 1597337160448497702656183

theorem tailTrace_3110803 : CollatzResearch.WordTrace tailWord_3110803 prefixEnd_3110803 1597337160448497702656183 := by
  unfold tailWord_3110803
  simp only [CollatzResearch.WordTrace]
  refine ⟨113460306549099488699921063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75640204366066325799947375 113460306549099488699921063)
  ·
    refine ⟨170190459823649233049881595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113460306549099488699921063 170190459823649233049881595)
    ·
      refine ⟨255285689735473849574822393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170190459823649233049881595 255285689735473849574822393)
      ·
        refine ⟨191464267301605387181116795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255285689735473849574822393 191464267301605387181116795)
        ·
          refine ⟨287196400952408080771675193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191464267301605387181116795 287196400952408080771675193)
          ·
            refine ⟨215397300714306060578756395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287196400952408080771675193 215397300714306060578756395)
            ·
              refine ⟨323095951071459090868134593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215397300714306060578756395 323095951071459090868134593)
              ·
                refine ⟨242321963303594318151100945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323095951071459090868134593 242321963303594318151100945)
                ·
                  refine ⟨181741472477695738613325709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242321963303594318151100945 181741472477695738613325709)
                  ·
                    refine ⟨68153052179135901979997141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181741472477695738613325709 68153052179135901979997141)
                    ·
                      refine ⟨1597337160448497702656183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68153052179135901979997141 1597337160448497702656183)
                      ·
                        rfl

theorem cell23_3110803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_3110803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110803 prefixEnd_3110803 := by exact prefixLift 3110803
  have htrace : WordTrace (prefixWord ++ tailWord_3110803) baseStart_3110803 baseEnd_3110803 := by
    simpa [prefixWord, tailWord_3110803, baseEnd_3110803] using wordTrace_append hprefix tailTrace_3110803
  have hstable : (prefixWord ++ tailWord_3110803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110803).length < 2 ^ (prefixWord ++ tailWord_3110803).sum := by decide
  have hdescent : baseEnd_3110803 < baseStart_3110803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110807 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3110807 : Nat := 118140960795 + 3110807 * 2 ^ 59
def prefixEnd_3110807 : Nat := 4983230072969 + 3 ^ 40 * 3110807 * 2
def baseEnd_3110807 : Nat := 1597339214371115687006165

theorem tailTrace_3110807 : CollatzResearch.WordTrace tailWord_3110807 prefixEnd_3110807 1597339214371115687006165 := by
  unfold tailWord_3110807
  simp only [CollatzResearch.WordTrace]
  refine ⟨113460452441084997383066675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75640301627389998255377783 113460452441084997383066675)
  ·
    refine ⟨170190678661627496074600013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113460452441084997383066675 170190678661627496074600013)
    ·
      refine ⟨63821504498110311027975005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170190678661627496074600013 63821504498110311027975005)
      ·
        refine ⟨23933064186791366635490627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63821504498110311027975005 23933064186791366635490627)
        ·
          refine ⟨35899596280187049953235941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23933064186791366635490627 35899596280187049953235941)
          ·
            refine ⟨6731174302535071866231739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35899596280187049953235941 6731174302535071866231739)
            ·
              refine ⟨10096761453802607799347609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731174302535071866231739 10096761453802607799347609)
              ·
                refine ⟨7572571090351955849510707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10096761453802607799347609 7572571090351955849510707)
                ·
                  refine ⟨11358856635527933774266061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572571090351955849510707 11358856635527933774266061)
                  ·
                    refine ⟨4259571238322975165349773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11358856635527933774266061 4259571238322975165349773)
                    ·
                      refine ⟨1597339214371115687006165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259571238322975165349773 1597339214371115687006165)
                      ·
                        rfl

theorem cell23_3110807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3110807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110807 prefixEnd_3110807 := by exact prefixLift 3110807
  have htrace : WordTrace (prefixWord ++ tailWord_3110807) baseStart_3110807 baseEnd_3110807 := by
    simpa [prefixWord, tailWord_3110807, baseEnd_3110807] using wordTrace_append hprefix tailTrace_3110807
  have hstable : (prefixWord ++ tailWord_3110807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110807).length < 2 ^ (prefixWord ++ tailWord_3110807).sum := by decide
  have hdescent : baseEnd_3110807 < baseStart_3110807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110814 : List Nat := [4, 3, 1, 3, 2, 10]
def baseStart_3110814 : Nat := 118140960795 + 3110814 * 2 ^ 59
def prefixEnd_3110814 : Nat := 4983230072969 + 3 ^ 40 * 3110814 * 2
def baseEnd_3110814 : Nat := 6573427196443198187731

theorem tailTrace_3110814 : CollatzResearch.WordTrace tailWord_3110814 prefixEnd_3110814 6573427196443198187731 := by
  unfold tailWord_3110814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182588469007454697321437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75640471834706425052380997 14182588469007454697321437)
  ·
    refine ⟨5318470675877795511495539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14182588469007454697321437 5318470675877795511495539)
    ·
      refine ⟨7977706013816693267243309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318470675877795511495539 7977706013816693267243309)
      ·
        refine ⟨2991639755181259975216241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7977706013816693267243309 2991639755181259975216241)
        ·
          refine ⟨2243729816385944981412181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2991639755181259975216241 2243729816385944981412181)
          ·
            refine ⟨6573427196443198187731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2243729816385944981412181 6573427196443198187731)
            ·
              rfl

theorem cell23_3110814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 10].length) (baseStart_3110814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110814 prefixEnd_3110814 := by exact prefixLift 3110814
  have htrace : WordTrace (prefixWord ++ tailWord_3110814) baseStart_3110814 baseEnd_3110814 := by
    simpa [prefixWord, tailWord_3110814, baseEnd_3110814] using wordTrace_append hprefix tailTrace_3110814
  have hstable : (prefixWord ++ tailWord_3110814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110814).length < 2 ^ (prefixWord ++ tailWord_3110814).sum := by decide
  have hdescent : baseEnd_3110814 < baseStart_3110814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110840 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_3110840 : Nat := 118140960795 + 3110840 * 2 ^ 59
def prefixEnd_3110840 : Nat := 4983230072969 + 3 ^ 40 * 3110840 * 2
def baseEnd_3110840 : Nat := 532452053077571352631171

theorem tailTrace_3110840 : CollatzResearch.WordTrace tailWord_3110840 prefixEnd_3110840 532452053077571352631171 := by
  unfold tailWord_3110840
  simp only [CollatzResearch.WordTrace]
  refine ⟨56730828024982722009508987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75641104033310296012678649 56730828024982722009508987)
  ·
    refine ⟨85096242037474083014263481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56730828024982722009508987 85096242037474083014263481)
    ·
      refine ⟨63822181528105562260697611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85096242037474083014263481 63822181528105562260697611)
      ·
        refine ⟨95733272292158343391046417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63822181528105562260697611 95733272292158343391046417)
        ·
          refine ⟨71799954219118757543284813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95733272292158343391046417 71799954219118757543284813)
          ·
            refine ⟨26924982832169534078731805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71799954219118757543284813 26924982832169534078731805)
            ·
              refine ⟨10096868562063575279524427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26924982832169534078731805 10096868562063575279524427)
              ·
                refine ⟨15145302843095362919286641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096868562063575279524427 15145302843095362919286641)
                ·
                  refine ⟨11358977132321522189464981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15145302843095362919286641 11358977132321522189464981)
                  ·
                    refine ⟨532452053077571352631171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11358977132321522189464981 532452053077571352631171)
                    ·
                      rfl

theorem cell23_3110840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_3110840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110840 prefixEnd_3110840 := by exact prefixLift 3110840
  have htrace : WordTrace (prefixWord ++ tailWord_3110840) baseStart_3110840 baseEnd_3110840 := by
    simpa [prefixWord, tailWord_3110840, baseEnd_3110840] using wordTrace_append hprefix tailTrace_3110840
  have hstable : (prefixWord ++ tailWord_3110840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110840).length < 2 ^ (prefixWord ++ tailWord_3110840).sum := by decide
  have hdescent : baseEnd_3110840 < baseStart_3110840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110881 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_3110881 : Nat := 118140960795 + 3110881 * 2 ^ 59
def prefixEnd_3110881 : Nat := 4983230072969 + 3 ^ 40 * 3110881 * 2
def baseEnd_3110881 : Nat := 1597377211939548397480825

theorem tailTrace_3110881 : CollatzResearch.WordTrace tailWord_3110881 prefixEnd_3110881 1597377211939548397480825 := by
  unfold tailWord_3110881
  simp only [CollatzResearch.WordTrace]
  refine ⟨113463151442816908021260497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75642100961877938680840331 113463151442816908021260497)
  ·
    refine ⟨85097363582112681015945373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113463151442816908021260497 85097363582112681015945373)
    ·
      refine ⟨31911511343292255380979515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85097363582112681015945373 31911511343292255380979515)
      ·
        refine ⟨47867267014938383071469273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31911511343292255380979515 47867267014938383071469273)
        ·
          refine ⟨35900450261203787303601955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47867267014938383071469273 35900450261203787303601955)
          ·
            refine ⟨53850675391805680955402933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35900450261203787303601955 53850675391805680955402933)
            ·
              refine ⟨5048500817981782589569025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53850675391805680955402933 5048500817981782589569025)
              ·
                refine ⟨3786375613486336942176769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048500817981782589569025 3786375613486336942176769)
                ·
                  refine ⟨2839781710114752706632577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786375613486336942176769 2839781710114752706632577)
                  ·
                    refine ⟨2129836282586064529974433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2839781710114752706632577 2129836282586064529974433)
                    ·
                      refine ⟨1597377211939548397480825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129836282586064529974433 1597377211939548397480825)
                      ·
                        rfl

theorem cell23_3110881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_3110881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110881 prefixEnd_3110881 := by exact prefixLift 3110881
  have htrace : WordTrace (prefixWord ++ tailWord_3110881) baseStart_3110881 baseEnd_3110881 := by
    simpa [prefixWord, tailWord_3110881, baseEnd_3110881] using wordTrace_append hprefix tailTrace_3110881
  have hstable : (prefixWord ++ tailWord_3110881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110881).length < 2 ^ (prefixWord ++ tailWord_3110881).sum := by decide
  have hdescent : baseEnd_3110881 < baseStart_3110881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110907 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 5, 2]
def baseStart_3110907 : Nat := 118140960795 + 3110907 * 2 ^ 59
def prefixEnd_3110907 : Nat := 4983230072969 + 3 ^ 40 * 3110907 * 2
def baseEnd_3110907 : Nat := 1597390562436565295755705

theorem tailTrace_3110907 : CollatzResearch.WordTrace tailWord_3110907 prefixEnd_3110907 1597390562436565295755705 := by
  unfold tailWord_3110907
  simp only [CollatzResearch.WordTrace]
  refine ⟨113464099740722714461706975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75642733160481809641137983 113464099740722714461706975)
  ·
    refine ⟨170196149611084071692560463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113464099740722714461706975 170196149611084071692560463)
    ·
      refine ⟨255294224416626107538840695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170196149611084071692560463 255294224416626107538840695)
      ·
        refine ⟨382941336624939161308261043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255294224416626107538840695 382941336624939161308261043)
        ·
          refine ⟨574412004937408741962391565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382941336624939161308261043 574412004937408741962391565)
          ·
            refine ⟨215404501851528278235896837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574412004937408741962391565 215404501851528278235896837)
            ·
              refine ⟨40388344097161552169230657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215404501851528278235896837 40388344097161552169230657)
              ·
                refine ⟨30291258072871164126922993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40388344097161552169230657 30291258072871164126922993)
                ·
                  refine ⟨22718443554653373095192245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30291258072871164126922993 22718443554653373095192245)
                  ·
                    refine ⟨2129854083248753727674273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22718443554653373095192245 2129854083248753727674273)
                    ·
                      refine ⟨1597390562436565295755705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129854083248753727674273 1597390562436565295755705)
                      ·
                        rfl

theorem cell23_3110907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5, 2].length) (baseStart_3110907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3110907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3110907 prefixEnd_3110907 := by exact prefixLift 3110907
  have htrace : WordTrace (prefixWord ++ tailWord_3110907) baseStart_3110907 baseEnd_3110907 := by
    simpa [prefixWord, tailWord_3110907, baseEnd_3110907] using wordTrace_append hprefix tailTrace_3110907
  have hstable : (prefixWord ++ tailWord_3110907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110907).length < 2 ^ (prefixWord ++ tailWord_3110907).sum := by decide
  have hdescent : baseEnd_3110907 < baseStart_3110907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111021 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3111021 : Nat := 118140960795 + 3111021 * 2 ^ 59
def prefixEnd_3111021 : Nat := 4983230072969 + 3 ^ 40 * 3111021 * 2
def baseEnd_3111021 : Nat := 1597449099231177849730181

theorem tailTrace_3111021 : CollatzResearch.WordTrace tailWord_3111021 prefixEnd_3111021 1597449099231177849730181 := by
  unfold tailWord_3111021
  simp only [CollatzResearch.WordTrace]
  refine ⟨113468257662309711931356917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75645505108206474620904611 113468257662309711931356917)
  ·
    refine ⟨10637649155841535493564711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113468257662309711931356917 10637649155841535493564711)
    ·
      refine ⟨15956473733762303240347067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10637649155841535493564711 15956473733762303240347067)
      ·
        refine ⟨23934710600643454860520601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15956473733762303240347067 23934710600643454860520601)
        ·
          refine ⟨17951032950482591145390451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23934710600643454860520601 17951032950482591145390451)
          ·
            refine ⟨26926549425723886718085677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17951032950482591145390451 26926549425723886718085677)
            ·
              refine ⟨10097456034646457519282129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26926549425723886718085677 10097456034646457519282129)
              ·
                refine ⟨7573092025984843139461597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10097456034646457519282129 7573092025984843139461597)
                ·
                  refine ⟨2839909509744316177298099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7573092025984843139461597 2839909509744316177298099)
                  ·
                    refine ⟨4259864264616474265947149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2839909509744316177298099 4259864264616474265947149)
                    ·
                      refine ⟨1597449099231177849730181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4259864264616474265947149 1597449099231177849730181)
                      ·
                        rfl

theorem cell23_3111021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3111021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111021 prefixEnd_3111021 := by exact prefixLift 3111021
  have htrace : WordTrace (prefixWord ++ tailWord_3111021) baseStart_3111021 baseEnd_3111021 := by
    simpa [prefixWord, tailWord_3111021, baseEnd_3111021] using wordTrace_append hprefix tailTrace_3111021
  have hstable : (prefixWord ++ tailWord_3111021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111021).length < 2 ^ (prefixWord ++ tailWord_3111021).sum := by decide
  have hdescent : baseEnd_3111021 < baseStart_3111021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111031 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_3111031 : Nat := 118140960795 + 3111031 * 2 ^ 59
def prefixEnd_3111031 : Nat := 4983230072969 + 3 ^ 40 * 3111031 * 2
def baseEnd_3111031 : Nat := 1597454234037722810605135

theorem tailTrace_3111031 : CollatzResearch.WordTrace tailWord_3111031 prefixEnd_3111031 1597454234037722810605135 := by
  unfold tailWord_3111031
  simp only [CollatzResearch.WordTrace]
  refine ⟨113468622392273483639220947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75645748261515655759480631 113468622392273483639220947)
  ·
    refine ⟨170202933588410225458831421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113468622392273483639220947 170202933588410225458831421)
    ·
      refine ⟨63826100095653834547061783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170202933588410225458831421 63826100095653834547061783)
      ·
        refine ⟨95739150143480751820592675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63826100095653834547061783 95739150143480751820592675)
        ·
          refine ⟨143608725215221127730889013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95739150143480751820592675 143608725215221127730889013)
          ·
            refine ⟨13463317988926980724770845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143608725215221127730889013 13463317988926980724770845)
            ·
              refine ⟨5048744245847617771789067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13463317988926980724770845 5048744245847617771789067)
              ·
                refine ⟨7573116368771426657683601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048744245847617771789067 7573116368771426657683601)
                ·
                  refine ⟨5679837276578569993262701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7573116368771426657683601 5679837276578569993262701)
                  ·
                    refine ⟨2129938978716963747473513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5679837276578569993262701 2129938978716963747473513)
                    ·
                      refine ⟨1597454234037722810605135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129938978716963747473513 1597454234037722810605135)
                      ·
                        rfl

theorem cell23_3111031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_3111031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111031 prefixEnd_3111031 := by exact prefixLift 3111031
  have htrace : WordTrace (prefixWord ++ tailWord_3111031) baseStart_3111031 baseEnd_3111031 := by
    simpa [prefixWord, tailWord_3111031, baseEnd_3111031] using wordTrace_append hprefix tailTrace_3111031
  have hstable : (prefixWord ++ tailWord_3111031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111031).length < 2 ^ (prefixWord ++ tailWord_3111031).sum := by decide
  have hdescent : baseEnd_3111031 < baseStart_3111031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111041 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3111041 : Nat := 118140960795 + 3111041 * 2 ^ 59
def prefixEnd_3111041 : Nat := 4983230072969 + 3 ^ 40 * 3111041 * 2
def baseEnd_3111041 : Nat := 532486456281422590493363

theorem tailTrace_3111041 : CollatzResearch.WordTrace tailWord_3111041 prefixEnd_3111041 532486456281422590493363 := by
  unfold tailWord_3111041
  simp only [CollatzResearch.WordTrace]
  refine ⟨113468987122237255347084977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75645991414824836898056651 113468987122237255347084977)
  ·
    refine ⟨85101740341677941510313733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113468987122237255347084977 85101740341677941510313733)
    ·
      refine ⟨15956576314064614033183825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85101740341677941510313733 15956576314064614033183825)
      ·
        refine ⟨11967432235548460524887869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15956576314064614033183825 11967432235548460524887869)
        ·
          refine ⟨4487787088330672696832951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11967432235548460524887869 4487787088330672696832951)
          ·
            refine ⟨6731680632496009045249427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487787088330672696832951 6731680632496009045249427)
            ·
              refine ⟨10097520948744013567874141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731680632496009045249427 10097520948744013567874141)
              ·
                refine ⟨3786570355779005087952803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10097520948744013567874141 3786570355779005087952803)
                ·
                  refine ⟨5679855533668507631929205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786570355779005087952803 5679855533668507631929205)
                  ·
                    refine ⟨532486456281422590493363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5679855533668507631929205 532486456281422590493363)
                    ·
                      rfl

theorem cell23_3111041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3111041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111041 prefixEnd_3111041 := by exact prefixLift 3111041
  have htrace : WordTrace (prefixWord ++ tailWord_3111041) baseStart_3111041 baseEnd_3111041 := by
    simpa [prefixWord, tailWord_3111041, baseEnd_3111041] using wordTrace_append hprefix tailTrace_3111041
  have hstable : (prefixWord ++ tailWord_3111041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111041).length < 2 ^ (prefixWord ++ tailWord_3111041).sum := by decide
  have hdescent : baseEnd_3111041 < baseStart_3111041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111071 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 1, 6]
def baseStart_3111071 : Nat := 118140960795 + 3111071 * 2 ^ 59
def prefixEnd_3111071 : Nat := 4983230072969 + 3 ^ 40 * 3111071 * 2
def baseEnd_3111071 : Nat := 532491591087967551368317

theorem tailTrace_3111071 : CollatzResearch.WordTrace tailWord_3111071 prefixEnd_3111071 532491591087967551368317 := by
  unfold tailWord_3111071
  simp only [CollatzResearch.WordTrace]
  refine ⟨113470081312128570470677067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75646720874752380313784711 113470081312128570470677067)
  ·
    refine ⟨170205121968192855706015601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113470081312128570470677067 170205121968192855706015601)
    ·
      refine ⟨127653841476144641779511701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170205121968192855706015601 127653841476144641779511701)
      ·
        refine ⟨5983773819194280083414611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127653841476144641779511701 5983773819194280083414611)
        ·
          refine ⟨8975660728791420125121917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983773819194280083414611 8975660728791420125121917)
          ·
            refine ⟨3365872773296782546920719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8975660728791420125121917 3365872773296782546920719)
            ·
              refine ⟨5048809159945173820381079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365872773296782546920719 5048809159945173820381079)
              ·
                refine ⟨7573213739917760730571619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048809159945173820381079 7573213739917760730571619)
                ·
                  refine ⟨11359820609876641095857429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7573213739917760730571619 11359820609876641095857429)
                  ·
                    refine ⟨532491591087967551368317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11359820609876641095857429 532491591087967551368317)
                    ·
                      rfl

theorem cell23_3111071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_3111071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111071 prefixEnd_3111071 := by exact prefixLift 3111071
  have htrace : WordTrace (prefixWord ++ tailWord_3111071) baseStart_3111071 baseEnd_3111071 := by
    simpa [prefixWord, tailWord_3111071, baseEnd_3111071] using wordTrace_append hprefix tailTrace_3111071
  have hstable : (prefixWord ++ tailWord_3111071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111071).length < 2 ^ (prefixWord ++ tailWord_3111071).sum := by decide
  have hdescent : baseEnd_3111071 < baseStart_3111071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111095 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 1, 2, 2]
def baseStart_3111095 : Nat := 118140960795 + 3111095 * 2 ^ 59
def prefixEnd_3111095 : Nat := 4983230072969 + 3 ^ 40 * 3111095 * 2
def baseEnd_3111095 : Nat := 1597487096799610560204841

theorem tailTrace_3111095 : CollatzResearch.WordTrace tailWord_3111095 prefixEnd_3111095 1597487096799610560204841 := by
  unfold tailWord_3111095
  simp only [CollatzResearch.WordTrace]
  refine ⟨113470956664041622569550739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75647304442694415046367159 113470956664041622569550739)
  ·
    refine ⟨170206434996062433854326109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113470956664041622569550739 170206434996062433854326109)
    ·
      refine ⟨63827413123523412695372291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170206434996062433854326109 63827413123523412695372291)
      ·
        refine ⟨95741119685285119043058437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63827413123523412695372291 95741119685285119043058437)
        ·
          refine ⟨17951459940990959820573457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95741119685285119043058437 17951459940990959820573457)
          ·
            refine ⟨13463594955743219865430093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17951459940990959820573457 13463594955743219865430093)
            ·
              refine ⟨5048848108403707449536285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13463594955743219865430093 5048848108403707449536285)
              ·
                refine ⟨1893318040651390293576107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5048848108403707449536285 1893318040651390293576107)
                ·
                  refine ⟨2839977060977085440364161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893318040651390293576107 2839977060977085440364161)
                  ·
                    refine ⟨2129982795732814080273121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2839977060977085440364161 2129982795732814080273121)
                    ·
                      refine ⟨1597487096799610560204841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2129982795732814080273121 1597487096799610560204841)
                      ·
                        rfl

theorem cell23_3111095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_3111095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111095 prefixEnd_3111095 := by exact prefixLift 3111095
  have htrace : WordTrace (prefixWord ++ tailWord_3111095) baseStart_3111095 baseEnd_3111095 := by
    simpa [prefixWord, tailWord_3111095, baseEnd_3111095] using wordTrace_append hprefix tailTrace_3111095
  have hstable : (prefixWord ++ tailWord_3111095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111095).length < 2 ^ (prefixWord ++ tailWord_3111095).sum := by decide
  have hdescent : baseEnd_3111095 < baseStart_3111095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111127 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 8]
def baseStart_3111127 : Nat := 118140960795 + 3111127 * 2 ^ 59
def prefixEnd_3111127 : Nat := 4983230072969 + 3 ^ 40 * 3111127 * 2
def baseEnd_3111127 : Nat := 532501176060184811668231

theorem tailTrace_3111127 : CollatzResearch.WordTrace tailWord_3111127 prefixEnd_3111127 532501176060184811668231 := by
  unfold tailWord_3111127
  simp only [CollatzResearch.WordTrace]
  refine ⟨113472123799925692034715635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75648082533283794689810423 113472123799925692034715635)
  ·
    refine ⟨170208185699888538052073453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113472123799925692034715635 170208185699888538052073453)
    ·
      refine ⟨63828069637458201769527545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170208185699888538052073453 63828069637458201769527545)
      ·
        refine ⟨47871052228093651327145659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63828069637458201769527545 47871052228093651327145659)
        ·
          refine ⟨71806578342140476990718489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47871052228093651327145659 71806578342140476990718489)
          ·
            refine ⟨53854933756605357743038867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71806578342140476990718489 53854933756605357743038867)
            ·
              refine ⟨80782400634908036614558301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53854933756605357743038867 80782400634908036614558301)
              ·
                refine ⟨30293400238090513730459363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80782400634908036614558301 30293400238090513730459363)
                ·
                  refine ⟨45440100357135770595689045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30293400238090513730459363 45440100357135770595689045)
                  ·
                    refine ⟨532501176060184811668231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45440100357135770595689045 532501176060184811668231)
                    ·
                      rfl

theorem cell23_3111127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_3111127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111127 prefixEnd_3111127 := by exact prefixLift 3111127
  have htrace : WordTrace (prefixWord ++ tailWord_3111127) baseStart_3111127 baseEnd_3111127 := by
    simpa [prefixWord, tailWord_3111127, baseEnd_3111127] using wordTrace_append hprefix tailTrace_3111127
  have hstable : (prefixWord ++ tailWord_3111127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111127).length < 2 ^ (prefixWord ++ tailWord_3111127).sum := by decide
  have hdescent : baseEnd_3111127 < baseStart_3111127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111128 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3111128 : Nat := 118140960795 + 3111128 * 2 ^ 59
def prefixEnd_3111128 : Nat := 4983230072969 + 3 ^ 40 * 3111128 * 2
def baseEnd_3111128 : Nat := 1597504041661208931092189

theorem tailTrace_3111128 : CollatzResearch.WordTrace tailWord_3111128 prefixEnd_3111128 1597504041661208931092189 := by
  unfold tailWord_3111128
  simp only [CollatzResearch.WordTrace]
  refine ⟨56736080136461034602751019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75648106848614712803668025 56736080136461034602751019)
  ·
    refine ⟨85104120204691551904126529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56736080136461034602751019 85104120204691551904126529)
    ·
      refine ⟨63828090153518663928094897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85104120204691551904126529 63828090153518663928094897)
      ·
        refine ⟨47871067615138997946071173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63828090153518663928094897 47871067615138997946071173)
        ·
          refine ⟨8975825177838562114888345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47871067615138997946071173 8975825177838562114888345)
          ·
            refine ⟨6731868883378921586166259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8975825177838562114888345 6731868883378921586166259)
            ·
              refine ⟨10097803325068382379249389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731868883378921586166259 10097803325068382379249389)
              ·
                refine ⟨3786676246900643392218521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10097803325068382379249389 3786676246900643392218521)
                ·
                  refine ⟨2840007185175482544163891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786676246900643392218521 2840007185175482544163891)
                  ·
                    refine ⟨4260010777763223816245837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2840007185175482544163891 4260010777763223816245837)
                    ·
                      refine ⟨1597504041661208931092189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4260010777763223816245837 1597504041661208931092189)
                      ·
                        rfl

theorem cell23_3111128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3111128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111128 prefixEnd_3111128 := by exact prefixLift 3111128
  have htrace : WordTrace (prefixWord ++ tailWord_3111128) baseStart_3111128 baseEnd_3111128 := by
    simpa [prefixWord, tailWord_3111128, baseEnd_3111128] using wordTrace_append hprefix tailTrace_3111128
  have hstable : (prefixWord ++ tailWord_3111128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111128).length < 2 ^ (prefixWord ++ tailWord_3111128).sum := by decide
  have hdescent : baseEnd_3111128 < baseStart_3111128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111132 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3111132 : Nat := 118140960795 + 3111132 * 2 ^ 59
def prefixEnd_3111132 : Nat := 4983230072969 + 3 ^ 40 * 3111132 * 2
def baseEnd_3111132 : Nat := 1597506095583826915442171

theorem tailTrace_3111132 : CollatzResearch.WordTrace tailWord_3111132 prefixEnd_3111132 1597506095583826915442171 := by
  unfold tailWord_3111132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56736153082453788944323825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75648204109938385259098433 56736153082453788944323825)
  ·
    refine ⟨42552114811840341708242869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56736153082453788944323825 42552114811840341708242869)
    ·
      refine ⟨3989260763610032035147769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42552114811840341708242869 3989260763610032035147769)
      ·
        refine ⟨2991945572707524026360827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3989260763610032035147769 2991945572707524026360827)
        ·
          refine ⟨4487918359061286039541241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991945572707524026360827 4487918359061286039541241)
          ·
            refine ⟨3365938769295964529655931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487918359061286039541241 3365938769295964529655931)
            ·
              refine ⟨5048908153943946794483897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365938769295964529655931 5048908153943946794483897)
              ·
                refine ⟨3786681115457960095862923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048908153943946794483897 3786681115457960095862923)
                ·
                  refine ⟨5680021673186940143794385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786681115457960095862923 5680021673186940143794385)
                  ·
                    refine ⟨4260016254890205107845789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5680021673186940143794385 4260016254890205107845789)
                    ·
                      refine ⟨1597506095583826915442171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4260016254890205107845789 1597506095583826915442171)
                      ·
                        rfl

theorem cell23_3111132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3111132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111132 prefixEnd_3111132 := by exact prefixLift 3111132
  have htrace : WordTrace (prefixWord ++ tailWord_3111132) baseStart_3111132 baseEnd_3111132 := by
    simpa [prefixWord, tailWord_3111132, baseEnd_3111132] using wordTrace_append hprefix tailTrace_3111132
  have hstable : (prefixWord ++ tailWord_3111132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111132).length < 2 ^ (prefixWord ++ tailWord_3111132).sum := by decide
  have hdescent : baseEnd_3111132 < baseStart_3111132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111151 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 3, 4, 2]
def baseStart_3111151 : Nat := 118140960795 + 3111151 * 2 ^ 59
def prefixEnd_3111151 : Nat := 4983230072969 + 3 ^ 40 * 3111151 * 2
def baseEnd_3111151 : Nat := 1597515851716262341104583

theorem tailTrace_3111151 : CollatzResearch.WordTrace tailWord_3111151 prefixEnd_3111151 1597515851716262341104583 := by
  unfold tailWord_3111151
  simp only [CollatzResearch.WordTrace]
  refine ⟨113472999151838744133589307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75648666101225829422392871 113472999151838744133589307)
  ·
    refine ⟨170209498727758116200383961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113472999151838744133589307 170209498727758116200383961)
    ·
      refine ⟨127657124045818587150287971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170209498727758116200383961 127657124045818587150287971)
      ·
        refine ⟨191485686068727880725431957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127657124045818587150287971 191485686068727880725431957)
        ·
          refine ⟨8975891534471619409004623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191485686068727880725431957 8975891534471619409004623)
          ·
            refine ⟨13463837301707429113506935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8975891534471619409004623 13463837301707429113506935)
            ·
              refine ⟨20195755952561143670260403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13463837301707429113506935 20195755952561143670260403)
              ·
                refine ⟨30293633928841715505390605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20195755952561143670260403 30293633928841715505390605)
                ·
                  refine ⟨11360112723315643314521477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30293633928841715505390605 11360112723315643314521477)
                  ·
                    refine ⟨2130021135621683121472777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11360112723315643314521477 2130021135621683121472777)
                    ·
                      refine ⟨1597515851716262341104583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130021135621683121472777 1597515851716262341104583)
                      ·
                        rfl

theorem cell23_3111151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4, 2].length) (baseStart_3111151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111151 prefixEnd_3111151 := by exact prefixLift 3111151
  have htrace : WordTrace (prefixWord ++ tailWord_3111151) baseStart_3111151 baseEnd_3111151 := by
    simpa [prefixWord, tailWord_3111151, baseEnd_3111151] using wordTrace_append hprefix tailTrace_3111151
  have hstable : (prefixWord ++ tailWord_3111151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111151).length < 2 ^ (prefixWord ++ tailWord_3111151).sum := by decide
  have hdescent : baseEnd_3111151 < baseStart_3111151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111168 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2]
def baseStart_3111168 : Nat := 118140960795 + 3111168 * 2 ^ 59
def prefixEnd_3111168 : Nat := 4983230072969 + 3 ^ 40 * 3111168 * 2
def baseEnd_3111168 : Nat := 1597524580887388774592005

theorem tailTrace_3111168 : CollatzResearch.WordTrace tailWord_3111168 prefixEnd_3111168 1597524580887388774592005 := by
  unfold tailWord_3111168
  simp only [CollatzResearch.WordTrace]
  refine ⟨56736809596388578018479079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75649079461851437357972105 56736809596388578018479079)
  ·
    refine ⟨85105214394582867027718619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56736809596388578018479079 85105214394582867027718619)
    ·
      refine ⟨127657821591874300541577929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85105214394582867027718619 127657821591874300541577929)
      ·
        refine ⟨95743366193905725406183447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127657821591874300541577929 95743366193905725406183447)
        ·
          refine ⟨143615049290858588109275171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95743366193905725406183447 143615049290858588109275171)
          ·
            refine ⟨215422573936287882163912757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143615049290858588109275171 215422573936287882163912757)
            ·
              refine ⟨20195866306526988952866821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215422573936287882163912757 20195866306526988952866821)
              ·
                refine ⟨3786724932473810428662529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20195866306526988952866821 3786724932473810428662529)
                ·
                  refine ⟨2840043699355357821496897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786724932473810428662529 2840043699355357821496897)
                  ·
                    refine ⟨2130032774516518366122673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2840043699355357821496897 2130032774516518366122673)
                    ·
                      refine ⟨1597524580887388774592005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130032774516518366122673 1597524580887388774592005)
                      ·
                        rfl

theorem cell23_3111168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_3111168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111168 prefixEnd_3111168 := by exact prefixLift 3111168
  have htrace : WordTrace (prefixWord ++ tailWord_3111168) baseStart_3111168 baseEnd_3111168 := by
    simpa [prefixWord, tailWord_3111168, baseEnd_3111168] using wordTrace_append hprefix tailTrace_3111168
  have hstable : (prefixWord ++ tailWord_3111168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111168).length < 2 ^ (prefixWord ++ tailWord_3111168).sum := by decide
  have hdescent : baseEnd_3111168 < baseStart_3111168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111285 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3111285 : Nat := 118140960795 + 3111285 * 2 ^ 59
def prefixEnd_3111285 : Nat := 4983230072969 + 3 ^ 40 * 3111285 * 2
def baseEnd_3111285 : Nat := 532528219374654938942989

theorem tailTrace_3111285 : CollatzResearch.WordTrace tailWord_3111285 prefixEnd_3111285 532528219374654938942989 := by
  unfold tailWord_3111285
  simp only [CollatzResearch.WordTrace]
  refine ⟨113477886533353285018967309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75651924355568856679311539 113477886533353285018967309)
  ·
    refine ⟨42554207450007481882112741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113477886533353285018967309 42554207450007481882112741)
    ·
      refine ⟨7978913896876402852896139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42554207450007481882112741 7978913896876402852896139)
      ·
        refine ⟨11968370845314604279344209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7978913896876402852896139 11968370845314604279344209)
        ·
          refine ⟨8976278133985953209508157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11968370845314604279344209 8976278133985953209508157)
          ·
            refine ⟨3366104300244732453565559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8976278133985953209508157 3366104300244732453565559)
            ·
              refine ⟨5049156450367098680348339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366104300244732453565559 5049156450367098680348339)
              ·
                refine ⟨7573734675550648020522509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049156450367098680348339 7573734675550648020522509)
                ·
                  refine ⟨2840150503331493007695941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7573734675550648020522509 2840150503331493007695941)
                  ·
                    refine ⟨532528219374654938942989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840150503331493007695941 532528219374654938942989)
                    ·
                      rfl

theorem cell23_3111285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3111285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111285 prefixEnd_3111285 := by exact prefixLift 3111285
  have htrace : WordTrace (prefixWord ++ tailWord_3111285) baseStart_3111285 baseEnd_3111285 := by
    simpa [prefixWord, tailWord_3111285, baseEnd_3111285] using wordTrace_append hprefix tailTrace_3111285
  have hstable : (prefixWord ++ tailWord_3111285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111285).length < 2 ^ (prefixWord ++ tailWord_3111285).sum := by decide
  have hdescent : baseEnd_3111285 < baseStart_3111285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111335 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_3111335 : Nat := 118140960795 + 3111335 * 2 ^ 59
def prefixEnd_3111335 : Nat := 4983230072969 + 3 ^ 40 * 3111335 * 2
def baseEnd_3111335 : Nat := 1597610332156689621203737

theorem tailTrace_3111335 : CollatzResearch.WordTrace tailWord_3111335 prefixEnd_3111335 1597610332156689621203737 := by
  unfold tailWord_3111335
  simp only [CollatzResearch.WordTrace]
  refine ⟨113479710183172143558287459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75653140122114762372191639 113479710183172143558287459)
  ·
    refine ⟨170219565274758215337431189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113479710183172143558287459 170219565274758215337431189)
    ·
      refine ⟨7979042122254291343942087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170219565274758215337431189 7979042122254291343942087)
      ·
        refine ⟨11968563183381437015913131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979042122254291343942087 11968563183381437015913131)
        ·
          refine ⟨17952844775072155523869697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11968563183381437015913131 17952844775072155523869697)
          ·
            refine ⟨13464633581304116642902273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17952844775072155523869697 13464633581304116642902273)
            ·
              refine ⟨10098475185978087482176705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13464633581304116642902273 10098475185978087482176705)
              ·
                refine ⟨7573856389483565611632529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10098475185978087482176705 7573856389483565611632529)
                ·
                  refine ⟨5680392292112674208724397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7573856389483565611632529 5680392292112674208724397)
                  ·
                    refine ⟨2130147109542252828271649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5680392292112674208724397 2130147109542252828271649)
                    ·
                      refine ⟨1597610332156689621203737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130147109542252828271649 1597610332156689621203737)
                      ·
                        rfl

theorem cell23_3111335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_3111335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111335 prefixEnd_3111335 := by exact prefixLift 3111335
  have htrace : WordTrace (prefixWord ++ tailWord_3111335) baseStart_3111335 baseEnd_3111335 := by
    simpa [prefixWord, tailWord_3111335, baseEnd_3111335] using wordTrace_append hprefix tailTrace_3111335
  have hstable : (prefixWord ++ tailWord_3111335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111335).length < 2 ^ (prefixWord ++ tailWord_3111335).sum := by decide
  have hdescent : baseEnd_3111335 < baseStart_3111335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111368 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3111368 : Nat := 118140960795 + 3111368 * 2 ^ 59
def prefixEnd_3111368 : Nat := 4983230072969 + 3 ^ 40 * 3111368 * 2
def baseEnd_3111368 : Nat := 1597627277018287992091085

theorem tailTrace_3111368 : CollatzResearch.WordTrace tailWord_3111368 prefixEnd_3111368 1597627277018287992091085 := by
  unfold tailWord_3111368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56740456896026295097119379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75653942528035060129492505 56740456896026295097119379)
  ·
    refine ⟨85110685344039442645679069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56740456896026295097119379 85110685344039442645679069)
    ·
      refine ⟨31916507004014790992129651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85110685344039442645679069 31916507004014790992129651)
      ·
        refine ⟨47874760506022186488194477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31916507004014790992129651 47874760506022186488194477)
        ·
          refine ⟨17953035189758319933072929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47874760506022186488194477 17953035189758319933072929)
          ·
            refine ⟨13464776392318739949804697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17953035189758319933072929 13464776392318739949804697)
            ·
              refine ⟨10098582294239054962353523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13464776392318739949804697 10098582294239054962353523)
              ·
                refine ⟨15147873441358582443530285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098582294239054962353523 15147873441358582443530285)
                ·
                  refine ⟨5680452540509468416323857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15147873441358582443530285 5680452540509468416323857)
                  ·
                    refine ⟨4260339405382101312242893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5680452540509468416323857 4260339405382101312242893)
                    ·
                      refine ⟨1597627277018287992091085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4260339405382101312242893 1597627277018287992091085)
                      ·
                        rfl

theorem cell23_3111368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3111368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111368 prefixEnd_3111368 := by exact prefixLift 3111368
  have htrace : WordTrace (prefixWord ++ tailWord_3111368) baseStart_3111368 baseEnd_3111368 := by
    simpa [prefixWord, tailWord_3111368, baseEnd_3111368] using wordTrace_append hprefix tailTrace_3111368
  have hstable : (prefixWord ++ tailWord_3111368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111368).length < 2 ^ (prefixWord ++ tailWord_3111368).sum := by decide
  have hdescent : baseEnd_3111368 < baseStart_3111368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111382 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3111382 : Nat := 118140960795 + 3111382 * 2 ^ 59
def prefixEnd_3111382 : Nat := 4983230072969 + 3 ^ 40 * 3111382 * 2
def baseEnd_3111382 : Nat := 1597634465747450937316021

theorem tailTrace_3111382 : CollatzResearch.WordTrace tailWord_3111382 prefixEnd_3111382 1597634465747450937316021 := by
  unfold tailWord_3111382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092589025875116911578025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75654282942667913723498933 7092589025875116911578025)
  ·
    refine ⟨5319441769406337683683519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7092589025875116911578025 5319441769406337683683519)
    ·
      refine ⟨7979162654109506525525279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319441769406337683683519 7979162654109506525525279)
      ·
        refine ⟨11968743981164259788287919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979162654109506525525279 11968743981164259788287919)
        ·
          refine ⟨17953115971746389682431879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11968743981164259788287919 17953115971746389682431879)
          ·
            refine ⟨26929673957619584523647819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17953115971746389682431879 26929673957619584523647819)
            ·
              refine ⟨40394510936429376785471729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26929673957619584523647819 40394510936429376785471729)
              ·
                refine ⟨30295883202322032589103797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40394510936429376785471729 30295883202322032589103797)
                ·
                  refine ⟨2840239050217690555228481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30295883202322032589103797 2840239050217690555228481)
                  ·
                    refine ⟨2130179287663267916421361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2840239050217690555228481 2130179287663267916421361)
                    ·
                      refine ⟨1597634465747450937316021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130179287663267916421361 1597634465747450937316021)
                      ·
                        rfl

theorem cell23_3111382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3111382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111382 prefixEnd_3111382 := by exact prefixLift 3111382
  have htrace : WordTrace (prefixWord ++ tailWord_3111382) baseStart_3111382 baseEnd_3111382 := by
    simpa [prefixWord, tailWord_3111382, baseEnd_3111382] using wordTrace_append hprefix tailTrace_3111382
  have hstable : (prefixWord ++ tailWord_3111382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111382).length < 2 ^ (prefixWord ++ tailWord_3111382).sum := by decide
  have hdescent : baseEnd_3111382 < baseStart_3111382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111428 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3111428 : Nat := 118140960795 + 3111428 * 2 ^ 59
def prefixEnd_3111428 : Nat := 4983230072969 + 3 ^ 40 * 3111428 * 2
def baseEnd_3111428 : Nat := 1597658085857557757340809

theorem tailTrace_3111428 : CollatzResearch.WordTrace tailWord_3111428 prefixEnd_3111428 1597658085857557757340809 := by
  unfold tailWord_3111428
  simp only [CollatzResearch.WordTrace]
  refine ⟨56741551085917610220711469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75655401447890146960948625 56741551085917610220711469)
  ·
    refine ⟨21278081657219103832766801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56741551085917610220711469 21278081657219103832766801)
    ·
      refine ⟨15958561242914327874575101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21278081657219103832766801 15958561242914327874575101)
      ·
        refine ⟨5984460466092872952965663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15958561242914327874575101 5984460466092872952965663)
        ·
          refine ⟨8976690699139309429448495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984460466092872952965663 8976690699139309429448495)
          ·
            refine ⟨13465036048708964144172743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8976690699139309429448495 13465036048708964144172743)
            ·
              refine ⟨20197554073063446216259115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13465036048708964144172743 20197554073063446216259115)
              ·
                refine ⟨30296331109595169324388673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20197554073063446216259115 30296331109595169324388673)
                ·
                  refine ⟨22722248332196376993291505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30296331109595169324388673 22722248332196376993291505)
                  ·
                    refine ⟨17041686249147282744968629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22722248332196376993291505 17041686249147282744968629)
                    ·
                      refine ⟨1597658085857557757340809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17041686249147282744968629 1597658085857557757340809)
                      ·
                        rfl

theorem cell23_3111428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3111428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111428 prefixEnd_3111428 := by exact prefixLift 3111428
  have htrace : WordTrace (prefixWord ++ tailWord_3111428) baseStart_3111428 baseEnd_3111428 := by
    simpa [prefixWord, tailWord_3111428, baseEnd_3111428] using wordTrace_append hprefix tailTrace_3111428
  have hstable : (prefixWord ++ tailWord_3111428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111428).length < 2 ^ (prefixWord ++ tailWord_3111428).sum := by decide
  have hdescent : baseEnd_3111428 < baseStart_3111428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111458 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3111458 : Nat := 118140960795 + 3111458 * 2 ^ 59
def prefixEnd_3111458 : Nat := 4983230072969 + 3 ^ 40 * 3111458 * 2
def baseEnd_3111458 : Nat := 1597673490277192639965671

theorem tailTrace_3111458 : CollatzResearch.WordTrace tailWord_3111458 prefixEnd_3111458 1597673490277192639965671 := by
  unfold tailWord_3111458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28371049090431633891253757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75656130907817690376676685 28371049090431633891253757)
  ·
    refine ⟨10639143408911862709220159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28371049090431633891253757 10639143408911862709220159)
    ·
      refine ⟨15958715113367794063830239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10639143408911862709220159 15958715113367794063830239)
      ·
        refine ⟨23938072670051691095745359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15958715113367794063830239 23938072670051691095745359)
        ·
          refine ⟨35907109005077536643618039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23938072670051691095745359 35907109005077536643618039)
          ·
            refine ⟨53860663507616304965427059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35907109005077536643618039 53860663507616304965427059)
            ·
              refine ⟨80790995261424457448140589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53860663507616304965427059 80790995261424457448140589)
              ·
                refine ⟨30296623223034171543052721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80790995261424457448140589 30296623223034171543052721)
                ·
                  refine ⟨22722467417275628657289541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30296623223034171543052721 22722467417275628657289541)
                  ·
                    refine ⟨4260462640739180373241789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22722467417275628657289541 4260462640739180373241789)
                    ·
                      refine ⟨1597673490277192639965671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4260462640739180373241789 1597673490277192639965671)
                      ·
                        rfl

theorem cell23_3111458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3111458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111458 prefixEnd_3111458 := by exact prefixLift 3111458
  have htrace : WordTrace (prefixWord ++ tailWord_3111458) baseStart_3111458 baseEnd_3111458 := by
    simpa [prefixWord, tailWord_3111458, baseEnd_3111458] using wordTrace_append hprefix tailTrace_3111458
  have hstable : (prefixWord ++ tailWord_3111458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111458).length < 2 ^ (prefixWord ++ tailWord_3111458).sum := by decide
  have hdescent : baseEnd_3111458 < baseStart_3111458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111491 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 7]
def baseStart_3111491 : Nat := 118140960795 + 3111491 * 2 ^ 59
def prefixEnd_3111491 : Nat := 4983230072969 + 3 ^ 40 * 3111491 * 2
def baseEnd_3111491 : Nat := 532563478379597003617673

theorem tailTrace_3111491 : CollatzResearch.WordTrace tailWord_3111491 prefixEnd_3111491 532563478379597003617673 := by
  unfold tailWord_3111491
  simp only [CollatzResearch.WordTrace]
  refine ⟨113485399970606982200966327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75656933313737988133977551 113485399970606982200966327)
  ·
    refine ⟨170228099955910473301449491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113485399970606982200966327 170228099955910473301449491)
    ·
      refine ⟨255342149933865709952174237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170228099955910473301449491 255342149933865709952174237)
      ·
        refine ⟨95753306225199641232065339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255342149933865709952174237 95753306225199641232065339)
        ·
          refine ⟨143629959337799461848098009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95753306225199641232065339 143629959337799461848098009)
          ·
            refine ⟨107722469503349596386073507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143629959337799461848098009 107722469503349596386073507)
            ·
              refine ⟨161583704255024394579110261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107722469503349596386073507 161583704255024394579110261)
              ·
                refine ⟨15148472273908536991791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161583704255024394579110261 15148472273908536991791587)
                ·
                  refine ⟨22722708410862805487687381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15148472273908536991791587 22722708410862805487687381)
                  ·
                    refine ⟨532563478379597003617673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22722708410862805487687381 532563478379597003617673)
                    ·
                      rfl

theorem cell23_3111491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_3111491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111491 prefixEnd_3111491 := by exact prefixLift 3111491
  have htrace : WordTrace (prefixWord ++ tailWord_3111491) baseStart_3111491 baseEnd_3111491 := by
    simpa [prefixWord, tailWord_3111491, baseEnd_3111491] using wordTrace_append hprefix tailTrace_3111491
  have hstable : (prefixWord ++ tailWord_3111491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111491).length < 2 ^ (prefixWord ++ tailWord_3111491).sum := by decide
  have hdescent : baseEnd_3111491 < baseStart_3111491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111545 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3111545 : Nat := 118140960795 + 3111545 * 2 ^ 59
def prefixEnd_3111545 : Nat := 4983230072969 + 3 ^ 40 * 3111545 * 2
def baseEnd_3111545 : Nat := 1597718163094133799577771

theorem tailTrace_3111545 : CollatzResearch.WordTrace tailWord_3111545 prefixEnd_3111545 1597718163094133799577771 := by
  unfold tailWord_3111545
  simp only [CollatzResearch.WordTrace]
  refine ⟨113487369512411349423432089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75658246341607566282288059 113487369512411349423432089)
  ·
    refine ⟨85115527134308512067574067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113487369512411349423432089 85115527134308512067574067)
    ·
      refine ⟨127673290701462768101361101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85115527134308512067574067 127673290701462768101361101)
      ·
        refine ⟨47877484013048538038010413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127673290701462768101361101 47877484013048538038010413)
        ·
          refine ⟨17954056504893201764253905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47877484013048538038010413 17954056504893201764253905)
          ·
            refine ⟨13465542378669901323190429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17954056504893201764253905 13465542378669901323190429)
            ·
              refine ⟨5049578392001212996196411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13465542378669901323190429 5049578392001212996196411)
              ·
                refine ⟨7574367588001819494294617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049578392001212996196411 7574367588001819494294617)
                ·
                  refine ⟨5680775691001364620720963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7574367588001819494294617 5680775691001364620720963)
                  ·
                    refine ⟨8521163536502046931081445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5680775691001364620720963 8521163536502046931081445)
                    ·
                      refine ⟨1597718163094133799577771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8521163536502046931081445 1597718163094133799577771)
                      ·
                        rfl

theorem cell23_3111545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3111545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111545 prefixEnd_3111545 := by exact prefixLift 3111545
  have htrace : WordTrace (prefixWord ++ tailWord_3111545) baseStart_3111545 baseEnd_3111545 := by
    simpa [prefixWord, tailWord_3111545, baseEnd_3111545] using wordTrace_append hprefix tailTrace_3111545
  have hstable : (prefixWord ++ tailWord_3111545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111545).length < 2 ^ (prefixWord ++ tailWord_3111545).sum := by decide
  have hdescent : baseEnd_3111545 < baseStart_3111545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111572 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3111572 : Nat := 118140960795 + 3111572 * 2 ^ 59
def prefixEnd_3111572 : Nat := 4983230072969 + 3 ^ 40 * 3111572 * 2
def baseEnd_3111572 : Nat := 532577342357268397980049

theorem tailTrace_3111572 : CollatzResearch.WordTrace tailWord_3111572 prefixEnd_3111572 532577342357268397980049 := by
  unfold tailWord_3111572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56744177141656766517332485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75658902855542355356443313 56744177141656766517332485)
  ·
    refine ⟨10639533214060643721999841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56744177141656766517332485 10639533214060643721999841)
    ·
      refine ⟨7979649910545482791499881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10639533214060643721999841 7979649910545482791499881)
      ·
        refine ⟨5984737432909112093624911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7979649910545482791499881 5984737432909112093624911)
        ·
          refine ⟨8977106149363668140437367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984737432909112093624911 8977106149363668140437367)
          ·
            refine ⟨13465659224045502210656051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977106149363668140437367 13465659224045502210656051)
            ·
              refine ⟨20198488836068253315984077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13465659224045502210656051 20198488836068253315984077)
              ·
                refine ⟨7574433313525594993494029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20198488836068253315984077 7574433313525594993494029)
                ·
                  refine ⟨2840412492572098122560261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7574433313525594993494029 2840412492572098122560261)
                  ·
                    refine ⟨532577342357268397980049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840412492572098122560261 532577342357268397980049)
                    ·
                      rfl

theorem cell23_3111572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3111572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111572 prefixEnd_3111572 := by exact prefixLift 3111572
  have htrace : WordTrace (prefixWord ++ tailWord_3111572) baseStart_3111572 baseEnd_3111572 := by
    simpa [prefixWord, tailWord_3111572, baseEnd_3111572] using wordTrace_append hprefix tailTrace_3111572
  have hstable : (prefixWord ++ tailWord_3111572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111572).length < 2 ^ (prefixWord ++ tailWord_3111572).sum := by decide
  have hdescent : baseEnd_3111572 < baseStart_3111572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111588 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3111588 : Nat := 118140960795 + 3111588 * 2 ^ 59
def prefixEnd_3111588 : Nat := 4983230072969 + 3 ^ 40 * 3111588 * 2
def baseEnd_3111588 : Nat := 1597740242762277131340073

theorem tailTrace_3111588 : CollatzResearch.WordTrace tailWord_3111588 prefixEnd_3111588 1597740242762277131340073 := by
  unfold tailWord_3111588
  simp only [CollatzResearch.WordTrace]
  refine ⟨56744468925627783883623709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75659291900837045178164945 56744468925627783883623709)
  ·
    refine ⟨21279175847110418956358891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56744468925627783883623709 21279175847110418956358891)
    ·
      refine ⟨31918763770665628434538337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21279175847110418956358891 31918763770665628434538337)
      ·
        refine ⟨23939072827999221325903753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31918763770665628434538337 23939072827999221325903753)
        ·
          refine ⟨17954304620999415994427815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23939072827999221325903753 17954304620999415994427815)
          ·
            refine ⟨26931456931499123991641723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17954304620999415994427815 26931456931499123991641723)
            ·
              refine ⟨40397185397248685987462585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26931456931499123991641723 40397185397248685987462585)
              ·
                refine ⟨30297889047936514490596939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40397185397248685987462585 30297889047936514490596939)
                ·
                  refine ⟨45446833571904771735895409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30297889047936514490596939 45446833571904771735895409)
                  ·
                    refine ⟨34085125178928578801921557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45446833571904771735895409 34085125178928578801921557)
                    ·
                      refine ⟨1597740242762277131340073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34085125178928578801921557 1597740242762277131340073)
                      ·
                        rfl

theorem cell23_3111588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3111588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111588 prefixEnd_3111588 := by exact prefixLift 3111588
  have htrace : WordTrace (prefixWord ++ tailWord_3111588) baseStart_3111588 baseEnd_3111588 := by
    simpa [prefixWord, tailWord_3111588, baseEnd_3111588] using wordTrace_append hprefix tailTrace_3111588
  have hstable : (prefixWord ++ tailWord_3111588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111588).length < 2 ^ (prefixWord ++ tailWord_3111588).sum := by decide
  have hdescent : baseEnd_3111588 < baseStart_3111588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111615 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 1, 5]
def baseStart_3111615 : Nat := 118140960795 + 3111615 * 2 ^ 59
def prefixEnd_3111615 : Nat := 4983230072969 + 3 ^ 40 * 3111615 * 2
def baseEnd_3111615 : Nat := 532584702246649508567483

theorem tailTrace_3111615 : CollatzResearch.WordTrace tailWord_3111615 prefixEnd_3111615 532584702246649508567483 := by
  unfold tailWord_3111615
  simp only [CollatzResearch.WordTrace]
  refine ⟨113489922622157751378480299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75659948414771834252320199 113489922622157751378480299)
  ·
    refine ⟨170234883933236627067720449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113489922622157751378480299 170234883933236627067720449)
    ·
      refine ⟨127676162949927470300790337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170234883933236627067720449 127676162949927470300790337)
      ·
        refine ⟨95757122212445602725592753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127676162949927470300790337 95757122212445602725592753)
        ·
          refine ⟨71817841659334202044194565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95757122212445602725592753 71817841659334202044194565)
          ·
            refine ⟨13465845311125162883286481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71817841659334202044194565 13465845311125162883286481)
            ·
              refine ⟨10099383983343872162464861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13465845311125162883286481 10099383983343872162464861)
              ·
                refine ⟨3787268993753952060924323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10099383983343872162464861 3787268993753952060924323)
                ·
                  refine ⟨5680903490630928091386485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787268993753952060924323 5680903490630928091386485)
                  ·
                    refine ⟨532584702246649508567483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5680903490630928091386485 532584702246649508567483)
                    ·
                      rfl

theorem cell23_3111615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_3111615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111615 prefixEnd_3111615 := by exact prefixLift 3111615
  have htrace : WordTrace (prefixWord ++ tailWord_3111615) baseStart_3111615 baseEnd_3111615 := by
    simpa [prefixWord, tailWord_3111615, baseEnd_3111615] using wordTrace_append hprefix tailTrace_3111615
  have hstable : (prefixWord ++ tailWord_3111615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111615).length < 2 ^ (prefixWord ++ tailWord_3111615).sum := by decide
  have hdescent : baseEnd_3111615 < baseStart_3111615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111636 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3111636 : Nat := 118140960795 + 3111636 * 2 ^ 59
def prefixEnd_3111636 : Nat := 4983230072969 + 3 ^ 40 * 3111636 * 2
def baseEnd_3111636 : Nat := 177529432203743660393317

theorem tailTrace_3111636 : CollatzResearch.WordTrace tailWord_3111636 prefixEnd_3111636 177529432203743660393317 := by
  unfold tailWord_3111636
  simp only [CollatzResearch.WordTrace]
  refine ⟨56745344277540835982497381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75660459036721114643329841 56745344277540835982497381)
  ·
    refine ⟨10639752052038906746718259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56745344277540835982497381 10639752052038906746718259)
    ·
      refine ⟨15959628078058360120077389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10639752052038906746718259 15959628078058360120077389)
      ·
        refine ⟨5984860529271885045029021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15959628078058360120077389 5984860529271885045029021)
        ·
          refine ⟨2244322698476956891885883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5984860529271885045029021 2244322698476956891885883)
          ·
            refine ⟨3366484047715435337828825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244322698476956891885883 3366484047715435337828825)
            ·
              refine ⟨2524863035786576503371619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366484047715435337828825 2524863035786576503371619)
              ·
                refine ⟨3787294553679864755057429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524863035786576503371619 3787294553679864755057429)
                ·
                  refine ⟨177529432203743660393317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3787294553679864755057429 177529432203743660393317)
                  ·
                    rfl

theorem cell23_3111636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3111636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111636 prefixEnd_3111636 := by exact prefixLift 3111636
  have htrace : WordTrace (prefixWord ++ tailWord_3111636) baseStart_3111636 baseEnd_3111636 := by
    simpa [prefixWord, tailWord_3111636, baseEnd_3111636] using wordTrace_append hprefix tailTrace_3111636
  have hstable : (prefixWord ++ tailWord_3111636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111636).length < 2 ^ (prefixWord ++ tailWord_3111636).sum := by decide
  have hdescent : baseEnd_3111636 < baseStart_3111636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111652 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_3111652 : Nat := 118140960795 + 3111652 * 2 ^ 59
def prefixEnd_3111652 : Nat := 4983230072969 + 3 ^ 40 * 3111652 * 2
def baseEnd_3111652 : Nat := 1597773105524164880939779

theorem tailTrace_3111652 : CollatzResearch.WordTrace tailWord_3111652 prefixEnd_3111652 1597773105524164880939779 := by
  unfold tailWord_3111652
  simp only [CollatzResearch.WordTrace]
  refine ⟨56745636061511853348788605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75660848082015804465051473 56745636061511853348788605)
  ·
    refine ⟨21279613523066945005795727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56745636061511853348788605 21279613523066945005795727)
    ·
      refine ⟨31919420284600417508693591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21279613523066945005795727 31919420284600417508693591)
      ·
        refine ⟨47879130426900626263040387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31919420284600417508693591 47879130426900626263040387)
        ·
          refine ⟨71818695640350939394560581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47879130426900626263040387 71818695640350939394560581)
          ·
            refine ⟨13466005432565801136480109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71818695640350939394560581 13466005432565801136480109)
            ·
              refine ⟨5049752037212175426180041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13466005432565801136480109 5049752037212175426180041)
              ·
                refine ⟨3787314027909131569635031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049752037212175426180041 3787314027909131569635031)
                ·
                  refine ⟨5680971041863697354452547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787314027909131569635031 5680971041863697354452547)
                  ·
                    refine ⟨8521456562795546031678821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5680971041863697354452547 8521456562795546031678821)
                    ·
                      refine ⟨1597773105524164880939779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8521456562795546031678821 1597773105524164880939779)
                      ·
                        rfl

theorem cell23_3111652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_3111652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111652 prefixEnd_3111652 := by exact prefixLift 3111652
  have htrace : WordTrace (prefixWord ++ tailWord_3111652) baseStart_3111652 baseEnd_3111652 := by
    simpa [prefixWord, tailWord_3111652, baseEnd_3111652] using wordTrace_append hprefix tailTrace_3111652
  have hstable : (prefixWord ++ tailWord_3111652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111652).length < 2 ^ (prefixWord ++ tailWord_3111652).sum := by decide
  have hdescent : baseEnd_3111652 < baseStart_3111652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111665 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_3111665 : Nat := 118140960795 + 3111665 * 2 ^ 59
def prefixEnd_3111665 : Nat := 4983230072969 + 3 ^ 40 * 3111665 * 2
def baseEnd_3111665 : Nat := 1597779780772673330077219

theorem tailTrace_3111665 : CollatzResearch.WordTrace tailWord_3111665 prefixEnd_3111665 1597779780772673330077219 := by
  unfold tailWord_3111665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113491746271976609917800449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75661164181317739945200299 113491746271976609917800449)
  ·
    refine ⟨85118809703982457438350337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113491746271976609917800449 85118809703982457438350337)
    ·
      refine ⟨63839107277986843078762753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85118809703982457438350337 63839107277986843078762753)
      ·
        refine ⟨47879330458490132309072065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63839107277986843078762753 47879330458490132309072065)
        ·
          refine ⟨35909497843867599231804049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47879330458490132309072065 35909497843867599231804049)
          ·
            refine ⟨26932123382900699423853037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35909497843867599231804049 26932123382900699423853037)
            ·
              refine ⟨10099546268587762283944889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26932123382900699423853037 10099546268587762283944889)
              ·
                refine ⟨7574659701440821712958667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10099546268587762283944889 7574659701440821712958667)
                ·
                  refine ⟨11361989552161232569438001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7574659701440821712958667 11361989552161232569438001)
                  ·
                    refine ⟨8521492164120924427078501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11361989552161232569438001 8521492164120924427078501)
                    ·
                      refine ⟨1597779780772673330077219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8521492164120924427078501 1597779780772673330077219)
                      ·
                        rfl

theorem cell23_3111665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_3111665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111665 prefixEnd_3111665 := by exact prefixLift 3111665
  have htrace : WordTrace (prefixWord ++ tailWord_3111665) baseStart_3111665 baseEnd_3111665 := by
    simpa [prefixWord, tailWord_3111665, baseEnd_3111665] using wordTrace_append hprefix tailTrace_3111665
  have hstable : (prefixWord ++ tailWord_3111665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111665).length < 2 ^ (prefixWord ++ tailWord_3111665).sum := by decide
  have hdescent : baseEnd_3111665 < baseStart_3111665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111709 : List Nat := [1, 4, 2, 4, 1, 1, 3, 7]
def baseStart_3111709 : Nat := 118140960795 + 3111709 * 2 ^ 59
def prefixEnd_3111709 : Nat := 4983230072969 + 3 ^ 40 * 3111709 * 2
def baseEnd_3111709 : Nat := 59177865700795228071371

theorem tailTrace_3111709 : CollatzResearch.WordTrace tailWord_3111709 prefixEnd_3111709 59177865700795228071371 := by
  unfold tailWord_3111709
  simp only [CollatzResearch.WordTrace]
  refine ⟨113493351083817205432402181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75662234055878136954934787 113493351083817205432402181)
  ·
    refine ⟨21280003328215726018575409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113493351083817205432402181 21280003328215726018575409)
    ·
      refine ⟨15960002496161794513931557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21280003328215726018575409 15960002496161794513931557)
      ·
        refine ⟨2992500468030336471362167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15960002496161794513931557 2992500468030336471362167)
        ·
          refine ⟨4488750702045504707043251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992500468030336471362167 4488750702045504707043251)
          ·
            refine ⟨6733126053068257060564877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488750702045504707043251 6733126053068257060564877)
            ·
              refine ⟨2524922269900596397711829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6733126053068257060564877 2524922269900596397711829)
              ·
                refine ⟨59177865700795228071371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2524922269900596397711829 59177865700795228071371)
                ·
                  rfl

theorem cell23_3111709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 7].length) (baseStart_3111709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111709 prefixEnd_3111709 := by exact prefixLift 3111709
  have htrace : WordTrace (prefixWord ++ tailWord_3111709) baseStart_3111709 baseEnd_3111709 := by
    simpa [prefixWord, tailWord_3111709, baseEnd_3111709] using wordTrace_append hprefix tailTrace_3111709
  have hstable : (prefixWord ++ tailWord_3111709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111709).length < 2 ^ (prefixWord ++ tailWord_3111709).sum := by decide
  have hdescent : baseEnd_3111709 < baseStart_3111709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111729 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_3111729 : Nat := 118140960795 + 3111729 * 2 ^ 59
def prefixEnd_3111729 : Nat := 4983230072969 + 3 ^ 40 * 3111729 * 2
def baseEnd_3111729 : Nat := 1597812643534561079676925

theorem tailTrace_3111729 : CollatzResearch.WordTrace tailWord_3111729 prefixEnd_3111729 1597812643534561079676925 := by
  unfold tailWord_3111729
  simp only [CollatzResearch.WordTrace]
  refine ⟨113494080543744748848130241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75662720362496499232086827 113494080543744748848130241)
  ·
    refine ⟨85120560407808561636097681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113494080543744748848130241 85120560407808561636097681)
    ·
      refine ⟨63840420305856421227073261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85120560407808561636097681 63840420305856421227073261)
      ·
        refine ⟨23940157614696157960152473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63840420305856421227073261 23940157614696157960152473)
        ·
          refine ⟨17955118211022118470114355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23940157614696157960152473 17955118211022118470114355)
          ·
            refine ⟨26932677316533177705171533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17955118211022118470114355 26932677316533177705171533)
            ·
              refine ⟨10099753993699941639439325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26932677316533177705171533 10099753993699941639439325)
              ·
                refine ⟨3787407747637478114789747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10099753993699941639439325 3787407747637478114789747)
                ·
                  refine ⟨5681111621456217172184621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787407747637478114789747 5681111621456217172184621)
                  ·
                    refine ⟨2130416858046081439569233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5681111621456217172184621 2130416858046081439569233)
                    ·
                      refine ⟨1597812643534561079676925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130416858046081439569233 1597812643534561079676925)
                      ·
                        rfl

theorem cell23_3111729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_3111729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111729 prefixEnd_3111729 := by exact prefixLift 3111729
  have htrace : WordTrace (prefixWord ++ tailWord_3111729) baseStart_3111729 baseEnd_3111729 := by
    simpa [prefixWord, tailWord_3111729, baseEnd_3111729] using wordTrace_append hprefix tailTrace_3111729
  have hstable : (prefixWord ++ tailWord_3111729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111729).length < 2 ^ (prefixWord ++ tailWord_3111729).sum := by decide
  have hdescent : baseEnd_3111729 < baseStart_3111729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111765 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 7]
def baseStart_3111765 : Nat := 118140960795 + 3111765 * 2 ^ 59
def prefixEnd_3111765 : Nat := 4983230072969 + 3 ^ 40 * 3111765 * 2
def baseEnd_3111765 : Nat := 177536792093124770980751

theorem tailTrace_3111765 : CollatzResearch.WordTrace tailWord_3111765 prefixEnd_3111765 177536792093124770980751 := by
  unfold tailWord_3111765
  simp only [CollatzResearch.WordTrace]
  refine ⟨113495393571614326996440749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75663595714409551330960499 113495393571614326996440749)
  ·
    refine ⟨42560772589355372623665281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113495393571614326996440749 42560772589355372623665281)
    ·
      refine ⟨31920579442016529467748961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42560772589355372623665281 31920579442016529467748961)
      ·
        refine ⟨23940434581512397100811721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31920579442016529467748961 23940434581512397100811721)
        ·
          refine ⟨17955325936134297825608791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23940434581512397100811721 17955325936134297825608791)
          ·
            refine ⟨26932988904201446738413187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17955325936134297825608791 26932988904201446738413187)
            ·
              refine ⟨40399483356302170107619781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26932988904201446738413187 40399483356302170107619781)
              ·
                refine ⟨7574903129306656895178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40399483356302170107619781 7574903129306656895178709)
                ·
                  refine ⟨177536792093124770980751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7574903129306656895178709 177536792093124770980751)
                  ·
                    rfl

theorem cell23_3111765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_3111765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111765 prefixEnd_3111765 := by exact prefixLift 3111765
  have htrace : WordTrace (prefixWord ++ tailWord_3111765) baseStart_3111765 baseEnd_3111765 := by
    simpa [prefixWord, tailWord_3111765, baseEnd_3111765] using wordTrace_append hprefix tailTrace_3111765
  have hstable : (prefixWord ++ tailWord_3111765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111765).length < 2 ^ (prefixWord ++ tailWord_3111765).sum := by decide
  have hdescent : baseEnd_3111765 < baseStart_3111765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111795 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 4, 5]
def baseStart_3111795 : Nat := 118140960795 + 3111795 * 2 ^ 59
def prefixEnd_3111795 : Nat := 4983230072969 + 3 ^ 40 * 3111795 * 2
def baseEnd_3111795 : Nat := 532615511085919273817207

theorem tailTrace_3111795 : CollatzResearch.WordTrace tailWord_3111795 prefixEnd_3111795 532615511085919273817207 := by
  unfold tailWord_3111795
  simp only [CollatzResearch.WordTrace]
  refine ⟨113496487761505642120032839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75664325174337094746688559 113496487761505642120032839)
  ·
    refine ⟨170244731642258463180049259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113496487761505642120032839 170244731642258463180049259)
    ·
      refine ⟨255367097463387694770073889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170244731642258463180049259 255367097463387694770073889)
      ·
        refine ⟨191525323097540771077555417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255367097463387694770073889 191525323097540771077555417)
        ·
          refine ⟨143643992323155578308166563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191525323097540771077555417 143643992323155578308166563)
          ·
            refine ⟨215465988484733367462249845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143643992323155578308166563 215465988484733367462249845)
            ·
              refine ⟨20199936420443753199585923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215465988484733367462249845 20199936420443753199585923)
              ·
                refine ⟨30299904630665629799378885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20199936420443753199585923 30299904630665629799378885)
                ·
                  refine ⟨5681232118249805587383541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30299904630665629799378885 5681232118249805587383541)
                  ·
                    refine ⟨532615511085919273817207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5681232118249805587383541 532615511085919273817207)
                    ·
                      rfl

theorem cell23_3111795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 5].length) (baseStart_3111795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111795 prefixEnd_3111795 := by exact prefixLift 3111795
  have htrace : WordTrace (prefixWord ++ tailWord_3111795) baseStart_3111795 baseEnd_3111795 := by
    simpa [prefixWord, tailWord_3111795, baseEnd_3111795] using wordTrace_append hprefix tailTrace_3111795
  have hstable : (prefixWord ++ tailWord_3111795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111795).length < 2 ^ (prefixWord ++ tailWord_3111795).sum := by decide
  have hdescent : baseEnd_3111795 < baseStart_3111795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111802 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_3111802 : Nat := 118140960795 + 3111802 * 2 ^ 59
def prefixEnd_3111802 : Nat := 4983230072969 + 3 ^ 40 * 3111802 * 2
def baseEnd_3111802 : Nat := 1597850127622339294064089

theorem tailTrace_3111802 : CollatzResearch.WordTrace tailWord_3111802 prefixEnd_3111802 1597850127622339294064089 := by
  unfold tailWord_3111802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28374185768120070578884415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75664495381653521543691773 28374185768120070578884415)
  ·
    refine ⟨42561278652180105868326623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28374185768120070578884415 42561278652180105868326623)
    ·
      refine ⟨63841917978270158802489935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42561278652180105868326623 63841917978270158802489935)
      ·
        refine ⟨95762876967405238203734903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63841917978270158802489935 95762876967405238203734903)
        ·
          refine ⟨143644315451107857305602355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95762876967405238203734903 143644315451107857305602355)
          ·
            refine ⟨215466473176661785958403533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143644315451107857305602355 215466473176661785958403533)
            ·
              refine ⟨80799927441248169734401325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215466473176661785958403533 80799927441248169734401325)
              ·
                refine ⟨30299972790468063650400497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80799927441248169734401325 30299972790468063650400497)
                ·
                  refine ⟨22724979592851047737800373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30299972790468063650400497 22724979592851047737800373)
                  ·
                    refine ⟨2130466836829785725418785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22724979592851047737800373 2130466836829785725418785)
                    ·
                      refine ⟨1597850127622339294064089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130466836829785725418785 1597850127622339294064089)
                      ·
                        rfl

theorem cell23_3111802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_3111802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111802 prefixEnd_3111802 := by exact prefixLift 3111802
  have htrace : WordTrace (prefixWord ++ tailWord_3111802) baseStart_3111802 baseEnd_3111802 := by
    simpa [prefixWord, tailWord_3111802, baseEnd_3111802] using wordTrace_append hprefix tailTrace_3111802
  have hstable : (prefixWord ++ tailWord_3111802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111802).length < 2 ^ (prefixWord ++ tailWord_3111802).sum := by decide
  have hdescent : baseEnd_3111802 < baseStart_3111802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111805 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_3111805 : Nat := 118140960795 + 3111805 * 2 ^ 59
def prefixEnd_3111805 : Nat := 4983230072969 + 3 ^ 40 * 3111805 * 2
def baseEnd_3111805 : Nat := 1597851668064302782326575

theorem tailTrace_3111805 : CollatzResearch.WordTrace tailWord_3111805 prefixEnd_3111805 1597851668064302782326575 := by
  unfold tailWord_3111805
  simp only [CollatzResearch.WordTrace]
  refine ⟨113496852491469413827896869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75664568327646275885264579 113496852491469413827896869)
  ·
    refine ⟨21280659842150515092730663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113496852491469413827896869 21280659842150515092730663)
    ·
      refine ⟨31920989763225772639095995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21280659842150515092730663 31920989763225772639095995)
      ·
        refine ⟨47881484644838658958643993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31920989763225772639095995 47881484644838658958643993)
        ·
          refine ⟨35911113483628994218982995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47881484644838658958643993 35911113483628994218982995)
          ·
            refine ⟨53866670225443491328474493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35911113483628994218982995 53866670225443491328474493)
            ·
              refine ⟨20200001334541309248177935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53866670225443491328474493 20200001334541309248177935)
              ·
                refine ⟨30300002001811963872266903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20200001334541309248177935 30300002001811963872266903)
                ·
                  refine ⟨45450003002717945808400355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30300002001811963872266903 45450003002717945808400355)
                  ·
                    refine ⟨68175004504076918712600533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45450003002717945808400355 68175004504076918712600533)
                    ·
                      refine ⟨1597851668064302782326575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68175004504076918712600533 1597851668064302782326575)
                      ·
                        rfl

theorem cell23_3111805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_3111805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111805 prefixEnd_3111805 := by exact prefixLift 3111805
  have htrace : WordTrace (prefixWord ++ tailWord_3111805) baseStart_3111805 baseEnd_3111805 := by
    simpa [prefixWord, tailWord_3111805, baseEnd_3111805] using wordTrace_append hprefix tailTrace_3111805
  have hstable : (prefixWord ++ tailWord_3111805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111805).length < 2 ^ (prefixWord ++ tailWord_3111805).sum := by decide
  have hdescent : baseEnd_3111805 < baseStart_3111805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111872 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 6]
def baseStart_3111872 : Nat := 118140960795 + 3111872 * 2 ^ 59
def prefixEnd_3111872 : Nat := 4983230072969 + 3 ^ 40 * 3111872 * 2
def baseEnd_3111872 : Nat := 177542896807572668909863

theorem tailTrace_3111872 : CollatzResearch.WordTrace tailWord_3111872 prefixEnd_3111872 177542896807572668909863 := by
  unfold tailWord_3111872
  simp only [CollatzResearch.WordTrace]
  refine ⟨56749648091113342135292935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75666197454817789513723913 56749648091113342135292935)
  ·
    refine ⟨85124472136670013202939403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56749648091113342135292935 85124472136670013202939403)
    ·
      refine ⟨127686708205005019804409105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85124472136670013202939403 127686708205005019804409105)
      ·
        refine ⟨95765031153753764853306829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127686708205005019804409105 95765031153753764853306829)
        ·
          refine ⟨35911886682657661819990061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95765031153753764853306829 35911886682657661819990061)
          ·
            refine ⟨13466957505996623182496273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35911886682657661819990061 13466957505996623182496273)
            ·
              refine ⟨10100218129497467386872205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13466957505996623182496273 10100218129497467386872205)
              ·
                refine ⟨3787581798561550270077077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10100218129497467386872205 3787581798561550270077077)
                ·
                  refine ⟨177542896807572668909863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3787581798561550270077077 177542896807572668909863)
                  ·
                    rfl

theorem cell23_3111872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_3111872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111872 prefixEnd_3111872 := by exact prefixLift 3111872
  have htrace : WordTrace (prefixWord ++ tailWord_3111872) baseStart_3111872 baseEnd_3111872 := by
    simpa [prefixWord, tailWord_3111872, baseEnd_3111872] using wordTrace_append hprefix tailTrace_3111872
  have hstable : (prefixWord ++ tailWord_3111872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111872).length < 2 ^ (prefixWord ++ tailWord_3111872).sum := by decide
  have hdescent : baseEnd_3111872 < baseStart_3111872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111875 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_3111875 : Nat := 118140960795 + 3111875 * 2 ^ 59
def prefixEnd_3111875 : Nat := 4983230072969 + 3 ^ 40 * 3111875 * 2
def baseEnd_3111875 : Nat := 1597887611710117508451253

theorem tailTrace_3111875 : CollatzResearch.WordTrace tailWord_3111875 prefixEnd_3111875 1597887611710117508451253 := by
  unfold tailWord_3111875
  simp only [CollatzResearch.WordTrace]
  refine ⟨113499405601215815782945079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75666270400810543855296719 113499405601215815782945079)
  ·
    refine ⟨170249108401823723674417619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113499405601215815782945079 170249108401823723674417619)
    ·
      refine ⟨255373662602735585511626429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170249108401823723674417619 255373662602735585511626429)
      ·
        refine ⟨95765123476025844566859911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255373662602735585511626429 95765123476025844566859911)
        ·
          refine ⟨143647685214038766850289867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95765123476025844566859911 143647685214038766850289867)
          ·
            refine ⟨215471527821058150275434801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143647685214038766850289867 215471527821058150275434801)
            ·
              refine ⟨161603645865793612706576101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215471527821058150275434801 161603645865793612706576101)
              ·
                refine ⟨30300683599836302382483019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161603645865793612706576101 30300683599836302382483019)
                ·
                  refine ⟨45451025399754453573724529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30300683599836302382483019 45451025399754453573724529)
                  ·
                    refine ⟨34088269049815840180293397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45451025399754453573724529 34088269049815840180293397)
                    ·
                      refine ⟨1597887611710117508451253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34088269049815840180293397 1597887611710117508451253)
                      ·
                        rfl

theorem cell23_3111875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_3111875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111875 prefixEnd_3111875 := by exact prefixLift 3111875
  have htrace : WordTrace (prefixWord ++ tailWord_3111875) baseStart_3111875 baseEnd_3111875 := by
    simpa [prefixWord, tailWord_3111875, baseEnd_3111875] using wordTrace_append hprefix tailTrace_3111875
  have hstable : (prefixWord ++ tailWord_3111875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111875).length < 2 ^ (prefixWord ++ tailWord_3111875).sum := by decide
  have hdescent : baseEnd_3111875 < baseStart_3111875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111886 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_3111886 : Nat := 118140960795 + 3111886 * 2 ^ 59
def prefixEnd_3111886 : Nat := 4983230072969 + 3 ^ 40 * 3111886 * 2
def baseEnd_3111886 : Nat := 1597893259997316965413703

theorem tailTrace_3111886 : CollatzResearch.WordTrace tailWord_3111886 prefixEnd_3111886 1597893259997316965413703 := by
  unfold tailWord_3111886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187475850521995582699439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75666537869450643107730341 14187475850521995582699439)
  ·
    refine ⟨21281213775782993374049159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14187475850521995582699439 21281213775782993374049159)
    ·
      refine ⟨31921820663674490061073739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21281213775782993374049159 31921820663674490061073739)
      ·
        refine ⟨47882730995511735091610609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31921820663674490061073739 47882730995511735091610609)
        ·
          refine ⟨35912048246633801318707957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47882730995511735091610609 35912048246633801318707957)
          ·
            refine ⟨3366754523121918873628871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35912048246633801318707957 3366754523121918873628871)
            ·
              refine ⟨5050131784682878310443307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366754523121918873628871 5050131784682878310443307)
              ·
                refine ⟨7575197677024317465664961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050131784682878310443307 7575197677024317465664961)
                ·
                  refine ⟨5681398257768238099248721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7575197677024317465664961 5681398257768238099248721)
                  ·
                    refine ⟨4261048693326178574436541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681398257768238099248721 4261048693326178574436541)
                    ·
                      refine ⟨1597893259997316965413703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261048693326178574436541 1597893259997316965413703)
                      ·
                        rfl

theorem cell23_3111886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_3111886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111886 prefixEnd_3111886 := by exact prefixLift 3111886
  have htrace : WordTrace (prefixWord ++ tailWord_3111886) baseStart_3111886 baseEnd_3111886 := by
    simpa [prefixWord, tailWord_3111886, baseEnd_3111886] using wordTrace_append hprefix tailTrace_3111886
  have hstable : (prefixWord ++ tailWord_3111886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111886).length < 2 ^ (prefixWord ++ tailWord_3111886).sum := by decide
  have hdescent : baseEnd_3111886 < baseStart_3111886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111893 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_3111893 : Nat := 118140960795 + 3111893 * 2 ^ 59
def prefixEnd_3111893 : Nat := 4983230072969 + 3 ^ 40 * 3111893 * 2
def baseEnd_3111893 : Nat := 532632284787299479342057

theorem tailTrace_3111893 : CollatzResearch.WordTrace tailWord_3111893 prefixEnd_3111893 532632284787299479342057 := by
  unfold tailWord_3111893
  simp only [CollatzResearch.WordTrace]
  refine ⟨113500062115150604857100333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75666708076767069904733555 113500062115150604857100333)
  ·
    refine ⟨42562523293181476821412625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113500062115150604857100333 42562523293181476821412625)
    ·
      refine ⟨31921892469886107616059469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42562523293181476821412625 31921892469886107616059469)
      ·
        refine ⟨11970709676207290356022301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31921892469886107616059469 11970709676207290356022301)
        ·
          refine ⟨4489016128577733883508363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11970709676207290356022301 4489016128577733883508363)
          ·
            refine ⟨6733524192866600825262545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489016128577733883508363 6733524192866600825262545)
            ·
              refine ⟨5050143144649950618946909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6733524192866600825262545 5050143144649950618946909)
              ·
                refine ⟨1893803679243731482105091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5050143144649950618946909 1893803679243731482105091)
                ·
                  refine ⟨2840705518865597223157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893803679243731482105091 2840705518865597223157637)
                  ·
                    refine ⟨532632284787299479342057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2840705518865597223157637 532632284787299479342057)
                    ·
                      rfl

theorem cell23_3111893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_3111893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111893 prefixEnd_3111893 := by exact prefixLift 3111893
  have htrace : WordTrace (prefixWord ++ tailWord_3111893) baseStart_3111893 baseEnd_3111893 := by
    simpa [prefixWord, tailWord_3111893, baseEnd_3111893] using wordTrace_append hprefix tailTrace_3111893
  have hstable : (prefixWord ++ tailWord_3111893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111893).length < 2 ^ (prefixWord ++ tailWord_3111893).sum := by decide
  have hdescent : baseEnd_3111893 < baseStart_3111893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111906 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3111906 : Nat := 118140960795 + 3111906 * 2 ^ 59
def prefixEnd_3111906 : Nat := 4983230072969 + 3 ^ 40 * 3111906 * 2
def baseEnd_3111906 : Nat := 177544836623378543018179

theorem tailTrace_3111906 : CollatzResearch.WordTrace tailWord_3111906 prefixEnd_3111906 177544836623378543018179 := by
  unfold tailWord_3111906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28375134066025877019330893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75667024176069005384882381 28375134066025877019330893)
  ·
    refine ⟨10640675274759703882249085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28375134066025877019330893 10640675274759703882249085)
    ·
      refine ⟨3990253228034888955843407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10640675274759703882249085 3990253228034888955843407)
      ·
        refine ⟨5985379842052333433765111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990253228034888955843407 5985379842052333433765111)
        ·
          refine ⟨8978069763078500150647667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985379842052333433765111 8978069763078500150647667)
          ·
            refine ⟨13467104644617750225971501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978069763078500150647667 13467104644617750225971501)
            ·
              refine ⟨5050164241731656334739313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13467104644617750225971501 5050164241731656334739313)
              ·
                refine ⟨3787623181298742251054485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050164241731656334739313 3787623181298742251054485)
                ·
                  refine ⟨177544836623378543018179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3787623181298742251054485 177544836623378543018179)
                  ·
                    rfl

theorem cell23_3111906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3111906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111906 prefixEnd_3111906 := by exact prefixLift 3111906
  have htrace : WordTrace (prefixWord ++ tailWord_3111906) baseStart_3111906 baseEnd_3111906 := by
    simpa [prefixWord, tailWord_3111906, baseEnd_3111906] using wordTrace_append hprefix tailTrace_3111906
  have hstable : (prefixWord ++ tailWord_3111906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111906).length < 2 ^ (prefixWord ++ tailWord_3111906).sum := by decide
  have hdescent : baseEnd_3111906 < baseStart_3111906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111915 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 10]
def baseStart_3111915 : Nat := 118140960795 + 3111915 * 2 ^ 59
def prefixEnd_3111915 : Nat := 4983230072969 + 3 ^ 40 * 3111915 * 2
def baseEnd_3111915 : Nat := 532636050312099117317023

theorem tailTrace_3111915 : CollatzResearch.WordTrace tailWord_3111915 prefixEnd_3111915 532636050312099117317023 := by
  unfold tailWord_3111915
  simp only [CollatzResearch.WordTrace]
  refine ⟨113500864521070902614401199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75667243014047268409600799 113500864521070902614401199)
  ·
    refine ⟨170251296781606353921601799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113500864521070902614401199 170251296781606353921601799)
    ·
      refine ⟨255376945172409530882402699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170251296781606353921601799 255376945172409530882402699)
      ·
        refine ⟨383065417758614296323604049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255376945172409530882402699 383065417758614296323604049)
        ·
          refine ⟨287299063318960722242703037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383065417758614296323604049 287299063318960722242703037)
          ·
            refine ⟨107737148744610270841013639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287299063318960722242703037 107737148744610270841013639)
            ·
              refine ⟨161605723116915406261520459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107737148744610270841013639 161605723116915406261520459)
              ·
                refine ⟨242408584675373109392280689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161605723116915406261520459 242408584675373109392280689)
                ·
                  refine ⟨181806438506529832044210517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242408584675373109392280689 181806438506529832044210517)
                  ·
                    refine ⟨532636050312099117317023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 181806438506529832044210517 532636050312099117317023)
                    ·
                      rfl

theorem cell23_3111915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_3111915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111915 prefixEnd_3111915 := by exact prefixLift 3111915
  have htrace : WordTrace (prefixWord ++ tailWord_3111915) baseStart_3111915 baseEnd_3111915 := by
    simpa [prefixWord, tailWord_3111915, baseEnd_3111915] using wordTrace_append hprefix tailTrace_3111915
  have hstable : (prefixWord ++ tailWord_3111915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111915).length < 2 ^ (prefixWord ++ tailWord_3111915).sum := by decide
  have hdescent : baseEnd_3111915 < baseStart_3111915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111926 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3111926 : Nat := 118140960795 + 3111926 * 2 ^ 59
def prefixEnd_3111926 : Nat := 4983230072969 + 3 ^ 40 * 3111926 * 2
def baseEnd_3111926 : Nat := 1597913799223496808913519

theorem tailTrace_3111926 : CollatzResearch.WordTrace tailWord_3111926 prefixEnd_3111926 1597913799223496808913519 := by
  unfold tailWord_3111926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093829107751940718315727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75667510482687367662034421 7093829107751940718315727)
  ·
    refine ⟨10640743661627911077473591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7093829107751940718315727 10640743661627911077473591)
    ·
      refine ⟨15961115492441866616210387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10640743661627911077473591 15961115492441866616210387)
      ·
        refine ⟨23941673238662799924315581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961115492441866616210387 23941673238662799924315581)
        ·
          refine ⟨8978127464498549971618343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23941673238662799924315581 8978127464498549971618343)
          ·
            refine ⟨13467191196747824957427515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978127464498549971618343 13467191196747824957427515)
            ·
              refine ⟨20200786795121737436141273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13467191196747824957427515 20200786795121737436141273)
              ·
                refine ⟨15150590096341303077105955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20200786795121737436141273 15150590096341303077105955)
                ·
                  refine ⟨22725885144511954615658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15150590096341303077105955 22725885144511954615658933)
                  ·
                    refine ⟨2130551732297995745218025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22725885144511954615658933 2130551732297995745218025)
                    ·
                      refine ⟨1597913799223496808913519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130551732297995745218025 1597913799223496808913519)
                      ·
                        rfl

theorem cell23_3111926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3111926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111926 prefixEnd_3111926 := by exact prefixLift 3111926
  have htrace : WordTrace (prefixWord ++ tailWord_3111926) baseStart_3111926 baseEnd_3111926 := by
    simpa [prefixWord, tailWord_3111926, baseEnd_3111926] using wordTrace_append hprefix tailTrace_3111926
  have hstable : (prefixWord ++ tailWord_3111926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111926).length < 2 ^ (prefixWord ++ tailWord_3111926).sum := by decide
  have hdescent : baseEnd_3111926 < baseStart_3111926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111950 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_3111950 : Nat := 118140960795 + 3111950 * 2 ^ 59
def prefixEnd_3111950 : Nat := 4983230072969 + 3 ^ 40 * 3111950 * 2
def baseEnd_3111950 : Nat := 1597926122759204715013409

theorem tailTrace_3111950 : CollatzResearch.WordTrace tailWord_3111950 prefixEnd_3111950 1597926122759204715013409 := by
  unfold tailWord_3111950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187767634493012948990663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75668094050629402394616869 14187767634493012948990663)
  ·
    refine ⟨21281651451739519423485995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14187767634493012948990663 21281651451739519423485995)
    ·
      refine ⟨31922477177609279135228993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21281651451739519423485995 31922477177609279135228993)
      ·
        refine ⟨23941857883206959351421745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31922477177609279135228993 23941857883206959351421745)
        ·
          refine ⟨17956393412405219513566309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23941857883206959351421745 17956393412405219513566309)
          ·
            refine ⟨3366823764825978658793683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17956393412405219513566309 3366823764825978658793683)
            ·
              refine ⟨5050235647238967988190525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366823764825978658793683 5050235647238967988190525)
              ·
                refine ⟨1893838367714612995571447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5050235647238967988190525 1893838367714612995571447)
                ·
                  refine ⟨2840757551571919493357171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893838367714612995571447 2840757551571919493357171)
                  ·
                    refine ⟨4261136327357879240035757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2840757551571919493357171 4261136327357879240035757)
                    ·
                      refine ⟨1597926122759204715013409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261136327357879240035757 1597926122759204715013409)
                      ·
                        rfl

theorem cell23_3111950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_3111950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111950 prefixEnd_3111950 := by exact prefixLift 3111950
  have htrace : WordTrace (prefixWord ++ tailWord_3111950) baseStart_3111950 baseEnd_3111950 := by
    simpa [prefixWord, tailWord_3111950, baseEnd_3111950] using wordTrace_append hprefix tailTrace_3111950
  have hstable : (prefixWord ++ tailWord_3111950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111950).length < 2 ^ (prefixWord ++ tailWord_3111950).sum := by decide
  have hdescent : baseEnd_3111950 < baseStart_3111950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111959 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3111959 : Nat := 118140960795 + 3111959 * 2 ^ 59
def prefixEnd_3111959 : Nat := 4983230072969 + 3 ^ 40 * 3111959 * 2
def baseEnd_3111959 : Nat := 1597930744085095179800867

theorem tailTrace_3111959 : CollatzResearch.WordTrace tailWord_3111959 prefixEnd_3111959 1597930744085095179800867 := by
  unfold tailWord_3111959
  simp only [CollatzResearch.WordTrace]
  refine ⟨113502469332911498129002931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75668312888607665419335287 113502469332911498129002931)
  ·
    refine ⟨170253703999367247193504397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113502469332911498129002931 170253703999367247193504397)
    ·
      refine ⟨63845138999762717697564149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170253703999367247193504397 63845138999762717697564149)
      ·
        refine ⟨5985481781227754784146639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63845138999762717697564149 5985481781227754784146639)
        ·
          refine ⟨8978222671841632176219959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985481781227754784146639 8978222671841632176219959)
          ·
            refine ⟨13467334007762448264329939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978222671841632176219959 13467334007762448264329939)
            ·
              refine ⟨20201001011643672396494909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13467334007762448264329939 20201001011643672396494909)
              ·
                refine ⟨7575375379366377148685591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20201001011643672396494909 7575375379366377148685591)
                ·
                  refine ⟨11363063069049565723028387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7575375379366377148685591 11363063069049565723028387)
                  ·
                    refine ⟨17044594603574348584542581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11363063069049565723028387 17044594603574348584542581)
                    ·
                      refine ⟨1597930744085095179800867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17044594603574348584542581 1597930744085095179800867)
                      ·
                        rfl

theorem cell23_3111959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3111959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111959 prefixEnd_3111959 := by exact prefixLift 3111959
  have htrace : WordTrace (prefixWord ++ tailWord_3111959) baseStart_3111959 baseEnd_3111959 := by
    simpa [prefixWord, tailWord_3111959, baseEnd_3111959] using wordTrace_append hprefix tailTrace_3111959
  have hstable : (prefixWord ++ tailWord_3111959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111959).length < 2 ^ (prefixWord ++ tailWord_3111959).sum := by decide
  have hdescent : baseEnd_3111959 < baseStart_3111959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111989 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3111989 : Nat := 118140960795 + 3111989 * 2 ^ 59
def prefixEnd_3111989 : Nat := 4983230072969 + 3 ^ 40 * 3111989 * 2
def baseEnd_3111989 : Nat := 1597946148504730062425729

theorem tailTrace_3111989 : CollatzResearch.WordTrace tailWord_3111989 prefixEnd_3111989 1597946148504730062425729 := by
  unfold tailWord_3111989
  simp only [CollatzResearch.WordTrace]
  refine ⟨113503563522802813252595021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75669042348535208835063347 113503563522802813252595021)
  ·
    refine ⟨42563836321051054969723133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113503563522802813252595021 42563836321051054969723133)
    ·
      refine ⟨15961438620394145613646175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42563836321051054969723133 15961438620394145613646175)
      ·
        refine ⟨23942157930591218420469263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961438620394145613646175 23942157930591218420469263)
        ·
          refine ⟨35913236895886827630703895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23942157930591218420469263 35913236895886827630703895)
          ·
            refine ⟨53869855343830241446055843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35913236895886827630703895 53869855343830241446055843)
            ·
              refine ⟨80804783015745362169083765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53869855343830241446055843 80804783015745362169083765)
              ·
                refine ⟨7575448407726127703351603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80804783015745362169083765 7575448407726127703351603)
                ·
                  refine ⟨11363172611589191555027405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7575448407726127703351603 11363172611589191555027405)
                  ·
                    refine ⟨4261189729345946833135277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11363172611589191555027405 4261189729345946833135277)
                    ·
                      refine ⟨1597946148504730062425729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261189729345946833135277 1597946148504730062425729)
                      ·
                        rfl

theorem cell23_3111989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3111989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111989 prefixEnd_3111989 := by exact prefixLift 3111989
  have htrace : WordTrace (prefixWord ++ tailWord_3111989) baseStart_3111989 baseEnd_3111989 := by
    simpa [prefixWord, tailWord_3111989, baseEnd_3111989] using wordTrace_append hprefix tailTrace_3111989
  have hstable : (prefixWord ++ tailWord_3111989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111989).length < 2 ^ (prefixWord ++ tailWord_3111989).sum := by decide
  have hdescent : baseEnd_3111989 < baseStart_3111989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111993 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3111993 : Nat := 118140960795 + 3111993 * 2 ^ 59
def prefixEnd_3111993 : Nat := 4983230072969 + 3 ^ 40 * 3111993 * 2
def baseEnd_3111993 : Nat := 1597948202427348046775711

theorem tailTrace_3111993 : CollatzResearch.WordTrace tailWord_3111993 prefixEnd_3111993 1597948202427348046775711 := by
  unfold tailWord_3111993
  simp only [CollatzResearch.WordTrace]
  refine ⟨113503709414788321935740633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75669139609858881290493755 113503709414788321935740633)
  ·
    refine ⟨85127782061091241451805475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113503709414788321935740633 85127782061091241451805475)
    ·
      refine ⟨127691673091636862177708213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85127782061091241451805475 127691673091636862177708213)
      ·
        refine ⟨11971094352340955829160145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127691673091636862177708213 11971094352340955829160145)
        ·
          refine ⟨8978320764255716871870109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971094352340955829160145 8978320764255716871870109)
          ·
            refine ⟨3366870286595893826951291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8978320764255716871870109 3366870286595893826951291)
            ·
              refine ⟨5050305429893840740426937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366870286595893826951291 5050305429893840740426937)
              ·
                refine ⟨3787729072420380555320203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050305429893840740426937 3787729072420380555320203)
                ·
                  refine ⟨5681593608630570832980305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787729072420380555320203 5681593608630570832980305)
                  ·
                    refine ⟨4261195206472928124735229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681593608630570832980305 4261195206472928124735229)
                    ·
                      refine ⟨1597948202427348046775711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261195206472928124735229 1597948202427348046775711)
                      ·
                        rfl

theorem cell23_3111993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3111993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3111993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3111993 prefixEnd_3111993 := by exact prefixLift 3111993
  have htrace : WordTrace (prefixWord ++ tailWord_3111993) baseStart_3111993 baseEnd_3111993 := by
    simpa [prefixWord, tailWord_3111993, baseEnd_3111993] using wordTrace_append hprefix tailTrace_3111993
  have hstable : (prefixWord ++ tailWord_3111993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111993).length < 2 ^ (prefixWord ++ tailWord_3111993).sum := by decide
  have hdescent : baseEnd_3111993 < baseStart_3111993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112016 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2]
def baseStart_3112016 : Nat := 118140960795 + 3112016 * 2 ^ 59
def prefixEnd_3112016 : Nat := 4983230072969 + 3 ^ 40 * 3112016 * 2
def baseEnd_3112016 : Nat := 1597960012482401456788105

theorem tailTrace_3112016 : CollatzResearch.WordTrace tailWord_3112016 prefixEnd_3112016 1597960012482401456788105 := by
  unfold tailWord_3112016
  simp only [CollatzResearch.WordTrace]
  refine ⟨56752274146852498431913951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75669698862469997909218601 56752274146852498431913951)
  ·
    refine ⟨85128411220278747647870927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56752274146852498431913951 85128411220278747647870927)
    ·
      refine ⟨127692616830418121471806391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85128411220278747647870927 127692616830418121471806391)
      ·
        refine ⟨191538925245627182207709587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127692616830418121471806391 191538925245627182207709587)
        ·
          refine ⟨287308387868440773311564381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191538925245627182207709587 287308387868440773311564381)
          ·
            refine ⟨107740645450665289991836643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287308387868440773311564381 107740645450665289991836643)
            ·
              refine ⟨161610968175997934987754965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107740645450665289991836643 161610968175997934987754965)
              ·
                refine ⟨3787757066624951601275507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161610968175997934987754965 3787757066624951601275507)
                ·
                  refine ⟨5681635599937427401913261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787757066624951601275507 5681635599937427401913261)
                  ·
                    refine ⟨2130613349976535275717473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5681635599937427401913261 2130613349976535275717473)
                    ·
                      refine ⟨1597960012482401456788105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130613349976535275717473 1597960012482401456788105)
                      ·
                        rfl

theorem cell23_3112016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2].length) (baseStart_3112016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112016 prefixEnd_3112016 := by exact prefixLift 3112016
  have htrace : WordTrace (prefixWord ++ tailWord_3112016) baseStart_3112016 baseEnd_3112016 := by
    simpa [prefixWord, tailWord_3112016, baseEnd_3112016] using wordTrace_append hprefix tailTrace_3112016
  have hstable : (prefixWord ++ tailWord_3112016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112016).length < 2 ^ (prefixWord ++ tailWord_3112016).sum := by decide
  have hdescent : baseEnd_3112016 < baseStart_3112016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112039 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3112039 : Nat := 118140960795 + 3112039 * 2 ^ 59
def prefixEnd_3112039 : Nat := 4983230072969 + 3 ^ 40 * 3112039 * 2
def baseEnd_3112039 : Nat := 532657274179151622266833

theorem tailTrace_3112039 : CollatzResearch.WordTrace tailWord_3112039 prefixEnd_3112039 532657274179151622266833 := by
  unfold tailWord_3112039
  simp only [CollatzResearch.WordTrace]
  refine ⟨113505387172621671791915171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75670258115081114527943447 113505387172621671791915171)
  ·
    refine ⟨170258080758932507687872757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113505387172621671791915171 170258080758932507687872757)
    ·
      refine ⟨15961695071149922595738071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170258080758932507687872757 15961695071149922595738071)
      ·
        refine ⟨23942542606724883893607107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15961695071149922595738071 23942542606724883893607107)
        ·
          refine ⟨35913813910087325840410661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23942542606724883893607107 35913813910087325840410661)
          ·
            refine ⟨6733840108141373595076999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35913813910087325840410661 6733840108141373595076999)
            ·
              refine ⟨10100760162212060392615499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733840108141373595076999 10100760162212060392615499)
              ·
                refine ⟨15151140243318090588923249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10100760162212060392615499 15151140243318090588923249)
                ·
                  refine ⟨11363355182488567941692437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15151140243318090588923249 11363355182488567941692437)
                  ·
                    refine ⟨532657274179151622266833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11363355182488567941692437 532657274179151622266833)
                    ·
                      rfl

theorem cell23_3112039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3112039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112039 prefixEnd_3112039 := by exact prefixLift 3112039
  have htrace : WordTrace (prefixWord ++ tailWord_3112039) baseStart_3112039 baseEnd_3112039 := by
    simpa [prefixWord, tailWord_3112039, baseEnd_3112039] using wordTrace_append hprefix tailTrace_3112039
  have hstable : (prefixWord ++ tailWord_3112039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112039).length < 2 ^ (prefixWord ++ tailWord_3112039).sum := by decide
  have hdescent : baseEnd_3112039 < baseStart_3112039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112119 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3112119 : Nat := 118140960795 + 3112119 * 2 ^ 59
def prefixEnd_3112119 : Nat := 4983230072969 + 3 ^ 40 * 3112119 * 2
def baseEnd_3112119 : Nat := 1598012900989814553800131

theorem tailTrace_3112119 : CollatzResearch.WordTrace tailWord_3112119 prefixEnd_3112119 1598012900989814553800131 := by
  unfold tailWord_3112119
  simp only [CollatzResearch.WordTrace]
  refine ⟨113508305012331845454827411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75672203341554563636551607 113508305012331845454827411)
  ·
    refine ⟨170262457518497768182241117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113508305012331845454827411 170262457518497768182241117)
    ·
      refine ⟨63848421569436663068340419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170262457518497768182241117 63848421569436663068340419)
      ·
        refine ⟨95772632354154994602510629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63848421569436663068340419 95772632354154994602510629)
        ·
          refine ⟨17957368566404061487970743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95772632354154994602510629 17957368566404061487970743)
          ·
            refine ⟨26936052849606092231956115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17957368566404061487970743 26936052849606092231956115)
            ·
              refine ⟨40404079274409138347934173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26936052849606092231956115 40404079274409138347934173)
              ·
                refine ⟨15151529727903426880475315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40404079274409138347934173 15151529727903426880475315)
                ·
                  refine ⟨22727294591855140320712973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15151529727903426880475315 22727294591855140320712973)
                  ·
                    refine ⟨8522735471945677620267365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22727294591855140320712973 8522735471945677620267365)
                    ·
                      refine ⟨1598012900989814553800131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8522735471945677620267365 1598012900989814553800131)
                      ·
                        rfl

theorem cell23_3112119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3112119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112119 prefixEnd_3112119 := by exact prefixLift 3112119
  have htrace : WordTrace (prefixWord ++ tailWord_3112119) baseStart_3112119 baseEnd_3112119 := by
    simpa [prefixWord, tailWord_3112119, baseEnd_3112119] using wordTrace_append hprefix tailTrace_3112119
  have hstable : (prefixWord ++ tailWord_3112119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112119).length < 2 ^ (prefixWord ++ tailWord_3112119).sum := by decide
  have hdescent : baseEnd_3112119 < baseStart_3112119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112136 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_3112136 : Nat := 118140960795 + 3112136 * 2 ^ 59
def prefixEnd_3112136 : Nat := 4983230072969 + 3 ^ 40 * 3112136 * 2
def baseEnd_3112136 : Nat := 1598021630160940987287553

theorem tailTrace_3112136 : CollatzResearch.WordTrace tailWord_3112136 prefixEnd_3112136 1598021630160940987287553 := by
  unfold tailWord_3112136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56754462526635128679098131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75672616702180171572130841 56754462526635128679098131)
  ·
    refine ⟨85131693789952693018647197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56754462526635128679098131 85131693789952693018647197)
    ·
      refine ⟨31924385171232259881992699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85131693789952693018647197 31924385171232259881992699)
      ·
        refine ⟨47886577756848389822989049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31924385171232259881992699 47886577756848389822989049)
        ·
          refine ⟨35914933317636292367241787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47886577756848389822989049 35914933317636292367241787)
          ·
            refine ⟨53872399976454438550862681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35914933317636292367241787 53872399976454438550862681)
            ·
              refine ⟨40404299982340828913147011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53872399976454438550862681 40404299982340828913147011)
              ·
                refine ⟨60606449973511243369720517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40404299982340828913147011 60606449973511243369720517)
                ·
                  refine ⟨11363709370033358131822597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60606449973511243369720517 11363709370033358131822597)
                  ·
                    refine ⟨2130695506881254649716737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11363709370033358131822597 2130695506881254649716737)
                    ·
                      refine ⟨1598021630160940987287553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130695506881254649716737 1598021630160940987287553)
                      ·
                        rfl

theorem cell23_3112136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_3112136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112136 prefixEnd_3112136 := by exact prefixLift 3112136
  have htrace : WordTrace (prefixWord ++ tailWord_3112136) baseStart_3112136 baseEnd_3112136 := by
    simpa [prefixWord, tailWord_3112136, baseEnd_3112136] using wordTrace_append hprefix tailTrace_3112136
  have hstable : (prefixWord ++ tailWord_3112136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112136).length < 2 ^ (prefixWord ++ tailWord_3112136).sum := by decide
  have hdescent : baseEnd_3112136 < baseStart_3112136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112139 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3]
def baseStart_3112139 : Nat := 118140960795 + 3112139 * 2 ^ 59
def prefixEnd_3112139 : Nat := 4983230072969 + 3 ^ 40 * 3112139 * 2
def baseEnd_3112139 : Nat := 1598023170602904475550039

theorem tailTrace_3112139 : CollatzResearch.WordTrace tailWord_3112139 prefixEnd_3112139 1598023170602904475550039 := by
  unfold tailWord_3112139
  simp only [CollatzResearch.WordTrace]
  refine ⟨113509034472259388870555471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75672689648172925913703647 113509034472259388870555471)
  ·
    refine ⟨170263551708389083305833207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113509034472259388870555471 170263551708389083305833207)
    ·
      refine ⟨255395327562583624958749811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170263551708389083305833207 255395327562583624958749811)
      ·
        refine ⟨383092991343875437438124717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255395327562583624958749811 383092991343875437438124717)
        ·
          refine ⟨143659871753953289039296769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383092991343875437438124717 143659871753953289039296769)
          ·
            refine ⟨107744903815464966779472577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143659871753953289039296769 107744903815464966779472577)
            ·
              refine ⟨80808677861598725084604433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107744903815464966779472577 80808677861598725084604433)
              ·
                refine ⟨60606508396199043813453325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80808677861598725084604433 60606508396199043813453325)
                ·
                  refine ⟨22727440648574641430044997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60606508396199043813453325 22727440648574641430044997)
                  ·
                    refine ⟨4261395121607745268133437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22727440648574641430044997 4261395121607745268133437)
                    ·
                      refine ⟨1598023170602904475550039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261395121607745268133437 1598023170602904475550039)
                      ·
                        rfl

theorem cell23_3112139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3].length) (baseStart_3112139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112139 prefixEnd_3112139 := by exact prefixLift 3112139
  have htrace : WordTrace (prefixWord ++ tailWord_3112139) baseStart_3112139 baseEnd_3112139 := by
    simpa [prefixWord, tailWord_3112139, baseEnd_3112139] using wordTrace_append hprefix tailTrace_3112139
  have hstable : (prefixWord ++ tailWord_3112139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112139).length < 2 ^ (prefixWord ++ tailWord_3112139).sum := by decide
  have hdescent : baseEnd_3112139 < baseStart_3112139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112173 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3112173 : Nat := 118140960795 + 3112173 * 2 ^ 59
def prefixEnd_3112173 : Nat := 4983230072969 + 3 ^ 40 * 3112173 * 2
def baseEnd_3112173 : Nat := 1598040628945157342524883

theorem tailTrace_3112173 : CollatzResearch.WordTrace tailWord_3112173 prefixEnd_3112173 1598040628945157342524883 := by
  unfold tailWord_3112173
  simp only [CollatzResearch.WordTrace]
  refine ⟨113510274554136212677293173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75673516369424141784862115 113510274554136212677293173)
  ·
    refine ⟨10641588239450269938496235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113510274554136212677293173 10641588239450269938496235)
    ·
      refine ⟨15962382359175404907744353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10641588239450269938496235 15962382359175404907744353)
      ·
        refine ⟨11971786769381553680808265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15962382359175404907744353 11971786769381553680808265)
        ·
          refine ⟨8978840077036165260606199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971786769381553680808265 8978840077036165260606199)
          ·
            refine ⟨13468260115554247890909299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978840077036165260606199 13468260115554247890909299)
            ·
              refine ⟨20202390173331371836363949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13468260115554247890909299 20202390173331371836363949)
              ·
                refine ⟨7575896314999264438636481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20202390173331371836363949 7575896314999264438636481)
                ·
                  refine ⟨5681922236249448328977361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7575896314999264438636481 5681922236249448328977361)
                  ·
                    refine ⟨4261441677187086246733021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5681922236249448328977361 4261441677187086246733021)
                    ·
                      refine ⟨1598040628945157342524883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261441677187086246733021 1598040628945157342524883)
                      ·
                        rfl

theorem cell23_3112173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3112173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112173 prefixEnd_3112173 := by exact prefixLift 3112173
  have htrace : WordTrace (prefixWord ++ tailWord_3112173) baseStart_3112173 baseEnd_3112173 := by
    simpa [prefixWord, tailWord_3112173, baseEnd_3112173] using wordTrace_append hprefix tailTrace_3112173
  have hstable : (prefixWord ++ tailWord_3112173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112173).length < 2 ^ (prefixWord ++ tailWord_3112173).sum := by decide
  have hdescent : baseEnd_3112173 < baseStart_3112173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112206 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3112206 : Nat := 118140960795 + 3112206 * 2 ^ 59
def prefixEnd_3112206 : Nat := 4983230072969 + 3 ^ 40 * 3112206 * 2
def baseEnd_3112206 : Nat := 532685857935585237804077

theorem tailTrace_3112206 : CollatzResearch.WordTrace tailWord_3112206 prefixEnd_3112206 532685857935585237804077 := by
  unfold tailWord_3112206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188934770377082414155559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75674318775344439542162981 14188934770377082414155559)
  ·
    refine ⟨21283402155565623621233339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14188934770377082414155559 21283402155565623621233339)
    ·
      refine ⟨31925103233348435431850009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21283402155565623621233339 31925103233348435431850009)
      ·
        refine ⟨23943827425011326573887507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31925103233348435431850009 23943827425011326573887507)
        ·
          refine ⟨35915741137516989860831261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23943827425011326573887507 35915741137516989860831261)
          ·
            refine ⟨13468402926568871197811723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35915741137516989860831261 13468402926568871197811723)
            ·
              refine ⟨20202604389853306796717585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13468402926568871197811723 20202604389853306796717585)
              ·
                refine ⟨15151953292389980097538189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20202604389853306796717585 15151953292389980097538189)
                ·
                  refine ⟨5681982484646242536576821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15151953292389980097538189 5681982484646242536576821)
                  ·
                    refine ⟨532685857935585237804077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5681982484646242536576821 532685857935585237804077)
                    ·
                      rfl

theorem cell23_3112206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3112206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112206 prefixEnd_3112206 := by exact prefixLift 3112206
  have htrace : WordTrace (prefixWord ++ tailWord_3112206) baseStart_3112206 baseEnd_3112206 := by
    simpa [prefixWord, tailWord_3112206, baseEnd_3112206] using wordTrace_append hprefix tailTrace_3112206
  have hstable : (prefixWord ++ tailWord_3112206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112206).length < 2 ^ (prefixWord ++ tailWord_3112206).sum := by decide
  have hdescent : baseEnd_3112206 < baseStart_3112206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112236 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_3112236 : Nat := 118140960795 + 3112236 * 2 ^ 59
def prefixEnd_3112236 : Nat := 4983230072969 + 3 ^ 40 * 3112236 * 2
def baseEnd_3112236 : Nat := 532690992742130198679031

theorem tailTrace_3112236 : CollatzResearch.WordTrace tailWord_3112236 prefixEnd_3112236 532690992742130198679031 := by
  unfold tailWord_3112236
  simp only [CollatzResearch.WordTrace]
  refine ⟨56756286176453987218418281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75675048235271982957891041 56756286176453987218418281)
  ·
    refine ⟨42567214632340490413813711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56756286176453987218418281 42567214632340490413813711)
    ·
      refine ⟨63850821948510735620720567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42567214632340490413813711 63850821948510735620720567)
      ·
        refine ⟨95776232922766103431080851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63850821948510735620720567 95776232922766103431080851)
        ·
          refine ⟨143664349384149155146621277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95776232922766103431080851 143664349384149155146621277)
          ·
            refine ⟨53874131019055933179982979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143664349384149155146621277 53874131019055933179982979)
            ·
              refine ⟨80811196528583899769974469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53874131019055933179982979 80811196528583899769974469)
              ·
                refine ⟨15152099349109481206870213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80811196528583899769974469 15152099349109481206870213)
                ·
                  refine ⟨2841018627958027726288165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15152099349109481206870213 2841018627958027726288165)
                  ·
                    refine ⟨532690992742130198679031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2841018627958027726288165 532690992742130198679031)
                    ·
                      rfl

theorem cell23_3112236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_3112236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112236 prefixEnd_3112236 := by exact prefixLift 3112236
  have htrace : WordTrace (prefixWord ++ tailWord_3112236) baseStart_3112236 baseEnd_3112236 := by
    simpa [prefixWord, tailWord_3112236, baseEnd_3112236] using wordTrace_append hprefix tailTrace_3112236
  have hstable : (prefixWord ++ tailWord_3112236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112236).length < 2 ^ (prefixWord ++ tailWord_3112236).sum := by decide
  have hdescent : baseEnd_3112236 < baseStart_3112236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112239 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_3112239 : Nat := 118140960795 + 3112239 * 2 ^ 59
def prefixEnd_3112239 : Nat := 4983230072969 + 3 ^ 40 * 3112239 * 2
def baseEnd_3112239 : Nat := 1598074518668354084299579

theorem tailTrace_3112239 : CollatzResearch.WordTrace tailWord_3112239 prefixEnd_3112239 1598074518668354084299579 := by
  unfold tailWord_3112239
  simp only [CollatzResearch.WordTrace]
  refine ⟨113512681771897105949195771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75675121181264737299463847 113512681771897105949195771)
  ·
    refine ⟨170269022657845658923793657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113512681771897105949195771 170269022657845658923793657)
    ·
      refine ⟨127701766993384244192845243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170269022657845658923793657 127701766993384244192845243)
      ·
        refine ⟨191552650490076366289267865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127701766993384244192845243 191552650490076366289267865)
        ·
          refine ⟨143664487867557274716950899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191552650490076366289267865 143664487867557274716950899)
          ·
            refine ⟨215496731801335912075426349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143664487867557274716950899 215496731801335912075426349)
            ·
              refine ⟨80811274425500967028284881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215496731801335912075426349 80811274425500967028284881)
              ·
                refine ⟨60608455819125725271213661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80811274425500967028284881 60608455819125725271213661)
                ·
                  refine ⟨22728170932172146976705123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60608455819125725271213661 22728170932172146976705123)
                  ·
                    refine ⟨34092256398258220465057685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22728170932172146976705123 34092256398258220465057685)
                    ·
                      refine ⟨1598074518668354084299579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34092256398258220465057685 1598074518668354084299579)
                      ·
                        rfl

theorem cell23_3112239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_3112239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112239 prefixEnd_3112239 := by exact prefixLift 3112239
  have htrace : WordTrace (prefixWord ++ tailWord_3112239) baseStart_3112239 baseEnd_3112239 := by
    simpa [prefixWord, tailWord_3112239, baseEnd_3112239] using wordTrace_append hprefix tailTrace_3112239
  have hstable : (prefixWord ++ tailWord_3112239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112239).length < 2 ^ (prefixWord ++ tailWord_3112239).sum := by decide
  have hdescent : baseEnd_3112239 < baseStart_3112239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112243 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 4]
def baseStart_3112243 : Nat := 118140960795 + 3112243 * 2 ^ 59
def prefixEnd_3112243 : Nat := 4983230072969 + 3 ^ 40 * 3112243 * 2
def baseEnd_3112243 : Nat := 1598076572590972068649561

theorem tailTrace_3112243 : CollatzResearch.WordTrace tailWord_3112243 prefixEnd_3112243 1598076572590972068649561 := by
  unfold tailWord_3112243
  simp only [CollatzResearch.WordTrace]
  refine ⟨113512827663882614632341383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75675218442588409754894255 113512827663882614632341383)
  ·
    refine ⟨170269241495823921948512075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113512827663882614632341383 170269241495823921948512075)
    ·
      refine ⟨255403862243735882922768113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170269241495823921948512075 255403862243735882922768113)
      ·
        refine ⟨191552896682801912192076085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255403862243735882922768113 191552896682801912192076085)
        ·
          refine ⟨17958084064012679268007133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191552896682801912192076085 17958084064012679268007133)
          ·
            refine ⟨6734281524004754725502675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17958084064012679268007133 6734281524004754725502675)
            ·
              refine ⟨10101422286007132088254013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734281524004754725502675 10101422286007132088254013)
              ·
                refine ⟨3788033357252674533095255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10101422286007132088254013 3788033357252674533095255)
                ·
                  refine ⟨5682050035879011799642883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788033357252674533095255 5682050035879011799642883)
                  ·
                    refine ⟨8523075053818517699464325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682050035879011799642883 8523075053818517699464325)
                    ·
                      refine ⟨1598076572590972068649561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8523075053818517699464325 1598076572590972068649561)
                      ·
                        rfl

theorem cell23_3112243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_3112243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112243 prefixEnd_3112243 := by exact prefixLift 3112243
  have htrace : WordTrace (prefixWord ++ tailWord_3112243) baseStart_3112243 baseEnd_3112243 := by
    simpa [prefixWord, tailWord_3112243, baseEnd_3112243] using wordTrace_append hprefix tailTrace_3112243
  have hstable : (prefixWord ++ tailWord_3112243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112243).length < 2 ^ (prefixWord ++ tailWord_3112243).sum := by decide
  have hdescent : baseEnd_3112243 < baseStart_3112243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112259 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_3112259 : Nat := 118140960795 + 3112259 * 2 ^ 59
def prefixEnd_3112259 : Nat := 4983230072969 + 3 ^ 40 * 3112259 * 2
def baseEnd_3112259 : Nat := 1598084788281444006049487

theorem tailTrace_3112259 : CollatzResearch.WordTrace tailWord_3112259 prefixEnd_3112259 1598084788281444006049487 := by
  unfold tailWord_3112259
  simp only [CollatzResearch.WordTrace]
  refine ⟨113513411231824649364923831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75675607487883099576615887 113513411231824649364923831)
  ·
    refine ⟨170270116847736974047385747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113513411231824649364923831 170270116847736974047385747)
    ·
      refine ⟨255405175271605461071078621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170270116847736974047385747 255405175271605461071078621)
      ·
        refine ⟨95776940726852047901654483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255405175271605461071078621 95776940726852047901654483)
        ·
          refine ⟨143665411090278071852481725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95776940726852047901654483 143665411090278071852481725)
          ·
            refine ⟨53874529158854276944680647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143665411090278071852481725 53874529158854276944680647)
            ·
              refine ⟨80811793738281415417020971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53874529158854276944680647 80811793738281415417020971)
              ·
                refine ⟨121217690607422123125531457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80811793738281415417020971 121217690607422123125531457)
                ·
                  refine ⟨90913267955566592344148593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121217690607422123125531457 90913267955566592344148593)
                  ·
                    refine ⟨68184950966674944258111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90913267955566592344148593 68184950966674944258111445)
                    ·
                      refine ⟨1598084788281444006049487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68184950966674944258111445 1598084788281444006049487)
                      ·
                        rfl

theorem cell23_3112259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_3112259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112259 prefixEnd_3112259 := by exact prefixLift 3112259
  have htrace : WordTrace (prefixWord ++ tailWord_3112259) baseStart_3112259 baseEnd_3112259 := by
    simpa [prefixWord, tailWord_3112259, baseEnd_3112259] using wordTrace_append hprefix tailTrace_3112259
  have hstable : (prefixWord ++ tailWord_3112259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112259).length < 2 ^ (prefixWord ++ tailWord_3112259).sum := by decide
  have hdescent : baseEnd_3112259 < baseStart_3112259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112270 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3112270 : Nat := 118140960795 + 3112270 * 2 ^ 59
def prefixEnd_3112270 : Nat := 4983230072969 + 3 ^ 40 * 3112270 * 2
def baseEnd_3112270 : Nat := 532696812189547821003979

theorem tailTrace_3112270 : CollatzResearch.WordTrace tailWord_3112270 prefixEnd_3112270 532696812189547821003979 := by
  unfold tailWord_3112270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14189226554348099780446783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75675874956523198829049509 14189226554348099780446783)
  ·
    refine ⟨21283839831522149670670175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14189226554348099780446783 21283839831522149670670175)
    ·
      refine ⟨31925759747283224506005263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21283839831522149670670175 31925759747283224506005263)
      ·
        refine ⟨47888639620924836759007895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31925759747283224506005263 47888639620924836759007895)
        ·
          refine ⟨71832959431387255138511843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47888639620924836759007895 71832959431387255138511843)
          ·
            refine ⟨107749439147080882707767765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71832959431387255138511843 107749439147080882707767765)
            ·
              refine ⟨2525377480009708188463307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107749439147080882707767765 2525377480009708188463307)
              ·
                refine ⟨3788066220014562282694961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525377480009708188463307 3788066220014562282694961)
                ·
                  refine ⟨2841049665010921712021221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3788066220014562282694961 2841049665010921712021221)
                  ·
                    refine ⟨532696812189547821003979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2841049665010921712021221 532696812189547821003979)
                    ·
                      rfl

theorem cell23_3112270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3112270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112270 prefixEnd_3112270 := by exact prefixLift 3112270
  have htrace : WordTrace (prefixWord ++ tailWord_3112270) baseStart_3112270 baseEnd_3112270 := by
    simpa [prefixWord, tailWord_3112270, baseEnd_3112270] using wordTrace_append hprefix tailTrace_3112270
  have hstable : (prefixWord ++ tailWord_3112270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112270).length < 2 ^ (prefixWord ++ tailWord_3112270).sum := by decide
  have hdescent : baseEnd_3112270 < baseStart_3112270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112293 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3112293 : Nat := 118140960795 + 3112293 * 2 ^ 59
def prefixEnd_3112293 : Nat := 4983230072969 + 3 ^ 40 * 3112293 * 2
def baseEnd_3112293 : Nat := 1598102246623696873024331

theorem tailTrace_3112293 : CollatzResearch.WordTrace tailWord_3112293 prefixEnd_3112293 1598102246623696873024331 := by
  unfold tailWord_3112293
  simp only [CollatzResearch.WordTrace]
  refine ⟨113514651313701473171661533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75676434209134315447774355 113514651313701473171661533)
  ·
    refine ⟨42567994242638052439373075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113514651313701473171661533 42567994242638052439373075)
    ·
      refine ⟨63851991363957078659059613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42567994242638052439373075 63851991363957078659059613)
      ·
        refine ⟨23944496761483904497147355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63851991363957078659059613 23944496761483904497147355)
        ·
          refine ⟨35916745142225856745721033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23944496761483904497147355 35916745142225856745721033)
          ·
            refine ⟨26937558856669392559290775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35916745142225856745721033 26937558856669392559290775)
            ·
              refine ⟨40406338285004088838936163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26937558856669392559290775 40406338285004088838936163)
              ·
                refine ⟨60609507427506133258404245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40406338285004088838936163 60609507427506133258404245)
                ·
                  refine ⟨2841070660664349996487699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60609507427506133258404245 2841070660664349996487699)
                  ·
                    refine ⟨4261605990996524994731549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2841070660664349996487699 4261605990996524994731549)
                    ·
                      refine ⟨1598102246623696873024331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261605990996524994731549 1598102246623696873024331)
                      ·
                        rfl

theorem cell23_3112293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3112293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112293 prefixEnd_3112293 := by exact prefixLift 3112293
  have htrace : WordTrace (prefixWord ++ tailWord_3112293) baseStart_3112293 baseEnd_3112293 := by
    simpa [prefixWord, tailWord_3112293, baseEnd_3112293] using wordTrace_append hprefix tailTrace_3112293
  have hstable : (prefixWord ++ tailWord_3112293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112293).length < 2 ^ (prefixWord ++ tailWord_3112293).sum := by decide
  have hdescent : baseEnd_3112293 < baseStart_3112293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112306 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3112306 : Nat := 118140960795 + 3112306 * 2 ^ 59
def prefixEnd_3112306 : Nat := 4983230072969 + 3 ^ 40 * 3112306 * 2
def baseEnd_3112306 : Nat := 1598108921872205322161771

theorem tailTrace_3112306 : CollatzResearch.WordTrace tailWord_3112306 prefixEnd_3112306 1598108921872205322161771 := by
  unfold tailWord_3112306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378781365663594097971193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75676750308436250927923181 28378781365663594097971193)
  ·
    refine ⟨21284086024247695573478395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28378781365663594097971193 21284086024247695573478395)
    ·
      refine ⟨31926129036371543360217593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21284086024247695573478395 31926129036371543360217593)
      ·
        refine ⟨23944596777278657520163195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31926129036371543360217593 23944596777278657520163195)
        ·
          refine ⟨35916895165917986280244793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23944596777278657520163195 35916895165917986280244793)
          ·
            refine ⟨26937671374438489710183595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35916895165917986280244793 26937671374438489710183595)
            ·
              refine ⟨40406507061657734565275393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26937671374438489710183595 40406507061657734565275393)
              ·
                refine ⟨30304880296243300923956545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40406507061657734565275393 30304880296243300923956545)
                ·
                  refine ⟨22728660222182475692967409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30304880296243300923956545 22728660222182475692967409)
                  ·
                    refine ⟨17046495166636856769725557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22728660222182475692967409 17046495166636856769725557)
                    ·
                      refine ⟨1598108921872205322161771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17046495166636856769725557 1598108921872205322161771)
                      ·
                        rfl

theorem cell23_3112306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3112306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112306 prefixEnd_3112306 := by exact prefixLift 3112306
  have htrace : WordTrace (prefixWord ++ tailWord_3112306) baseStart_3112306 baseEnd_3112306 := by
    simpa [prefixWord, tailWord_3112306, baseEnd_3112306] using wordTrace_append hprefix tailTrace_3112306
  have hstable : (prefixWord ++ tailWord_3112306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112306).length < 2 ^ (prefixWord ++ tailWord_3112306).sum := by decide
  have hdescent : baseEnd_3112306 < baseStart_3112306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112316 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3112316 : Nat := 118140960795 + 3112316 * 2 ^ 59
def prefixEnd_3112316 : Nat := 4983230072969 + 3 ^ 40 * 3112316 * 2
def baseEnd_3112316 : Nat := 1598114056678750283036725

theorem tailTrace_3112316 : CollatzResearch.WordTrace tailWord_3112316 prefixEnd_3112316 1598114056678750283036725 := by
  unfold tailWord_3112316
  simp only [CollatzResearch.WordTrace]
  refine ⟨56757745096309074049874401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75676993461745432066499201 56757745096309074049874401)
  ·
    refine ⟨42568308822231805537405801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56757745096309074049874401 42568308822231805537405801)
    ·
      refine ⟨31926231616673854153054351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42568308822231805537405801 31926231616673854153054351)
      ·
        refine ⟨47889347425010781229581527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31926231616673854153054351 47889347425010781229581527)
        ·
          refine ⟨71834021137516171844372291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47889347425010781229581527 71834021137516171844372291)
          ·
            refine ⟨107751031706274257766558437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71834021137516171844372291 107751031706274257766558437)
            ·
              refine ⟨20203318444926423331229707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107751031706274257766558437 20203318444926423331229707)
              ·
                refine ⟨30304977667389634996844561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20203318444926423331229707 30304977667389634996844561)
                ·
                  refine ⟨22728733250542226247633421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30304977667389634996844561 22728733250542226247633421)
                  ·
                    refine ⟨8523274968953334842862533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22728733250542226247633421 8523274968953334842862533)
                    ·
                      refine ⟨1598114056678750283036725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8523274968953334842862533 1598114056678750283036725)
                      ·
                        rfl

theorem cell23_3112316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3112316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112316 prefixEnd_3112316 := by exact prefixLift 3112316
  have htrace : WordTrace (prefixWord ++ tailWord_3112316) baseStart_3112316 baseEnd_3112316 := by
    simpa [prefixWord, tailWord_3112316, baseEnd_3112316] using wordTrace_append hprefix tailTrace_3112316
  have hstable : (prefixWord ++ tailWord_3112316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112316).length < 2 ^ (prefixWord ++ tailWord_3112316).sum := by decide
  have hdescent : baseEnd_3112316 < baseStart_3112316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112327 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_3112327 : Nat := 118140960795 + 3112327 * 2 ^ 59
def prefixEnd_3112327 : Nat := 4983230072969 + 3 ^ 40 * 3112327 * 2
def baseEnd_3112327 : Nat := 1598119704965949739999175

theorem tailTrace_3112327 : CollatzResearch.WordTrace tailWord_3112327 prefixEnd_3112327 1598119704965949739999175 := by
  unfold tailWord_3112327
  simp only [CollatzResearch.WordTrace]
  refine ⟨113515891395578296978399235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75677260930385531318932823 113515891395578296978399235)
  ·
    refine ⟨170273837093367445467598853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113515891395578296978399235 170273837093367445467598853)
    ·
      refine ⟨31926344455006396025174785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170273837093367445467598853 31926344455006396025174785)
      ·
        refine ⟨23944758341254797018881089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31926344455006396025174785 23944758341254797018881089)
        ·
          refine ⟨17958568755941097764160817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23944758341254797018881089 17958568755941097764160817)
          ·
            refine ⟨13468926566955823323120613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17958568755941097764160817 13468926566955823323120613)
            ·
              refine ⟨2525423731304216873085115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13468926566955823323120613 2525423731304216873085115)
              ·
                refine ⟨3788135596956325309627673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525423731304216873085115 3788135596956325309627673)
                ·
                  refine ⟨2841101697717243982220755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3788135596956325309627673 2841101697717243982220755)
                  ·
                    refine ⟨4261652546575865973331133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2841101697717243982220755 4261652546575865973331133)
                    ·
                      refine ⟨1598119704965949739999175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261652546575865973331133 1598119704965949739999175)
                      ·
                        rfl

theorem cell23_3112327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_3112327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112327 prefixEnd_3112327 := by exact prefixLift 3112327
  have htrace : WordTrace (prefixWord ++ tailWord_3112327) baseStart_3112327 baseEnd_3112327 := by
    simpa [prefixWord, tailWord_3112327, baseEnd_3112327] using wordTrace_append hprefix tailTrace_3112327
  have hstable : (prefixWord ++ tailWord_3112327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112327).length < 2 ^ (prefixWord ++ tailWord_3112327).sum := by decide
  have hdescent : baseEnd_3112327 < baseStart_3112327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112354 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_3112354 : Nat := 118140960795 + 3112354 * 2 ^ 59
def prefixEnd_3112354 : Nat := 4983230072969 + 3 ^ 40 * 3112354 * 2
def baseEnd_3112354 : Nat := 1598133568943621134361551

theorem tailTrace_3112354 : CollatzResearch.WordTrace tailWord_3112354 prefixEnd_3112354 1598133568943621134361551 := by
  unfold tailWord_3112354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28379219041620120147408029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75677917444320320393088077 28379219041620120147408029)
  ·
    refine ⟨10642207140607545055278011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28379219041620120147408029 10642207140607545055278011)
    ·
      refine ⟨15963310710911317582917017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10642207140607545055278011 15963310710911317582917017)
      ·
        refine ⟨11972483033183488187187763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15963310710911317582917017 11972483033183488187187763)
        ·
          refine ⟨17958724549775232280781645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11972483033183488187187763 17958724549775232280781645)
          ·
            refine ⟨6734521706165712105293117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17958724549775232280781645 6734521706165712105293117)
            ·
              refine ⟨2525445639812142039484919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6734521706165712105293117 2525445639812142039484919)
              ·
                refine ⟨3788168459718213059227379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525445639812142039484919 3788168459718213059227379)
                ·
                  refine ⟨5682252689577319588841069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788168459718213059227379 5682252689577319588841069)
                  ·
                    refine ⟨2130844758591494845815401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5682252689577319588841069 2130844758591494845815401)
                    ·
                      refine ⟨1598133568943621134361551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130844758591494845815401 1598133568943621134361551)
                      ·
                        rfl

theorem cell23_3112354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_3112354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112354 prefixEnd_3112354 := by exact prefixLift 3112354
  have htrace : WordTrace (prefixWord ++ tailWord_3112354) baseStart_3112354 baseEnd_3112354 := by
    simpa [prefixWord, tailWord_3112354, baseEnd_3112354] using wordTrace_append hprefix tailTrace_3112354
  have hstable : (prefixWord ++ tailWord_3112354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112354).length < 2 ^ (prefixWord ++ tailWord_3112354).sum := by decide
  have hdescent : baseEnd_3112354 < baseStart_3112354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112380 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3112380 : Nat := 118140960795 + 3112380 * 2 ^ 59
def prefixEnd_3112380 : Nat := 4983230072969 + 3 ^ 40 * 3112380 * 2
def baseEnd_3112380 : Nat := 1598146919440638032636431

theorem tailTrace_3112380 : CollatzResearch.WordTrace tailWord_3112380 prefixEnd_3112380 1598146919440638032636431 := by
  unfold tailWord_3112380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56758912232193143515039297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75678549642924191353385729 56758912232193143515039297)
  ·
    refine ⟨42569184174144857636279473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56758912232193143515039297 42569184174144857636279473)
    ·
      refine ⟨31926888130608643227209605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42569184174144857636279473 31926888130608643227209605)
      ·
        refine ⟨5986291524489120605101801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31926888130608643227209605 5986291524489120605101801)
        ·
          refine ⟨4489718643366840453826351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5986291524489120605101801 4489718643366840453826351)
          ·
            refine ⟨6734577965050260680739527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489718643366840453826351 6734577965050260680739527)
            ·
              refine ⟨10101866947575391021109291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734577965050260680739527 10101866947575391021109291)
              ·
                refine ⟨15152800421363086531663937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10101866947575391021109291 15152800421363086531663937)
                ·
                  refine ⟨11364600316022314898747953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15152800421363086531663937 11364600316022314898747953)
                  ·
                    refine ⟨8523450237016736174060965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11364600316022314898747953 8523450237016736174060965)
                    ·
                      refine ⟨1598146919440638032636431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8523450237016736174060965 1598146919440638032636431)
                      ·
                        rfl

theorem cell23_3112380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3112380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112380 prefixEnd_3112380 := by exact prefixLift 3112380
  have htrace : WordTrace (prefixWord ++ tailWord_3112380) baseStart_3112380 baseEnd_3112380 := by
    simpa [prefixWord, tailWord_3112380, baseEnd_3112380] using wordTrace_append hprefix tailTrace_3112380
  have hstable : (prefixWord ++ tailWord_3112380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112380).length < 2 ^ (prefixWord ++ tailWord_3112380).sum := by decide
  have hdescent : baseEnd_3112380 < baseStart_3112380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112393 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 5, 2]
def baseStart_3112393 : Nat := 118140960795 + 3112393 * 2 ^ 59
def prefixEnd_3112393 : Nat := 4983230072969 + 3 ^ 40 * 3112393 * 2
def baseEnd_3112393 : Nat := 1598153594689146481773871

theorem tailTrace_3112393 : CollatzResearch.WordTrace tailWord_3112393 prefixEnd_3112393 1598153594689146481773871 := by
  unfold tailWord_3112393
  simp only [CollatzResearch.WordTrace]
  refine ⟨113518298613339190250301833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75678865742226126833534555 113518298613339190250301833)
  ·
    refine ⟨85138723960004392687726375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113518298613339190250301833 85138723960004392687726375)
    ·
      refine ⟨127708085940006589031589563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85138723960004392687726375 127708085940006589031589563)
      ·
        refine ⟨191562128910009883547384345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127708085940006589031589563 191562128910009883547384345)
        ·
          refine ⟨143671596682507412660538259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191562128910009883547384345 143671596682507412660538259)
          ·
            refine ⟨215507395023761118990807389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143671596682507412660538259 215507395023761118990807389)
            ·
              refine ⟨80815273133910419621552771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215507395023761118990807389 80815273133910419621552771)
              ·
                refine ⟨121222909700865629432329157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80815273133910419621552771 121222909700865629432329157)
                ·
                  refine ⟨22729295568912305518561717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121222909700865629432329157 22729295568912305518561717)
                  ·
                    refine ⟨2130871459585528642365161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22729295568912305518561717 2130871459585528642365161)
                    ·
                      refine ⟨1598153594689146481773871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130871459585528642365161 1598153594689146481773871)
                      ·
                        rfl

theorem cell23_3112393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5, 2].length) (baseStart_3112393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112393 prefixEnd_3112393 := by exact prefixLift 3112393
  have htrace : WordTrace (prefixWord ++ tailWord_3112393) baseStart_3112393 baseEnd_3112393 := by
    simpa [prefixWord, tailWord_3112393, baseEnd_3112393] using wordTrace_append hprefix tailTrace_3112393
  have hstable : (prefixWord ++ tailWord_3112393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112393).length < 2 ^ (prefixWord ++ tailWord_3112393).sum := by decide
  have hdescent : baseEnd_3112393 < baseStart_3112393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112440 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_3112440 : Nat := 118140960795 + 3112440 * 2 ^ 59
def prefixEnd_3112440 : Nat := 4983230072969 + 3 ^ 40 * 3112440 * 2
def baseEnd_3112440 : Nat := 1598177728279907797886155

theorem tailTrace_3112440 : CollatzResearch.WordTrace tailWord_3112440 prefixEnd_3112440 1598177728279907797886155 := by
  unfold tailWord_3112440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56760006422084458638631387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75680008562779278184841849 56760006422084458638631387)
  ·
    refine ⟨85140009633126687957947081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56760006422084458638631387 85140009633126687957947081)
    ·
      refine ⟨63855007224845015968460311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85140009633126687957947081 63855007224845015968460311)
      ·
        refine ⟨95782510837267523952690467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63855007224845015968460311 95782510837267523952690467)
        ·
          refine ⟨143673766255901285929035701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95782510837267523952690467 143673766255901285929035701)
          ·
            refine ⟨13469415586490745555847097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143673766255901285929035701 13469415586490745555847097)
            ·
              refine ⟨10102061689868059166885323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13469415586490745555847097 10102061689868059166885323)
              ·
                refine ⟨15153092534802088750327985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10102061689868059166885323 15153092534802088750327985)
                ·
                  refine ⟨11364819401101566562745989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15153092534802088750327985 11364819401101566562745989)
                  ·
                    refine ⟨2130903637706543730514873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11364819401101566562745989 2130903637706543730514873)
                    ·
                      refine ⟨1598177728279907797886155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130903637706543730514873 1598177728279907797886155)
                      ·
                        rfl

theorem cell23_3112440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_3112440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112440 prefixEnd_3112440 := by exact prefixLift 3112440
  have htrace : WordTrace (prefixWord ++ tailWord_3112440) baseStart_3112440 baseEnd_3112440 := by
    simpa [prefixWord, tailWord_3112440, baseEnd_3112440] using wordTrace_append hprefix tailTrace_3112440
  have hstable : (prefixWord ++ tailWord_3112440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112440).length < 2 ^ (prefixWord ++ tailWord_3112440).sum := by decide
  have hdescent : baseEnd_3112440 < baseStart_3112440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112443 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3]
def baseStart_3112443 : Nat := 118140960795 + 3112443 * 2 ^ 59
def prefixEnd_3112443 : Nat := 4983230072969 + 3 ^ 40 * 3112443 * 2
def baseEnd_3112443 : Nat := 1598179268721871286148641

theorem tailTrace_3112443 : CollatzResearch.WordTrace tailWord_3112443 prefixEnd_3112443 1598179268721871286148641 := by
  unfold tailWord_3112443
  simp only [CollatzResearch.WordTrace]
  refine ⟨113520122263158048789621983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75680081508772032526414655 113520122263158048789621983)
  ·
    refine ⟨170280183394737073184432975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113520122263158048789621983 170280183394737073184432975)
    ·
      refine ⟨255420275092105609776649463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170280183394737073184432975 255420275092105609776649463)
      ·
        refine ⟨383130412638158414664974195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255420275092105609776649463 383130412638158414664974195)
        ·
          refine ⟨574695618957237621997461293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383130412638158414664974195 574695618957237621997461293)
          ·
            refine ⟨215510857108964108249047985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574695618957237621997461293 215510857108964108249047985)
            ·
              refine ⟨161633142831723081186785989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215510857108964108249047985 161633142831723081186785989)
              ·
                refine ⟨30306214280948077722522373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161633142831723081186785989 30306214280948077722522373)
                ·
                  refine ⟨5682415177677764572972945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30306214280948077722522373 5682415177677764572972945)
                  ·
                    refine ⟨4261811383258323429729709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5682415177677764572972945 4261811383258323429729709)
                    ·
                      refine ⟨1598179268721871286148641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4261811383258323429729709 1598179268721871286148641)
                      ·
                        rfl

theorem cell23_3112443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3].length) (baseStart_3112443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112443 prefixEnd_3112443 := by exact prefixLift 3112443
  have htrace : WordTrace (prefixWord ++ tailWord_3112443) baseStart_3112443 baseEnd_3112443 := by
    simpa [prefixWord, tailWord_3112443, baseEnd_3112443] using wordTrace_append hprefix tailTrace_3112443
  have hstable : (prefixWord ++ tailWord_3112443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112443).length < 2 ^ (prefixWord ++ tailWord_3112443).sum := by decide
  have hdescent : baseEnd_3112443 < baseStart_3112443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112467 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 1, 4]
def baseStart_3112467 : Nat := 118140960795 + 3112467 * 2 ^ 59
def prefixEnd_3112467 : Nat := 4983230072969 + 3 ^ 40 * 3112467 * 2
def baseEnd_3112467 : Nat := 532730530752526397416177

theorem tailTrace_3112467 : CollatzResearch.WordTrace tailWord_3112467 prefixEnd_3112467 532730530752526397416177 := by
  unfold tailWord_3112467
  simp only [CollatzResearch.WordTrace]
  refine ⟨113520997615071100888495655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75680665076714067258997103 113520997615071100888495655)
  ·
    refine ⟨170281496422606651332743483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113520997615071100888495655 170281496422606651332743483)
    ·
      refine ⟨255422244633909976999115225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170281496422606651332743483 255422244633909976999115225)
      ·
        refine ⟨191566683475432482749336419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255422244633909976999115225 191566683475432482749336419)
        ·
          refine ⟨287350025213148724124004629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191566683475432482749336419 287350025213148724124004629)
          ·
            refine ⟨13469532431866346443312717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287350025213148724124004629 13469532431866346443312717)
            ·
              refine ⟨5051074661949879916242269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13469532431866346443312717 5051074661949879916242269)
              ·
                refine ⟨1894152998231204968590851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5051074661949879916242269 1894152998231204968590851)
                ·
                  refine ⟨2841229497346807452886277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894152998231204968590851 2841229497346807452886277)
                  ·
                    refine ⟨532730530752526397416177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2841229497346807452886277 532730530752526397416177)
                    ·
                      rfl

theorem cell23_3112467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 4].length) (baseStart_3112467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112467 prefixEnd_3112467 := by exact prefixLift 3112467
  have htrace : WordTrace (prefixWord ++ tailWord_3112467) baseStart_3112467 baseEnd_3112467 := by
    simpa [prefixWord, tailWord_3112467, baseEnd_3112467] using wordTrace_append hprefix tailTrace_3112467
  have hstable : (prefixWord ++ tailWord_3112467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112467).length < 2 ^ (prefixWord ++ tailWord_3112467).sum := by decide
  have hdescent : baseEnd_3112467 < baseStart_3112467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112517 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_3112517 : Nat := 118140960795 + 3112517 * 2 ^ 59
def prefixEnd_3112517 : Nat := 4983230072969 + 3 ^ 40 * 3112517 * 2
def baseEnd_3112517 : Nat := 1598217266290303996623301

theorem tailTrace_3112517 : CollatzResearch.WordTrace tailWord_3112517 prefixEnd_3112517 1598217266290303996623301 := by
  unfold tailWord_3112517
  simp only [CollatzResearch.WordTrace]
  refine ⟨113522821264889959427815805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75681880843259972951877203 113522821264889959427815805)
  ·
    refine ⟨42571057974333734785430927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113522821264889959427815805 42571057974333734785430927)
    ·
      refine ⟨63856586961500602178146391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42571057974333734785430927 63856586961500602178146391)
      ·
        refine ⟨95784880442250903267219587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63856586961500602178146391 95784880442250903267219587)
        ·
          refine ⟨143677320663376354900829381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95784880442250903267219587 143677320663376354900829381)
          ·
            refine ⟨26939497624383066543905509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143677320663376354900829381 26939497624383066543905509)
            ·
              refine ⟨5051155804571824976982283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26939497624383066543905509 5051155804571824976982283)
              ·
                refine ⟨7576733706857737465473425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051155804571824976982283 7576733706857737465473425)
                ·
                  refine ⟨5682550280143303099105069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7576733706857737465473425 5682550280143303099105069)
                  ·
                    refine ⟨2130956355053738662164401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5682550280143303099105069 2130956355053738662164401)
                    ·
                      refine ⟨1598217266290303996623301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2130956355053738662164401 1598217266290303996623301)
                      ·
                        rfl

theorem cell23_3112517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_3112517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112517 prefixEnd_3112517 := by exact prefixLift 3112517
  have htrace : WordTrace (prefixWord ++ tailWord_3112517) baseStart_3112517 baseEnd_3112517 := by
    simpa [prefixWord, tailWord_3112517, baseEnd_3112517] using wordTrace_append hprefix tailTrace_3112517
  have hstable : (prefixWord ++ tailWord_3112517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112517).length < 2 ^ (prefixWord ++ tailWord_3112517).sum := by decide
  have hdescent : baseEnd_3112517 < baseStart_3112517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112553 : List Nat := [1, 2, 1, 1, 1, 4, 5, 8]
def baseStart_3112553 : Nat := 118140960795 + 3112553 * 2 ^ 59
def prefixEnd_3112553 : Nat := 4983230072969 + 3 ^ 40 * 3112553 * 2
def baseEnd_3112553 : Nat := 59193916725698735399005

theorem tailTrace_3112553 : CollatzResearch.WordTrace tailWord_3112553 prefixEnd_3112553 59193916725698735399005 := by
  unfold tailWord_3112553
  simp only [CollatzResearch.WordTrace]
  refine ⟨113524134292759537576126313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75682756195173025050750875 113524134292759537576126313)
  ·
    refine ⟨85143100719569653182094735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113524134292759537576126313 85143100719569653182094735)
    ·
      refine ⟨127714651079354479773142103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85143100719569653182094735 127714651079354479773142103)
      ·
        refine ⟨191571976619031719659713155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127714651079354479773142103 191571976619031719659713155)
        ·
          refine ⟨287357964928547579489569733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191571976619031719659713155 287357964928547579489569733)
          ·
            refine ⟨53879618424102671154294325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287357964928547579489569733 53879618424102671154294325)
            ·
              refine ⟨5051214227259625420715093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53879618424102671154294325 5051214227259625420715093)
              ·
                refine ⟨59193916725698735399005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5051214227259625420715093 59193916725698735399005)
                ·
                  rfl

theorem cell23_3112553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 8].length) (baseStart_3112553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112553 prefixEnd_3112553 := by exact prefixLift 3112553
  have htrace : WordTrace (prefixWord ++ tailWord_3112553) baseStart_3112553 baseEnd_3112553 := by
    simpa [prefixWord, tailWord_3112553, baseEnd_3112553] using wordTrace_append hprefix tailTrace_3112553
  have hstable : (prefixWord ++ tailWord_3112553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112553).length < 2 ^ (prefixWord ++ tailWord_3112553).sum := by decide
  have hdescent : baseEnd_3112553 < baseStart_3112553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112557 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3112557 : Nat := 118140960795 + 3112557 * 2 ^ 59
def prefixEnd_3112557 : Nat := 4983230072969 + 3 ^ 40 * 3112557 * 2
def baseEnd_3112557 : Nat := 532745935172161280041039

theorem tailTrace_3112557 : CollatzResearch.WordTrace tailWord_3112557 prefixEnd_3112557 532745935172161280041039 := by
  unfold tailWord_3112557
  simp only [CollatzResearch.WordTrace]
  refine ⟨113524280184745046259271925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75682853456496697506181283 113524280184745046259271925)
  ·
    refine ⟨10642901267319848086806743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113524280184745046259271925 10642901267319848086806743)
    ·
      refine ⟨15964351900979772130210115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10642901267319848086806743 15964351900979772130210115)
      ·
        refine ⟨23946527851469658195315173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15964351900979772130210115 23946527851469658195315173)
        ·
          refine ⟨4489973972150560911621595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23946527851469658195315173 4489973972150560911621595)
          ·
            refine ⟨6734960958225841367432393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489973972150560911621595 6734960958225841367432393)
            ·
              refine ⟨5051220718669381025574295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6734960958225841367432393 5051220718669381025574295)
              ·
                refine ⟨7576831078004071538361443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051220718669381025574295 7576831078004071538361443)
                ·
                  refine ⟨11365246617006107307542165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576831078004071538361443 11365246617006107307542165)
                  ·
                    refine ⟨532745935172161280041039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11365246617006107307542165 532745935172161280041039)
                    ·
                      rfl

theorem cell23_3112557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3112557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112557 prefixEnd_3112557 := by exact prefixLift 3112557
  have htrace : WordTrace (prefixWord ++ tailWord_3112557) baseStart_3112557 baseEnd_3112557 := by
    simpa [prefixWord, tailWord_3112557, baseEnd_3112557] using wordTrace_append hprefix tailTrace_3112557
  have hstable : (prefixWord ++ tailWord_3112557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112557).length < 2 ^ (prefixWord ++ tailWord_3112557).sum := by decide
  have hdescent : baseEnd_3112557 < baseStart_3112557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112560 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_3112560 : Nat := 118140960795 + 3112560 * 2 ^ 59
def prefixEnd_3112560 : Nat := 4983230072969 + 3 ^ 40 * 3112560 * 2
def baseEnd_3112560 : Nat := 1598239345958447328385603

theorem tailTrace_3112560 : CollatzResearch.WordTrace tailWord_3112560 prefixEnd_3112560 1598239345958447328385603 := by
  unfold tailWord_3112560
  simp only [CollatzResearch.WordTrace]
  refine ⟨56762194801867088885815567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75682926402489451847754089 56762194801867088885815567)
  ·
    refine ⟨85143292202800633328723351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56762194801867088885815567 85143292202800633328723351)
    ·
      refine ⟨127714938304200949993085027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85143292202800633328723351 127714938304200949993085027)
      ·
        refine ⟨191572407456301424989627541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127714938304200949993085027 191572407456301424989627541)
        ·
          refine ⟨8979956599514129296388791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191572407456301424989627541 8979956599514129296388791)
          ·
            refine ⟨13469934899271193944583187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8979956599514129296388791 13469934899271193944583187)
            ·
              refine ⟨20204902348906790916874781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469934899271193944583187 20204902348906790916874781)
              ·
                refine ⟨7576838380840046593828043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20204902348906790916874781 7576838380840046593828043)
                ·
                  refine ⟨11365257571260069890742065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576838380840046593828043 11365257571260069890742065)
                  ·
                    refine ⟨8523943178445052418056549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11365257571260069890742065 8523943178445052418056549)
                    ·
                      refine ⟨1598239345958447328385603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8523943178445052418056549 1598239345958447328385603)
                      ·
                        rfl

theorem cell23_3112560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_3112560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112560 prefixEnd_3112560 := by exact prefixLift 3112560
  have htrace : WordTrace (prefixWord ++ tailWord_3112560) baseStart_3112560 baseEnd_3112560 := by
    simpa [prefixWord, tailWord_3112560, baseEnd_3112560] using wordTrace_append hprefix tailTrace_3112560
  have hstable : (prefixWord ++ tailWord_3112560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112560).length < 2 ^ (prefixWord ++ tailWord_3112560).sum := by decide
  have hdescent : baseEnd_3112560 < baseStart_3112560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112581 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 1, 2, 2]
def baseStart_3112581 : Nat := 118140960795 + 3112581 * 2 ^ 59
def prefixEnd_3112581 : Nat := 4983230072969 + 3 ^ 40 * 3112581 * 2
def baseEnd_3112581 : Nat := 1598250129052191746223007

theorem tailTrace_3112581 : CollatzResearch.WordTrace tailWord_3112581 prefixEnd_3112581 1598250129052191746223007 := by
  unfold tailWord_3112581
  simp only [CollatzResearch.WordTrace]
  refine ⟨113525155536658098358145597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75683437024438732238763731 113525155536658098358145597)
  ·
    refine ⟨42571933326246786884304599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113525155536658098358145597 42571933326246786884304599)
    ·
      refine ⟨63857899989370180326456899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42571933326246786884304599 63857899989370180326456899)
      ·
        refine ⟨95786849984055270489685349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63857899989370180326456899 95786849984055270489685349)
        ·
          refine ⟨17960034372010363216816003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95786849984055270489685349 17960034372010363216816003)
          ·
            refine ⟨26940051558015544825224005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960034372010363216816003 26940051558015544825224005)
            ·
              refine ⟨5051259667127914654729501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26940051558015544825224005 5051259667127914654729501)
              ·
                refine ⟨1894222375172967995523563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5051259667127914654729501 1894222375172967995523563)
                ·
                  refine ⟨2841333562759451993285345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894222375172967995523563 2841333562759451993285345)
                  ·
                    refine ⟨2131000172069588994964009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2841333562759451993285345 2131000172069588994964009)
                    ·
                      refine ⟨1598250129052191746223007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131000172069588994964009 1598250129052191746223007)
                      ·
                        rfl

theorem cell23_3112581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_3112581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112581 prefixEnd_3112581 := by exact prefixLift 3112581
  have htrace : WordTrace (prefixWord ++ tailWord_3112581) baseStart_3112581 baseEnd_3112581 := by
    simpa [prefixWord, tailWord_3112581, baseEnd_3112581] using wordTrace_append hprefix tailTrace_3112581
  have hstable : (prefixWord ++ tailWord_3112581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112581).length < 2 ^ (prefixWord ++ tailWord_3112581).sum := by decide
  have hdescent : baseEnd_3112581 < baseStart_3112581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112593 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_3112593 : Nat := 118140960795 + 3112593 * 2 ^ 59
def prefixEnd_3112593 : Nat := 4983230072969 + 3 ^ 40 * 3112593 * 2
def baseEnd_3112593 : Nat := 1598256290820045699272951

theorem tailTrace_3112593 : CollatzResearch.WordTrace tailWord_3112593 prefixEnd_3112593 1598256290820045699272951 := by
  unfold tailWord_3112593
  simp only [CollatzResearch.WordTrace]
  refine ⟨113525593212614624407582433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75683728808409749605054955 113525593212614624407582433)
  ·
    refine ⟨85144194909460968305686825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113525593212614624407582433 85144194909460968305686825)
    ·
      refine ⟨63858146182095726229265119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85144194909460968305686825 63858146182095726229265119)
      ·
        refine ⟨95787219273143589343897679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63858146182095726229265119 95787219273143589343897679)
        ·
          refine ⟨143680828909715384015846519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95787219273143589343897679 143680828909715384015846519)
          ·
            refine ⟨215521243364573076023769779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143680828909715384015846519 215521243364573076023769779)
            ·
              refine ⟨323281865046859614035654669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215521243364573076023769779 323281865046859614035654669)
              ·
                refine ⟨121230699392572355263370501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323281865046859614035654669 121230699392572355263370501)
                ·
                  refine ⟨22730756136107316611881969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121230699392572355263370501 22730756136107316611881969)
                  ·
                    refine ⟨17048067102080487458911477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22730756136107316611881969 17048067102080487458911477)
                    ·
                      refine ⟨1598256290820045699272951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17048067102080487458911477 1598256290820045699272951)
                      ·
                        rfl

theorem cell23_3112593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_3112593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112593 prefixEnd_3112593 := by exact prefixLift 3112593
  have htrace : WordTrace (prefixWord ++ tailWord_3112593) baseStart_3112593 baseEnd_3112593 := by
    simpa [prefixWord, tailWord_3112593, baseEnd_3112593] using wordTrace_append hprefix tailTrace_3112593
  have hstable : (prefixWord ++ tailWord_3112593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112593).length < 2 ^ (prefixWord ++ tailWord_3112593).sum := by decide
  have hdescent : baseEnd_3112593 < baseStart_3112593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112637 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_3112637 : Nat := 118140960795 + 3112637 * 2 ^ 59
def prefixEnd_3112637 : Nat := 4983230072969 + 3 ^ 40 * 3112637 * 2
def baseEnd_3112637 : Nat := 1598278883968843527122749

theorem tailTrace_3112637 : CollatzResearch.WordTrace tailWord_3112637 prefixEnd_3112637 1598278883968843527122749 := by
  unfold tailWord_3112637
  simp only [CollatzResearch.WordTrace]
  refine ⟨113527198024455219922184165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75684798682970146614789443 113527198024455219922184165)
  ·
    refine ⟨21286349629585353735409531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113527198024455219922184165 21286349629585353735409531)
    ·
      refine ⟨31929524444378030603114297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21286349629585353735409531 31929524444378030603114297)
      ·
        refine ⟨23947143333283522952335723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31929524444378030603114297 23947143333283522952335723)
        ·
          refine ⟨35920714999925284428503585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23947143333283522952335723 35920714999925284428503585)
          ·
            refine ⟨26940536249943963321377689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35920714999925284428503585 26940536249943963321377689)
            ·
              refine ⟨20205402187457972491033267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26940536249943963321377689 20205402187457972491033267)
              ·
                refine ⟨30308103281186958736549901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20205402187457972491033267 30308103281186958736549901)
                ·
                  refine ⟨11365538730445109526206213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30308103281186958736549901 11365538730445109526206213)
                  ·
                    refine ⟨2131038511958458036163665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11365538730445109526206213 2131038511958458036163665)
                    ·
                      refine ⟨1598278883968843527122749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131038511958458036163665 1598278883968843527122749)
                      ·
                        rfl

theorem cell23_3112637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_3112637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112637 prefixEnd_3112637 := by exact prefixLift 3112637
  have htrace : WordTrace (prefixWord ++ tailWord_3112637) baseStart_3112637 baseEnd_3112637 := by
    simpa [prefixWord, tailWord_3112637, baseEnd_3112637] using wordTrace_append hprefix tailTrace_3112637
  have hstable : (prefixWord ++ tailWord_3112637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112637).length < 2 ^ (prefixWord ++ tailWord_3112637).sum := by decide
  have hdescent : baseEnd_3112637 < baseStart_3112637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112640 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3112640 : Nat := 118140960795 + 3112640 * 2 ^ 59
def prefixEnd_3112640 : Nat := 4983230072969 + 3 ^ 40 * 3112640 * 2
def baseEnd_3112640 : Nat := 1598280424410807015385235

theorem tailTrace_3112640 : CollatzResearch.WordTrace tailWord_3112640 prefixEnd_3112640 1598280424410807015385235 := by
  unfold tailWord_3112640
  simp only [CollatzResearch.WordTrace]
  refine ⟨56763653721722175717271687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75684871628962900956362249 56763653721722175717271687)
  ·
    refine ⟨85145480582583263575907531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56763653721722175717271687 85145480582583263575907531)
    ·
      refine ⟨127718220873874895363861297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85145480582583263575907531 127718220873874895363861297)
      ·
        refine ⟨95788665655406171522895973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127718220873874895363861297 95788665655406171522895973)
        ·
          refine ⟨17960374810388657160542995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95788665655406171522895973 17960374810388657160542995)
          ·
            refine ⟨26940562215582985740814493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960374810388657160542995 26940562215582985740814493)
            ·
              refine ⟨10102710830843619652805435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26940562215582985740814493 10102710830843619652805435)
              ·
                refine ⟨15154066246265429479208153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10102710830843619652805435 15154066246265429479208153)
                ·
                  refine ⟨11365549684699072109406115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15154066246265429479208153 11365549684699072109406115)
                  ·
                    refine ⟨17048324527048608164109173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11365549684699072109406115 17048324527048608164109173)
                    ·
                      refine ⟨1598280424410807015385235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17048324527048608164109173 1598280424410807015385235)
                      ·
                        rfl

theorem cell23_3112640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3112640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112640 prefixEnd_3112640 := by exact prefixLift 3112640
  have htrace : WordTrace (prefixWord ++ tailWord_3112640) baseStart_3112640 baseEnd_3112640 := by
    simpa [prefixWord, tailWord_3112640, baseEnd_3112640] using wordTrace_append hprefix tailTrace_3112640
  have hstable : (prefixWord ++ tailWord_3112640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112640).length < 2 ^ (prefixWord ++ tailWord_3112640).sum := by decide
  have hdescent : baseEnd_3112640 < baseStart_3112640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112654 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_3112654 : Nat := 118140960795 + 3112654 * 2 ^ 59
def prefixEnd_3112654 : Nat := 4983230072969 + 3 ^ 40 * 3112654 * 2
def baseEnd_3112654 : Nat := 1598287613139969960610171

theorem tailTrace_3112654 : CollatzResearch.WordTrace tailWord_3112654 prefixEnd_3112654 1598287613139969960610171 := by
  unfold tailWord_3112654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190977258174203978194127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75685212043595754550368677 14190977258174203978194127)
  ·
    refine ⟨21286465887261305967291191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14190977258174203978194127 21286465887261305967291191)
    ·
      refine ⟨31929698830891958950936787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21286465887261305967291191 31929698830891958950936787)
      ·
        refine ⟨47894548246337938426405181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31929698830891958950936787 47894548246337938426405181)
        ·
          refine ⟨17960455592376726909901943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47894548246337938426405181 17960455592376726909901943)
          ·
            refine ⟨26940683388565090364852915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960455592376726909901943 26940683388565090364852915)
            ·
              refine ⟨40411025082847635547279373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26940683388565090364852915 40411025082847635547279373)
              ·
                refine ⟨15154134406067863330229765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40411025082847635547279373 15154134406067863330229765)
                ·
                  refine ⟨2841400201137724374418081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15154134406067863330229765 2841400201137724374418081)
                  ·
                    refine ⟨2131050150853293280813561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2841400201137724374418081 2131050150853293280813561)
                    ·
                      refine ⟨1598287613139969960610171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131050150853293280813561 1598287613139969960610171)
                      ·
                        rfl

theorem cell23_3112654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_3112654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112654 prefixEnd_3112654 := by exact prefixLift 3112654
  have htrace : WordTrace (prefixWord ++ tailWord_3112654) baseStart_3112654 baseEnd_3112654 := by
    simpa [prefixWord, tailWord_3112654, baseEnd_3112654] using wordTrace_append hprefix tailTrace_3112654
  have hstable : (prefixWord ++ tailWord_3112654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112654).length < 2 ^ (prefixWord ++ tailWord_3112654).sum := by decide
  have hdescent : baseEnd_3112654 < baseStart_3112654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112700 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3112700 : Nat := 118140960795 + 3112700 * 2 ^ 59
def prefixEnd_3112700 : Nat := 4983230072969 + 3 ^ 40 * 3112700 * 2
def baseEnd_3112700 : Nat := 1598311233250076780634959

theorem tailTrace_3112700 : CollatzResearch.WordTrace tailWord_3112700 prefixEnd_3112700 1598311233250076780634959 := by
  unfold tailWord_3112700
  simp only [CollatzResearch.WordTrace]
  refine ⟨56764747911613490840863777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75686330548817987787818369 56764747911613490840863777)
  ·
    refine ⟨42573560933710118130647833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56764747911613490840863777 42573560933710118130647833)
    ·
      refine ⟨31930170700282588597985875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42573560933710118130647833 31930170700282588597985875)
      ·
        refine ⟨47895256050423882896978813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31930170700282588597985875 47895256050423882896978813)
        ·
          refine ⟨17960721018908956086367055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47895256050423882896978813 17960721018908956086367055)
          ·
            refine ⟨26941081528363434129550583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960721018908956086367055 26941081528363434129550583)
            ·
              refine ⟨40411622292545151194325875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26941081528363434129550583 40411622292545151194325875)
              ·
                refine ⟨60617433438817726791488813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40411622292545151194325875 60617433438817726791488813)
                ·
                  refine ⟨22731537539556647546808305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60617433438817726791488813 22731537539556647546808305)
                  ·
                    refine ⟨17048653154667485660106229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22731537539556647546808305 17048653154667485660106229)
                    ·
                      refine ⟨1598311233250076780634959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17048653154667485660106229 1598311233250076780634959)
                      ·
                        rfl

theorem cell23_3112700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3112700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112700 prefixEnd_3112700 := by exact prefixLift 3112700
  have htrace : WordTrace (prefixWord ++ tailWord_3112700) baseStart_3112700 baseEnd_3112700 := by
    simpa [prefixWord, tailWord_3112700, baseEnd_3112700] using wordTrace_append hprefix tailTrace_3112700
  have hstable : (prefixWord ++ tailWord_3112700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112700).length < 2 ^ (prefixWord ++ tailWord_3112700).sum := by decide
  have hdescent : baseEnd_3112700 < baseStart_3112700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112737 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3112737 : Nat := 118140960795 + 3112737 * 2 ^ 59
def prefixEnd_3112737 : Nat := 4983230072969 + 3 ^ 40 * 3112737 * 2
def baseEnd_3112737 : Nat := 532776744011431045290763

theorem tailTrace_3112737 : CollatzResearch.WordTrace tailWord_3112737 prefixEnd_3112737 532776744011431045290763 := by
  unfold tailWord_3112737
  simp only [CollatzResearch.WordTrace]
  refine ⟨113530845324092937000824465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75687230216061958000549643 113530845324092937000824465)
  ·
    refine ⟨85148133993069702750618349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113530845324092937000824465 85148133993069702750618349)
    ·
      refine ⟨31930550247401138531481881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85148133993069702750618349 31930550247401138531481881)
      ·
        refine ⟨23947912685550853898611411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31930550247401138531481881 23947912685550853898611411)
        ·
          refine ⟨35921869028326280847917117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23947912685550853898611411 35921869028326280847917117)
          ·
            refine ⟨13470700885622355317968919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35921869028326280847917117 13470700885622355317968919)
            ·
              refine ⟨20206051328433532976953379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13470700885622355317968919 20206051328433532976953379)
              ·
                refine ⟨30309076992650299465430069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20206051328433532976953379 30309076992650299465430069)
                ·
                  refine ⟨2841475968060965574884069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30309076992650299465430069 2841475968060965574884069)
                  ·
                    refine ⟨532776744011431045290763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2841475968060965574884069 532776744011431045290763)
                    ·
                      rfl

theorem cell23_3112737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3112737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112737 prefixEnd_3112737 := by exact prefixLift 3112737
  have htrace : WordTrace (prefixWord ++ tailWord_3112737) baseStart_3112737 baseEnd_3112737 := by
    simpa [prefixWord, tailWord_3112737, baseEnd_3112737] using wordTrace_append hprefix tailTrace_3112737
  have hstable : (prefixWord ++ tailWord_3112737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112737).length < 2 ^ (prefixWord ++ tailWord_3112737).sum := by decide
  have hdescent : baseEnd_3112737 < baseStart_3112737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112744 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3112744 : Nat := 118140960795 + 3112744 * 2 ^ 59
def prefixEnd_3112744 : Nat := 4983230072969 + 3 ^ 40 * 3112744 * 2
def baseEnd_3112744 : Nat := 1598333826398874608484757

theorem tailTrace_3112744 : CollatzResearch.WordTrace tailWord_3112744 prefixEnd_3112744 1598333826398874608484757 := by
  unfold tailWord_3112744
  simp only [CollatzResearch.WordTrace]
  refine ⟨56765550317533788598164643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75687400423378384797552857 56765550317533788598164643)
  ·
    refine ⟨85148325476300682897246965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56765550317533788598164643 85148325476300682897246965)
    ·
      refine ⟨7982655513403189021616903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85148325476300682897246965 7982655513403189021616903)
      ·
        refine ⟨11973983270104783532425355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982655513403189021616903 11973983270104783532425355)
        ·
          refine ⟨17960974905157175298638033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973983270104783532425355 17960974905157175298638033)
          ·
            refine ⟨13470731178867881473978525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17960974905157175298638033 13470731178867881473978525)
            ·
              refine ⟨5051524192075455552741947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13470731178867881473978525 5051524192075455552741947)
              ·
                refine ⟨7577286288113183329112921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051524192075455552741947 7577286288113183329112921)
                ·
                  refine ⟨5682964716084887496834691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577286288113183329112921 5682964716084887496834691)
                  ·
                    refine ⟨8524447074127331245252037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5682964716084887496834691 8524447074127331245252037)
                    ·
                      refine ⟨1598333826398874608484757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8524447074127331245252037 1598333826398874608484757)
                      ·
                        rfl

theorem cell23_3112744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3112744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112744 prefixEnd_3112744 := by exact prefixLift 3112744
  have htrace : WordTrace (prefixWord ++ tailWord_3112744) baseStart_3112744 baseEnd_3112744 := by
    simpa [prefixWord, tailWord_3112744, baseEnd_3112744] using wordTrace_append hprefix tailTrace_3112744
  have hstable : (prefixWord ++ tailWord_3112744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112744).length < 2 ^ (prefixWord ++ tailWord_3112744).sum := by decide
  have hdescent : baseEnd_3112744 < baseStart_3112744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112767 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 8]
def baseStart_3112767 : Nat := 118140960795 + 3112767 * 2 ^ 59
def prefixEnd_3112767 : Nat := 4983230072969 + 3 ^ 40 * 3112767 * 2
def baseEnd_3112767 : Nat := 177593959605992002055239

theorem tailTrace_3112767 : CollatzResearch.WordTrace tailWord_3112767 prefixEnd_3112767 177593959605992002055239 := by
  unfold tailWord_3112767
  simp only [CollatzResearch.WordTrace]
  refine ⟨113531939513984252124416555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75687959675989501416277703 113531939513984252124416555)
  ·
    refine ⟨170297909270976378186624833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113531939513984252124416555 170297909270976378186624833)
    ·
      refine ⟨127723431953232283639968625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170297909270976378186624833 127723431953232283639968625)
      ·
        refine ⟨95792573964924212729976469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127723431953232283639968625 95792573964924212729976469)
        ·
          refine ⟨4490276904605822471717647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95792573964924212729976469 4490276904605822471717647)
          ·
            refine ⟨6735415356908733707576471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490276904605822471717647 6735415356908733707576471)
            ·
              refine ⟨10103123035363100561364707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735415356908733707576471 10103123035363100561364707)
              ·
                refine ⟨15154684553044650842047061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10103123035363100561364707 15154684553044650842047061)
                ·
                  refine ⟨177593959605992002055239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15154684553044650842047061 177593959605992002055239)
                  ·
                    rfl

theorem cell23_3112767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 8].length) (baseStart_3112767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112767 prefixEnd_3112767 := by exact prefixLift 3112767
  have htrace : WordTrace (prefixWord ++ tailWord_3112767) baseStart_3112767 baseEnd_3112767 := by
    simpa [prefixWord, tailWord_3112767, baseEnd_3112767] using wordTrace_append hprefix tailTrace_3112767
  have hstable : (prefixWord ++ tailWord_3112767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112767).length < 2 ^ (prefixWord ++ tailWord_3112767).sum := by decide
  have hdescent : baseEnd_3112767 < baseStart_3112767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112794 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_3112794 : Nat := 118140960795 + 3112794 * 2 ^ 59
def prefixEnd_3112794 : Nat := 4983230072969 + 3 ^ 40 * 3112794 * 2
def baseEnd_3112794 : Nat := 1598359500431599412859527

theorem tailTrace_3112794 : CollatzResearch.WordTrace tailWord_3112794 prefixEnd_3112794 1598359500431599412859527 := by
  unfold tailWord_3112794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28383231071221608933912359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75688616189924290490432957 28383231071221608933912359)
  ·
    refine ⟨42574846606832413400868539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28383231071221608933912359 42574846606832413400868539)
    ·
      refine ⟨63862269910248620101302809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42574846606832413400868539 63862269910248620101302809)
      ·
        refine ⟨47896702432686465075977107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63862269910248620101302809 47896702432686465075977107)
        ·
          refine ⟨71845053649029697613965661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47896702432686465075977107 71845053649029697613965661)
          ·
            refine ⟨26941895118386136605237123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71845053649029697613965661 26941895118386136605237123)
            ·
              refine ⟨40412842677579204907855685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26941895118386136605237123 40412842677579204907855685)
              ·
                refine ⟨7577408002046100920222941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40412842677579204907855685 7577408002046100920222941)
                ·
                  refine ⟨2841528000767287845083603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7577408002046100920222941 2841528000767287845083603)
                  ·
                    refine ⟨4262292001150931767625405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2841528000767287845083603 4262292001150931767625405)
                    ·
                      refine ⟨1598359500431599412859527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4262292001150931767625405 1598359500431599412859527)
                      ·
                        rfl

theorem cell23_3112794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_3112794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112794 prefixEnd_3112794 := by exact prefixLift 3112794
  have htrace : WordTrace (prefixWord ++ tailWord_3112794) baseStart_3112794 baseEnd_3112794 := by
    simpa [prefixWord, tailWord_3112794, baseEnd_3112794] using wordTrace_append hprefix tailTrace_3112794
  have hstable : (prefixWord ++ tailWord_3112794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112794).length < 2 ^ (prefixWord ++ tailWord_3112794).sum := by decide
  have hdescent : baseEnd_3112794 < baseStart_3112794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112821 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_3112821 : Nat := 118140960795 + 3112821 * 2 ^ 59
def prefixEnd_3112821 : Nat := 4983230072969 + 3 ^ 40 * 3112821 * 2
def baseEnd_3112821 : Nat := 1598373364409270807221903

theorem tailTrace_3112821 : CollatzResearch.WordTrace tailWord_3112821 prefixEnd_3112821 1598373364409270807221903 := by
  unfold tailWord_3112821
  simp only [CollatzResearch.WordTrace]
  refine ⟨113533909055788619346882317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75689272703859079564588211 113533909055788619346882317)
  ·
    refine ⟨42575215895920732255080869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113533909055788619346882317 42575215895920732255080869)
    ·
      refine ⟨7982852980485137297827663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42575215895920732255080869 7982852980485137297827663)
      ·
        refine ⟨11974279470727705946741495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982852980485137297827663 11974279470727705946741495)
        ·
          refine ⟨17961419206091558920112243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974279470727705946741495 17961419206091558920112243)
          ·
            refine ⟨26942128809137338380168365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961419206091558920112243 26942128809137338380168365)
            ·
              refine ⟨10103298303426501892563137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26942128809137338380168365 10103298303426501892563137)
              ·
                refine ⟨7577473727569876419422353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103298303426501892563137 7577473727569876419422353)
                ·
                  refine ⟨5683105295677407314566765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577473727569876419422353 5683105295677407314566765)
                  ·
                    refine ⟨2131164485879027742962537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5683105295677407314566765 2131164485879027742962537)
                    ·
                      refine ⟨1598373364409270807221903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131164485879027742962537 1598373364409270807221903)
                      ·
                        rfl

theorem cell23_3112821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_3112821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112821 prefixEnd_3112821 := by exact prefixLift 3112821
  have htrace : WordTrace (prefixWord ++ tailWord_3112821) baseStart_3112821 baseEnd_3112821 := by
    simpa [prefixWord, tailWord_3112821, baseEnd_3112821] using wordTrace_append hprefix tailTrace_3112821
  have hstable : (prefixWord ++ tailWord_3112821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112821).length < 2 ^ (prefixWord ++ tailWord_3112821).sum := by decide
  have hdescent : baseEnd_3112821 < baseStart_3112821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112837 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_3112837 : Nat := 118140960795 + 3112837 * 2 ^ 59
def prefixEnd_3112837 : Nat := 4983230072969 + 3 ^ 40 * 3112837 * 2
def baseEnd_3112837 : Nat := 1598381580099742744621829

theorem tailTrace_3112837 : CollatzResearch.WordTrace tailWord_3112837 prefixEnd_3112837 1598381580099742744621829 := by
  unfold tailWord_3112837
  simp only [CollatzResearch.WordTrace]
  refine ⟨113534492623730654079464765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75689661749153769386309843 113534492623730654079464765)
  ·
    refine ⟨42575434733898995279799287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113534492623730654079464765 42575434733898995279799287)
    ·
      refine ⟨63863152100848492919698931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42575434733898995279799287 63863152100848492919698931)
      ·
        refine ⟨95794728151272739379548397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63863152100848492919698931 95794728151272739379548397)
        ·
          refine ⟨35923023056727277267330649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95794728151272739379548397 35923023056727277267330649)
          ·
            refine ⟨26942267292545457950497987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35923023056727277267330649 26942267292545457950497987)
            ·
              refine ⟨40413400938818186925746981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26942267292545457950497987 40413400938818186925746981)
              ·
                refine ⟨7577512676028410048577559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40413400938818186925746981 7577512676028410048577559)
                ·
                  refine ⟨11366269014042615072866339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7577512676028410048577559 11366269014042615072866339)
                  ·
                    refine ⟨17049403521063922609299509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11366269014042615072866339 17049403521063922609299509)
                    ·
                      refine ⟨1598381580099742744621829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17049403521063922609299509 1598381580099742744621829)
                      ·
                        rfl

theorem cell23_3112837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_3112837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112837 prefixEnd_3112837 := by exact prefixLift 3112837
  have htrace : WordTrace (prefixWord ++ tailWord_3112837) baseStart_3112837 baseEnd_3112837 := by
    simpa [prefixWord, tailWord_3112837, baseEnd_3112837] using wordTrace_append hprefix tailTrace_3112837
  have hstable : (prefixWord ++ tailWord_3112837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112837).length < 2 ^ (prefixWord ++ tailWord_3112837).sum := by decide
  have hdescent : baseEnd_3112837 < baseStart_3112837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112871 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3112871 : Nat := 118140960795 + 3112871 * 2 ^ 59
def prefixEnd_3112871 : Nat := 4983230072969 + 3 ^ 40 * 3112871 * 2
def baseEnd_3112871 : Nat := 1598399038441995611596673

theorem tailTrace_3112871 : CollatzResearch.WordTrace tailWord_3112871 prefixEnd_3112871 1598399038441995611596673 := by
  unfold tailWord_3112871
  simp only [CollatzResearch.WordTrace]
  refine ⟨113535732705607477886202467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75690488470404985257468311 113535732705607477886202467)
  ·
    refine ⟨170303599058411216829303701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113535732705607477886202467 170303599058411216829303701)
    ·
      refine ⟨7982981205863025788873611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170303599058411216829303701 7982981205863025788873611)
      ·
        refine ⟨11974471808794538683310417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982981205863025788873611 11974471808794538683310417)
        ·
          refine ⟨8980853856595904012482813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11974471808794538683310417 8980853856595904012482813)
          ·
            refine ⟨3367820196223464004681055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8980853856595904012482813 3367820196223464004681055)
            ·
              refine ⟨5051730294335196007021583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367820196223464004681055 5051730294335196007021583)
              ·
                refine ⟨7577595441502794010532375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051730294335196007021583 7577595441502794010532375)
                ·
                  refine ⟨11366393162254191015798563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7577595441502794010532375 11366393162254191015798563)
                  ·
                    refine ⟨17049589743381286523697845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11366393162254191015798563 17049589743381286523697845)
                    ·
                      refine ⟨1598399038441995611596673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17049589743381286523697845 1598399038441995611596673)
                      ·
                        rfl

theorem cell23_3112871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3112871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112871 prefixEnd_3112871 := by exact prefixLift 3112871
  have htrace : WordTrace (prefixWord ++ tailWord_3112871) baseStart_3112871 baseEnd_3112871 := by
    simpa [prefixWord, tailWord_3112871, baseEnd_3112871] using wordTrace_append hprefix tailTrace_3112871
  have hstable : (prefixWord ++ tailWord_3112871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112871).length < 2 ^ (prefixWord ++ tailWord_3112871).sum := by decide
  have hdescent : baseEnd_3112871 < baseStart_3112871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112885 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_3112885 : Nat := 118140960795 + 3112885 * 2 ^ 59
def prefixEnd_3112885 : Nat := 4983230072969 + 3 ^ 40 * 3112885 * 2
def baseEnd_3112885 : Nat := 1598406227171158556821609

theorem tailTrace_3112885 : CollatzResearch.WordTrace tailWord_3112885 prefixEnd_3112885 1598406227171158556821609 := by
  unfold tailWord_3112885
  simp only [CollatzResearch.WordTrace]
  refine ⟨113536243327556758277212109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75690828885037838851474739 113536243327556758277212109)
  ·
    refine ⟨42576091247833784353954541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113536243327556758277212109 42576091247833784353954541)
    ·
      refine ⟨15966034217937669132732953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42576091247833784353954541 15966034217937669132732953)
      ·
        refine ⟨11974525663453251849549715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15966034217937669132732953 11974525663453251849549715)
        ·
          refine ⟨17961788495179877774324573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11974525663453251849549715 17961788495179877774324573)
          ·
            refine ⟨6735670685692454165371715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17961788495179877774324573 6735670685692454165371715)
            ·
              refine ⟨10103506028538681248057573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735670685692454165371715 10103506028538681248057573)
              ·
                refine ⟨1894407380351002734010795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10103506028538681248057573 1894407380351002734010795)
                ·
                  refine ⟨2841611070526504101016193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894407380351002734010795 2841611070526504101016193)
                  ·
                    refine ⟨2131208302894878075762145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2841611070526504101016193 2131208302894878075762145)
                    ·
                      refine ⟨1598406227171158556821609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131208302894878075762145 1598406227171158556821609)
                      ·
                        rfl

theorem cell23_3112885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_3112885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112885 prefixEnd_3112885 := by exact prefixLift 3112885
  have htrace : WordTrace (prefixWord ++ tailWord_3112885) baseStart_3112885 baseEnd_3112885 := by
    simpa [prefixWord, tailWord_3112885, baseEnd_3112885] using wordTrace_append hprefix tailTrace_3112885
  have hstable : (prefixWord ++ tailWord_3112885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112885).length < 2 ^ (prefixWord ++ tailWord_3112885).sum := by decide
  have hdescent : baseEnd_3112885 < baseStart_3112885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112907 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_3112907 : Nat := 118140960795 + 3112907 * 2 ^ 59
def prefixEnd_3112907 : Nat := 4983230072969 + 3 ^ 40 * 3112907 * 2
def baseEnd_3112907 : Nat := 1598417523745557470746507

theorem tailTrace_3112907 : CollatzResearch.WordTrace tailWord_3112907 prefixEnd_3112907 1598417523745557470746507 := by
  unfold tailWord_3112907
  simp only [CollatzResearch.WordTrace]
  refine ⟨113537045733477056034512975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75691363822318037356341983 113537045733477056034512975)
  ·
    refine ⟨170305568600215584051769463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113537045733477056034512975 170305568600215584051769463)
    ·
      refine ⟨255458352900323376077654195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170305568600215584051769463 255458352900323376077654195)
      ·
        refine ⟨383187529350485064116481293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255458352900323376077654195 383187529350485064116481293)
        ·
          refine ⟨143695323506431899043680485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383187529350485064116481293 143695323506431899043680485)
          ·
            refine ⟨26942873157455981070690091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143695323506431899043680485 26942873157455981070690091)
            ·
              refine ⟨40414309736183971606035137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26942873157455981070690091 40414309736183971606035137)
              ·
                refine ⟨30310732302137978704526353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40414309736183971606035137 30310732302137978704526353)
                ·
                  refine ⟨22733049226603484028394765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30310732302137978704526353 22733049226603484028394765)
                  ·
                    refine ⟨8524893459976306510648037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22733049226603484028394765 8524893459976306510648037)
                    ·
                      refine ⟨1598417523745557470746507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8524893459976306510648037 1598417523745557470746507)
                      ·
                        rfl

theorem cell23_3112907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_3112907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112907 prefixEnd_3112907 := by exact prefixLift 3112907
  have htrace : WordTrace (prefixWord ++ tailWord_3112907) baseStart_3112907 baseEnd_3112907 := by
    simpa [prefixWord, tailWord_3112907, baseEnd_3112907] using wordTrace_append hprefix tailTrace_3112907
  have hstable : (prefixWord ++ tailWord_3112907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112907).length < 2 ^ (prefixWord ++ tailWord_3112907).sum := by decide
  have hdescent : baseEnd_3112907 < baseStart_3112907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112911 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 1, 3, 2]
def baseStart_3112911 : Nat := 118140960795 + 3112911 * 2 ^ 59
def prefixEnd_3112911 : Nat := 4983230072969 + 3 ^ 40 * 3112911 * 2
def baseEnd_3112911 : Nat := 1598419577668175455096489

theorem tailTrace_3112911 : CollatzResearch.WordTrace tailWord_3112911 prefixEnd_3112911 1598419577668175455096489 := by
  unfold tailWord_3112911
  simp only [CollatzResearch.WordTrace]
  refine ⟨113537191625462564717658587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75691461083641709811772391 113537191625462564717658587)
  ·
    refine ⟨170305787438193847076487881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113537191625462564717658587 170305787438193847076487881)
    ·
      refine ⟨127729340578645385307365911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170305787438193847076487881 127729340578645385307365911)
      ·
        refine ⟨191594010867968077961048867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127729340578645385307365911 191594010867968077961048867)
        ·
          refine ⟨287391016301952116941573301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191594010867968077961048867 287391016301952116941573301)
          ·
            refine ⟨26942907778308010963272497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287391016301952116941573301 26942907778308010963272497)
            ·
              refine ⟨20207180833731008222454373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26942907778308010963272497 20207180833731008222454373)
              ·
                refine ⟨3788846406324564041710195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20207180833731008222454373 3788846406324564041710195)
                ·
                  refine ⟨5683269609486846062565293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788846406324564041710195 5683269609486846062565293)
                  ·
                    refine ⟨2131226103557567273461985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5683269609486846062565293 2131226103557567273461985)
                    ·
                      refine ⟨1598419577668175455096489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131226103557567273461985 1598419577668175455096489)
                      ·
                        rfl

theorem cell23_3112911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3, 2].length) (baseStart_3112911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112911 prefixEnd_3112911 := by exact prefixLift 3112911
  have htrace : WordTrace (prefixWord ++ tailWord_3112911) baseStart_3112911 baseEnd_3112911 := by
    simpa [prefixWord, tailWord_3112911, baseEnd_3112911] using wordTrace_append hprefix tailTrace_3112911
  have hstable : (prefixWord ++ tailWord_3112911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112911).length < 2 ^ (prefixWord ++ tailWord_3112911).sum := by decide
  have hdescent : baseEnd_3112911 < baseStart_3112911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112935 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3112935 : Nat := 118140960795 + 3112935 * 2 ^ 59
def prefixEnd_3112935 : Nat := 4983230072969 + 3 ^ 40 * 3112935 * 2
def baseEnd_3112935 : Nat := 1598431901203883361196379

theorem tailTrace_3112935 : CollatzResearch.WordTrace tailWord_3112935 prefixEnd_3112935 1598431901203883361196379 := by
  unfold tailWord_3112935
  simp only [CollatzResearch.WordTrace]
  refine ⟨113538066977375616816532259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75692044651583744544354839 113538066977375616816532259)
  ·
    refine ⟨170307100466063425224798389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113538066977375616816532259 170307100466063425224798389)
    ·
      refine ⟨15966290668693446114824849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170307100466063425224798389 15966290668693446114824849)
      ·
        refine ⟨11974718001520084586118637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15966290668693446114824849 11974718001520084586118637)
        ·
          refine ⟨4490519250570031719794489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11974718001520084586118637 4490519250570031719794489)
          ·
            refine ⟨3367889437927523789845867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490519250570031719794489 3367889437927523789845867)
            ·
              refine ⟨5051834156891285684768801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367889437927523789845867 5051834156891285684768801)
              ·
                refine ⟨3788875617668464263576601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051834156891285684768801 3788875617668464263576601)
                ·
                  refine ⟨2841656713251348197682451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3788875617668464263576601 2841656713251348197682451)
                  ·
                    refine ⟨4262485069877022296523677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2841656713251348197682451 4262485069877022296523677)
                    ·
                      refine ⟨1598431901203883361196379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4262485069877022296523677 1598431901203883361196379)
                      ·
                        rfl

theorem cell23_3112935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3112935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3112935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3112935 prefixEnd_3112935 := by exact prefixLift 3112935
  have htrace : WordTrace (prefixWord ++ tailWord_3112935) baseStart_3112935 baseEnd_3112935 := by
    simpa [prefixWord, tailWord_3112935, baseEnd_3112935] using wordTrace_append hprefix tailTrace_3112935
  have hstable : (prefixWord ++ tailWord_3112935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112935).length < 2 ^ (prefixWord ++ tailWord_3112935).sum := by decide
  have hdescent : baseEnd_3112935 < baseStart_3112935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113007 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 8]
def baseStart_3113007 : Nat := 118140960795 + 3113007 * 2 ^ 59
def prefixEnd_3113007 : Nat := 4983230072969 + 3 ^ 40 * 3113007 * 2
def baseEnd_3113007 : Nat := 532822957270335693165349

theorem tailTrace_3113007 : CollatzResearch.WordTrace tailWord_3113007 prefixEnd_3113007 532822957270335693165349 := by
  unfold tailWord_3113007
  simp only [CollatzResearch.WordTrace]
  refine ⟨113540693033114773113153275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75693795355409848742102183 113540693033114773113153275)
  ·
    refine ⟨170311039549672159669729913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113540693033114773113153275 170311039549672159669729913)
    ·
      refine ⟨127733279662254119752297435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170311039549672159669729913 127733279662254119752297435)
      ·
        refine ⟨191599919493381179628446153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127733279662254119752297435 191599919493381179628446153)
        ·
          refine ⟨143699939620035884721334615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191599919493381179628446153 143699939620035884721334615)
          ·
            refine ⟨215549909430053827082001923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143699939620035884721334615 215549909430053827082001923)
            ·
              refine ⟨323324864145080740623002885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215549909430053827082001923 323324864145080740623002885)
              ·
                refine ⟨60623412027202638866813041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323324864145080740623002885 60623412027202638866813041)
                ·
                  refine ⟨45467559020401979150109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60623412027202638866813041 45467559020401979150109781)
                  ·
                    refine ⟨532822957270335693165349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45467559020401979150109781 532822957270335693165349)
                    ·
                      rfl

theorem cell23_3113007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_3113007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113007 prefixEnd_3113007 := by exact prefixLift 3113007
  have htrace : WordTrace (prefixWord ++ tailWord_3113007) baseStart_3113007 baseEnd_3113007 := by
    simpa [prefixWord, tailWord_3113007, baseEnd_3113007] using wordTrace_append hprefix tailTrace_3113007
  have hstable : (prefixWord ++ tailWord_3113007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113007).length < 2 ^ (prefixWord ++ tailWord_3113007).sum := by decide
  have hdescent : baseEnd_3113007 < baseStart_3113007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113031 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_3113031 : Nat := 118140960795 + 3113031 * 2 ^ 59
def prefixEnd_3113031 : Nat := 4983230072969 + 3 ^ 40 * 3113031 * 2
def baseEnd_3113031 : Nat := 1598481195346714985595937

theorem tailTrace_3113031 : CollatzResearch.WordTrace tailWord_3113031 prefixEnd_3113031 1598481195346714985595937 := by
  unfold tailWord_3113031
  simp only [CollatzResearch.WordTrace]
  refine ⟨113541568385027825212026947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75694378923351883474684631 113541568385027825212026947)
  ·
    refine ⟨170312352577541737818040421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113541568385027825212026947 170312352577541737818040421)
    ·
      refine ⟨31933566108289075840882579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170312352577541737818040421 31933566108289075840882579)
      ·
        refine ⟨47900349162433613761323869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31933566108289075840882579 47900349162433613761323869)
        ·
          refine ⟨17962630935912605160496451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47900349162433613761323869 17962630935912605160496451)
          ·
            refine ⟨26943946403868907740744677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17962630935912605160496451 26943946403868907740744677)
            ·
              refine ⟨5051989950725420201389627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26943946403868907740744677 5051989950725420201389627)
              ·
                refine ⟨7577984926088130302084441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5051989950725420201389627 7577984926088130302084441)
                ·
                  refine ⟨5683488694566097726563331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7577984926088130302084441 5683488694566097726563331)
                  ·
                    refine ⟨8525233041849146589844997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683488694566097726563331 8525233041849146589844997)
                    ·
                      refine ⟨1598481195346714985595937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8525233041849146589844997 1598481195346714985595937)
                      ·
                        rfl

theorem cell23_3113031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_3113031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113031 prefixEnd_3113031 := by exact prefixLift 3113031
  have htrace : WordTrace (prefixWord ++ tailWord_3113031) baseStart_3113031 baseEnd_3113031 := by
    simpa [prefixWord, tailWord_3113031, baseEnd_3113031] using wordTrace_append hprefix tailTrace_3113031
  have hstable : (prefixWord ++ tailWord_3113031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113031).length < 2 ^ (prefixWord ++ tailWord_3113031).sum := by decide
  have hdescent : baseEnd_3113031 < baseStart_3113031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113044 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3113044 : Nat := 118140960795 + 3113044 * 2 ^ 59
def prefixEnd_3113044 : Nat := 4983230072969 + 3 ^ 40 * 3113044 * 2
def baseEnd_3113044 : Nat := 1598487870595223434733377

theorem tailTrace_3113044 : CollatzResearch.WordTrace tailWord_3113044 prefixEnd_3113044 1598487870595223434733377 := by
  unfold tailWord_3113044
  simp only [CollatzResearch.WordTrace]
  refine ⟨56771021266990364216125093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75694695022653818954833457 56771021266990364216125093)
  ·
    refine ⟨10644566487560693290523455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56771021266990364216125093 10644566487560693290523455)
    ·
      refine ⟨15966849731341039935785183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644566487560693290523455 15966849731341039935785183)
      ·
        refine ⟨23950274597011559903677775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15966849731341039935785183 23950274597011559903677775)
        ·
          refine ⟨35925411895517339855516663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23950274597011559903677775 35925411895517339855516663)
          ·
            refine ⟨53888117843276009783274995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35925411895517339855516663 53888117843276009783274995)
            ·
              refine ⟨80832176764914014674912493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53888117843276009783274995 80832176764914014674912493)
              ·
                refine ⟨30312066286842755503092185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80832176764914014674912493 30312066286842755503092185)
                ·
                  refine ⟨22734049715132066627319139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30312066286842755503092185 22734049715132066627319139)
                  ·
                    refine ⟨34101074572698099940978709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22734049715132066627319139 34101074572698099940978709)
                    ·
                      refine ⟨1598487870595223434733377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34101074572698099940978709 1598487870595223434733377)
                      ·
                        rfl

theorem cell23_3113044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3113044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113044 prefixEnd_3113044 := by exact prefixLift 3113044
  have htrace : WordTrace (prefixWord ++ tailWord_3113044) baseStart_3113044 baseEnd_3113044 := by
    simpa [prefixWord, tailWord_3113044, baseEnd_3113044] using wordTrace_append hprefix tailTrace_3113044
  have hstable : (prefixWord ++ tailWord_3113044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113044).length < 2 ^ (prefixWord ++ tailWord_3113044).sum := by decide
  have hdescent : baseEnd_3113044 < baseStart_3113044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113138 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3113138 : Nat := 118140960795 + 3113138 * 2 ^ 59
def prefixEnd_3113138 : Nat := 4983230072969 + 3 ^ 40 * 3113138 * 2
def baseEnd_3113138 : Nat := 1598536137776746066957945

theorem tailTrace_3113138 : CollatzResearch.WordTrace tailWord_3113138 prefixEnd_3113138 1598536137776746066957945 := by
  unfold tailWord_3113138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386367748910045621543017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75696980663760121657448045 28386367748910045621543017)
  ·
    refine ⟨21289775811682534216157263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28386367748910045621543017 21289775811682534216157263)
    ·
      refine ⟨31934663717523801324235895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21289775811682534216157263 31934663717523801324235895)
      ·
        refine ⟨47901995576285701986353843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31934663717523801324235895 47901995576285701986353843)
        ·
          refine ⟨71852993364428552979530765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47901995576285701986353843 71852993364428552979530765)
          ·
            refine ⟨26944872511660707367324037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71852993364428552979530765 26944872511660707367324037)
            ·
              refine ⟨5052163595936382631373257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26944872511660707367324037 5052163595936382631373257)
              ·
                refine ⟨3789122696952286973529943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052163595936382631373257 3789122696952286973529943)
                ·
                  refine ⟨5683684045428430460294915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789122696952286973529943 5683684045428430460294915)
                  ·
                    refine ⟨8525526068142645690442373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5683684045428430460294915 8525526068142645690442373)
                    ·
                      refine ⟨1598536137776746066957945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8525526068142645690442373 1598536137776746066957945)
                      ·
                        rfl

theorem cell23_3113138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3113138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113138 prefixEnd_3113138 := by exact prefixLift 3113138
  have htrace : WordTrace (prefixWord ++ tailWord_3113138) baseStart_3113138 baseEnd_3113138 := by
    simpa [prefixWord, tailWord_3113138, baseEnd_3113138] using wordTrace_append hprefix tailTrace_3113138
  have hstable : (prefixWord ++ tailWord_3113138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113138).length < 2 ^ (prefixWord ++ tailWord_3113138).sum := by decide
  have hdescent : baseEnd_3113138 < baseStart_3113138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113144 : List Nat := [2, 1, 2, 1, 2, 1, 5, 9]
def baseStart_3113144 : Nat := 118140960795 + 3113144 * 2 ^ 59
def prefixEnd_3113144 : Nat := 4983230072969 + 3 ^ 40 * 3113144 * 2
def baseEnd_3113144 : Nat := 59205156246691594203071

theorem tailTrace_3113144 : CollatzResearch.WordTrace tailWord_3113144 prefixEnd_3113144 59205156246691594203071 := by
  unfold tailWord_3113144
  simp only [CollatzResearch.WordTrace]
  refine ⟨56772844916809222755445243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75697126555745630340593657 56772844916809222755445243)
  ·
    refine ⟨85159267375213834133167865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56772844916809222755445243 85159267375213834133167865)
    ·
      refine ⟨63869450531410375599875899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85159267375213834133167865 63869450531410375599875899)
      ·
        refine ⟨95804175797115563399813849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63869450531410375599875899 95804175797115563399813849)
        ·
          refine ⟨71853131847836672549860387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95804175797115563399813849 71853131847836672549860387)
          ·
            refine ⟨107779697771755008824790581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71853131847836672549860387 107779697771755008824790581)
            ·
              refine ⟨10104346666102032077324117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107779697771755008824790581 10104346666102032077324117)
              ·
                refine ⟨59205156246691594203071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10104346666102032077324117 59205156246691594203071)
                ·
                  rfl

theorem cell23_3113144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 9].length) (baseStart_3113144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113144 prefixEnd_3113144 := by exact prefixLift 3113144
  have htrace : WordTrace (prefixWord ++ tailWord_3113144) baseStart_3113144 baseEnd_3113144 := by
    simpa [prefixWord, tailWord_3113144, baseEnd_3113144] using wordTrace_append hprefix tailTrace_3113144
  have hstable : (prefixWord ++ tailWord_3113144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113144).length < 2 ^ (prefixWord ++ tailWord_3113144).sum := by decide
  have hdescent : baseEnd_3113144 < baseStart_3113144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113186 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3113186 : Nat := 118140960795 + 3113186 * 2 ^ 59
def prefixEnd_3113186 : Nat := 4983230072969 + 3 ^ 40 * 3113186 * 2
def baseEnd_3113186 : Nat := 532853594949387293052575

theorem tailTrace_3113186 : CollatzResearch.WordTrace tailWord_3113186 prefixEnd_3113186 532853594949387293052575 := by
  unfold tailWord_3113186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386805424866571670979853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75698147799644191122612941 28386805424866571670979853)
  ·
    refine ⟨10645052034324964376617445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28386805424866571670979853 10645052034324964376617445)
    ·
      refine ⟨1995947256435930820615771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10645052034324964376617445 1995947256435930820615771)
      ·
        refine ⟨2993920884653896230923657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995947256435930820615771 2993920884653896230923657)
        ·
          refine ⟨2245440663490422173192743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993920884653896230923657 2245440663490422173192743)
          ·
            refine ⟨3368160995235633259789115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245440663490422173192743 3368160995235633259789115)
            ·
              refine ⟨5052241492853449889683673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368160995235633259789115 5052241492853449889683673)
              ·
                refine ⟨3789181119640087417262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052241492853449889683673 3789181119640087417262755)
                ·
                  refine ⟨5683771679460131125894133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789181119640087417262755 5683771679460131125894133)
                  ·
                    refine ⟨532853594949387293052575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5683771679460131125894133 532853594949387293052575)
                    ·
                      rfl

theorem cell23_3113186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3113186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113186 prefixEnd_3113186 := by exact prefixLift 3113186
  have htrace : WordTrace (prefixWord ++ tailWord_3113186) baseStart_3113186 baseEnd_3113186 := by
    simpa [prefixWord, tailWord_3113186, baseEnd_3113186] using wordTrace_append hprefix tailTrace_3113186
  have hstable : (prefixWord ++ tailWord_3113186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113186).length < 2 ^ (prefixWord ++ tailWord_3113186).sum := by decide
  have hdescent : baseEnd_3113186 < baseStart_3113186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113223 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3113223 : Nat := 118140960795 + 3113223 * 2 ^ 59
def prefixEnd_3113223 : Nat := 4983230072969 + 3 ^ 40 * 3113223 * 2
def baseEnd_3113223 : Nat := 1598579783632378234395055

theorem tailTrace_3113223 : CollatzResearch.WordTrace tailWord_3113223 prefixEnd_3113223 1598579783632378234395055 := by
  unfold tailWord_3113223
  simp only [CollatzResearch.WordTrace]
  refine ⟨113548571200332242003016323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75699047466888161335344215 113548571200332242003016323)
  ·
    refine ⟨170322856800498363004524485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113548571200332242003016323 170322856800498363004524485)
    ·
      refine ⟨31935535650093443063348341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170322856800498363004524485 31935535650093443063348341)
      ·
        refine ⟨2993956467196260287188907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31935535650093443063348341 2993956467196260287188907)
        ·
          refine ⟨4490934700794390430783361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993956467196260287188907 4490934700794390430783361)
          ·
            refine ⟨3368201025595792823087521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490934700794390430783361 3368201025595792823087521)
            ·
              refine ⟨2526150769196844617315641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368201025595792823087521 2526150769196844617315641)
              ·
                refine ⟨1894613076897633462986731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526150769196844617315641 1894613076897633462986731)
                ·
                  refine ⟨2841919615346450194480097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894613076897633462986731 2841919615346450194480097)
                  ·
                    refine ⟨2131439711509837645860073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2841919615346450194480097 2131439711509837645860073)
                    ·
                      refine ⟨1598579783632378234395055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131439711509837645860073 1598579783632378234395055)
                      ·
                        rfl

theorem cell23_3113223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3113223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113223 prefixEnd_3113223 := by exact prefixLift 3113223
  have htrace : WordTrace (prefixWord ++ tailWord_3113223) baseStart_3113223 baseEnd_3113223 := by
    simpa [prefixWord, tailWord_3113223, baseEnd_3113223] using wordTrace_append hprefix tailTrace_3113223
  have hstable : (prefixWord ++ tailWord_3113223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113223).length < 2 ^ (prefixWord ++ tailWord_3113223).sum := by decide
  have hdescent : baseEnd_3113223 < baseStart_3113223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113228 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_3113228 : Nat := 118140960795 + 3113228 * 2 ^ 59
def prefixEnd_3113228 : Nat := 4983230072969 + 3 ^ 40 * 3113228 * 2
def baseEnd_3113228 : Nat := 1598582351035650714832531

theorem tailTrace_3113228 : CollatzResearch.WordTrace tailWord_3113228 prefixEnd_3113228 1598582351035650714832531 := by
  unfold tailWord_3113228
  simp only [CollatzResearch.WordTrace]
  refine ⟨56774376782657063928474169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75699169043542751904632225 56774376782657063928474169)
  ·
    refine ⟨42580782586992797946355627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56774376782657063928474169 42580782586992797946355627)
    ·
      refine ⟨63871173880489196919533441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42580782586992797946355627 63871173880489196919533441)
      ·
        refine ⟨47903380410366897689650081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63871173880489196919533441 47903380410366897689650081)
        ·
          refine ⟨35927535307775173267237561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47903380410366897689650081 35927535307775173267237561)
          ·
            refine ⟨26945651480831379950428171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35927535307775173267237561 26945651480831379950428171)
            ·
              refine ⟨40418477221247069925642257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26945651480831379950428171 40418477221247069925642257)
              ·
                refine ⟨30313857915935302444231693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40418477221247069925642257 30313857915935302444231693)
                ·
                  refine ⟨11367696718475738416586885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30313857915935302444231693 11367696718475738416586885)
                  ·
                    refine ⟨2131443134714200953110041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11367696718475738416586885 2131443134714200953110041)
                    ·
                      refine ⟨1598582351035650714832531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131443134714200953110041 1598582351035650714832531)
                      ·
                        rfl

theorem cell23_3113228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_3113228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113228 prefixEnd_3113228 := by exact prefixLift 3113228
  have htrace : WordTrace (prefixWord ++ tailWord_3113228) baseStart_3113228 baseEnd_3113228 := by
    simpa [prefixWord, tailWord_3113228, baseEnd_3113228] using wordTrace_append hprefix tailTrace_3113228
  have hstable : (prefixWord ++ tailWord_3113228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113228).length < 2 ^ (prefixWord ++ tailWord_3113228).sum := by decide
  have hdescent : baseEnd_3113228 < baseStart_3113228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113251 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 7]
def baseStart_3113251 : Nat := 118140960795 + 3113251 * 2 ^ 59
def prefixEnd_3113251 : Nat := 4983230072969 + 3 ^ 40 * 3113251 * 2
def baseEnd_3113251 : Nat := 177621573454522680538325

theorem tailTrace_3113251 : CollatzResearch.WordTrace tailWord_3113251 prefixEnd_3113251 177621573454522680538325 := by
  unfold tailWord_3113251
  simp only [CollatzResearch.WordTrace]
  refine ⟨113549592444230802785035607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75699728296153868523357071 113549592444230802785035607)
  ·
    refine ⟨170324388666346204177553411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113549592444230802785035607 170324388666346204177553411)
    ·
      refine ⟨255486582999519306266330117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170324388666346204177553411 255486582999519306266330117)
      ·
        refine ⟨47903734312409869924936897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255486582999519306266330117 47903734312409869924936897)
        ·
          refine ⟨35927800734307402443702673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47903734312409869924936897 35927800734307402443702673)
          ·
            refine ⟨26945850550730551832777005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35927800734307402443702673 26945850550730551832777005)
            ·
              refine ⟨10104693956523956937291377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26945850550730551832777005 10104693956523956937291377)
              ·
                refine ⟨7578520467392967702968533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10104693956523956937291377 7578520467392967702968533)
                ·
                  refine ⟨177621573454522680538325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7578520467392967702968533 177621573454522680538325)
                  ·
                    rfl

theorem cell23_3113251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 7].length) (baseStart_3113251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113251 prefixEnd_3113251 := by exact prefixLift 3113251
  have htrace : WordTrace (prefixWord ++ tailWord_3113251) baseStart_3113251 baseEnd_3113251 := by
    simpa [prefixWord, tailWord_3113251, baseEnd_3113251] using wordTrace_append hprefix tailTrace_3113251
  have hstable : (prefixWord ++ tailWord_3113251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113251).length < 2 ^ (prefixWord ++ tailWord_3113251).sum := by decide
  have hdescent : baseEnd_3113251 < baseStart_3113251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113266 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_3113266 : Nat := 118140960795 + 3113266 * 2 ^ 59
def prefixEnd_3113266 : Nat := 4983230072969 + 3 ^ 40 * 3113266 * 2
def baseEnd_3113266 : Nat := 1598601863300521566157357

theorem tailTrace_3113266 : CollatzResearch.WordTrace tailWord_3113266 prefixEnd_3113266 1598601863300521566157357 := by
  unfold tailWord_3113266
  simp only [CollatzResearch.WordTrace]
  refine ⟨28387534884794115086707913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75700093026117640231221101 28387534884794115086707913)
  ·
    refine ⟨21290651163595586315030935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28387534884794115086707913 21290651163595586315030935)
    ·
      refine ⟨31935976745393379472546403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21290651163595586315030935 31935976745393379472546403)
      ·
        refine ⟨47903965118090069208819605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31935976745393379472546403 47903965118090069208819605)
        ·
          refine ⟨2245498364910471994163419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47903965118090069208819605 2245498364910471994163419)
          ·
            refine ⟨3368247547365707991245129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245498364910471994163419 3368247547365707991245129)
            ·
              refine ⟨2526185660524280993433847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368247547365707991245129 2526185660524280993433847)
              ·
                refine ⟨3789278490786421490150771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526185660524280993433847 3789278490786421490150771)
                ·
                  refine ⟨5683917736179632235226157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789278490786421490150771 5683917736179632235226157)
                  ·
                    refine ⟨2131469151067362088209809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5683917736179632235226157 2131469151067362088209809)
                    ·
                      refine ⟨1598601863300521566157357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131469151067362088209809 1598601863300521566157357)
                      ·
                        rfl

theorem cell23_3113266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_3113266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113266 prefixEnd_3113266 := by exact prefixLift 3113266
  have htrace : WordTrace (prefixWord ++ tailWord_3113266) baseStart_3113266 baseEnd_3113266 := by
    simpa [prefixWord, tailWord_3113266, baseEnd_3113266] using wordTrace_append hprefix tailTrace_3113266
  have hstable : (prefixWord ++ tailWord_3113266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113266).length < 2 ^ (prefixWord ++ tailWord_3113266).sum := by decide
  have hdescent : baseEnd_3113266 < baseStart_3113266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113288 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_3113288 : Nat := 118140960795 + 3113288 * 2 ^ 59
def prefixEnd_3113288 : Nat := 4983230072969 + 3 ^ 40 * 3113288 * 2
def baseEnd_3113288 : Nat := 1598613159874920480082255

theorem tailTrace_3113288 : CollatzResearch.WordTrace tailWord_3113288 prefixEnd_3113288 1598613159874920480082255 := by
  unfold tailWord_3113288
  simp only [CollatzResearch.WordTrace]
  refine ⟨56775470972548379052066259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75700627963397838736088345 56775470972548379052066259)
  ·
    refine ⟨85163206458822568578099389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56775470972548379052066259 85163206458822568578099389)
    ·
      refine ⟨31936202422058463216787271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85163206458822568578099389 31936202422058463216787271)
      ·
        refine ⟨47904303633087694825180907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31936202422058463216787271 47904303633087694825180907)
        ·
          refine ⟨71856455449631542237771361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47904303633087694825180907 71856455449631542237771361)
          ·
            refine ⟨53892341587223656678328521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71856455449631542237771361 53892341587223656678328521)
            ·
              refine ⟨40419256190417742508746391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53892341587223656678328521 40419256190417742508746391)
              ·
                refine ⟨60628884285626613763119587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40419256190417742508746391 60628884285626613763119587)
                ·
                  refine ⟨90943326428439920644679381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60628884285626613763119587 90943326428439920644679381)
                  ·
                    refine ⟨2131484213166560640109673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 90943326428439920644679381 2131484213166560640109673)
                    ·
                      refine ⟨1598613159874920480082255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131484213166560640109673 1598613159874920480082255)
                      ·
                        rfl

theorem cell23_3113288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_3113288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113288 prefixEnd_3113288 := by exact prefixLift 3113288
  have htrace : WordTrace (prefixWord ++ tailWord_3113288) baseStart_3113288 baseEnd_3113288 := by
    simpa [prefixWord, tailWord_3113288, baseEnd_3113288] using wordTrace_append hprefix tailTrace_3113288
  have hstable : (prefixWord ++ tailWord_3113288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113288).length < 2 ^ (prefixWord ++ tailWord_3113288).sum := by decide
  have hdescent : baseEnd_3113288 < baseStart_3113288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113331 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_3113331 : Nat := 118140960795 + 3113331 * 2 ^ 59
def prefixEnd_3113331 : Nat := 4983230072969 + 3 ^ 40 * 3113331 * 2
def baseEnd_3113331 : Nat := 1598635239543063811844557

theorem tailTrace_3113331 : CollatzResearch.WordTrace tailWord_3113331 prefixEnd_3113331 1598635239543063811844557 := by
  unfold tailWord_3113331
  simp only [CollatzResearch.WordTrace]
  refine ⟨113552510283940976447947847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75701673522627317631965231 113552510283940976447947847)
  ·
    refine ⟨170328765425911464671921771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113552510283940976447947847 170328765425911464671921771)
    ·
      refine ⟨255493148138867197007882657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170328765425911464671921771 255493148138867197007882657)
      ·
        refine ⟨191619861104150397755911993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255493148138867197007882657 191619861104150397755911993)
        ·
          refine ⟨143714895828112798316933995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191619861104150397755911993 143714895828112798316933995)
          ·
            refine ⟨215572343742169197475400993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143714895828112798316933995 215572343742169197475400993)
            ·
              refine ⟨161679257806626898106550745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215572343742169197475400993 161679257806626898106550745)
              ·
                refine ⟨121259443354970173579913059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161679257806626898106550745 121259443354970173579913059)
                ·
                  refine ⟨181889165032455260369869589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121259443354970173579913059 181889165032455260369869589)
                  ·
                    refine ⟨8526054610896340329837637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181889165032455260369869589 8526054610896340329837637)
                    ·
                      refine ⟨1598635239543063811844557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8526054610896340329837637 1598635239543063811844557)
                      ·
                        rfl

theorem cell23_3113331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_3113331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113331 prefixEnd_3113331 := by exact prefixLift 3113331
  have htrace : WordTrace (prefixWord ++ tailWord_3113331) baseStart_3113331 baseEnd_3113331 := by
    simpa [prefixWord, tailWord_3113331, baseEnd_3113331] using wordTrace_append hprefix tailTrace_3113331
  have hstable : (prefixWord ++ tailWord_3113331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113331).length < 2 ^ (prefixWord ++ tailWord_3113331).sum := by decide
  have hdescent : baseEnd_3113331 < baseStart_3113331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113366 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3113366 : Nat := 118140960795 + 3113366 * 2 ^ 59
def prefixEnd_3113366 : Nat := 4983230072969 + 3 ^ 40 * 3113366 * 2
def baseEnd_3113366 : Nat := 532884403788657058302299

theorem tailTrace_3113366 : CollatzResearch.WordTrace tailWord_3113366 prefixEnd_3113366 532884403788657058302299 := by
  unfold tailWord_3113366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097111677425886089091997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75702524559209451616981301 7097111677425886089091997)
  ·
    refine ⟨2661416879034707283409499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7097111677425886089091997 2661416879034707283409499)
    ·
      refine ⟨3992125318552060925114249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661416879034707283409499 3992125318552060925114249)
      ·
        refine ⟨2994093988914045693835687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3992125318552060925114249 2994093988914045693835687)
        ·
          refine ⟨4491140983371068540753531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994093988914045693835687 4491140983371068540753531)
          ·
            refine ⟨6736711475056602811130297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491140983371068540753531 6736711475056602811130297)
            ·
              refine ⟨5052533606292452108347723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6736711475056602811130297 5052533606292452108347723)
              ·
                refine ⟨7578800409438678162521585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052533606292452108347723 7578800409438678162521585)
                ·
                  refine ⟨5684100307079008621891189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578800409438678162521585 5684100307079008621891189)
                  ·
                    refine ⟨532884403788657058302299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5684100307079008621891189 532884403788657058302299)
                    ·
                      rfl

theorem cell23_3113366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3113366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113366 prefixEnd_3113366 := by exact prefixLift 3113366
  have htrace : WordTrace (prefixWord ++ tailWord_3113366) baseStart_3113366 baseEnd_3113366 := by
    simpa [prefixWord, tailWord_3113366, baseEnd_3113366] using wordTrace_append hprefix tailTrace_3113366
  have hstable : (prefixWord ++ tailWord_3113366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113366).length < 2 ^ (prefixWord ++ tailWord_3113366).sum := by decide
  have hdescent : baseEnd_3113366 < baseStart_3113366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113429 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3113429 : Nat := 118140960795 + 3113429 * 2 ^ 59
def prefixEnd_3113429 : Nat := 4983230072969 + 3 ^ 40 * 3113429 * 2
def baseEnd_3113429 : Nat := 1598685560647204428419107

theorem tailTrace_3113429 : CollatzResearch.WordTrace tailWord_3113429 prefixEnd_3113429 1598685560647204428419107 := by
  unfold tailWord_3113429
  simp only [CollatzResearch.WordTrace]
  refine ⟨113556084637585939185015341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75704056425057292790010227 113556084637585939185015341)
  ·
    refine ⟨42583531739094727194380753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113556084637585939185015341 42583531739094727194380753)
    ·
      refine ⟨31937648804321045395785565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42583531739094727194380753 31937648804321045395785565)
      ·
        refine ⟨11976618301620392023419587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31937648804321045395785565 11976618301620392023419587)
        ·
          refine ⟨17964927452430588035129381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11976618301620392023419587 17964927452430588035129381)
          ·
            refine ⟨3368423897330735256586759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17964927452430588035129381 3368423897330735256586759)
            ·
              refine ⟨5052635845996102884880139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368423897330735256586759 5052635845996102884880139)
              ·
                refine ⟨7578953768994154327320209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052635845996102884880139 7578953768994154327320209)
                ·
                  refine ⟨5684215326745615745490157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578953768994154327320209 5684215326745615745490157)
                  ·
                    refine ⟨2131580747529605904558809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5684215326745615745490157 2131580747529605904558809)
                    ·
                      refine ⟨1598685560647204428419107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131580747529605904558809 1598685560647204428419107)
                      ·
                        rfl

theorem cell23_3113429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3113429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113429 prefixEnd_3113429 := by exact prefixLift 3113429
  have htrace : WordTrace (prefixWord ++ tailWord_3113429) baseStart_3113429 baseEnd_3113429 := by
    simpa [prefixWord, tailWord_3113429, baseEnd_3113429] using wordTrace_append hprefix tailTrace_3113429
  have hstable : (prefixWord ++ tailWord_3113429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113429).length < 2 ^ (prefixWord ++ tailWord_3113429).sum := by decide
  have hdescent : baseEnd_3113429 < baseStart_3113429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113448 : List Nat := [2, 1, 4, 1, 1, 4, 10]
def baseStart_3113448 : Nat := 118140960795 + 3113448 * 2 ^ 59
def prefixEnd_3113448 : Nat := 4983230072969 + 3 ^ 40 * 3113448 * 2
def baseEnd_3113448 : Nat := 19736979219501726593599

theorem tailTrace_3113448 : CollatzResearch.WordTrace tailWord_3113448 prefixEnd_3113448 19736979219501726593599 := by
  unfold tailWord_3113448
  simp only [CollatzResearch.WordTrace]
  refine ⟨56778388812258552714978499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75704518416344736953304665 56778388812258552714978499)
  ·
    refine ⟨85167583218387829072467749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56778388812258552714978499 85167583218387829072467749)
    ·
      refine ⟨15968921853447717951087703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85167583218387829072467749 15968921853447717951087703)
      ·
        refine ⟨23953382780171576926631555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15968921853447717951087703 23953382780171576926631555)
        ·
          refine ⟨35930074170257365389947333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23953382780171576926631555 35930074170257365389947333)
          ·
            refine ⟨6736888906923256010615125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35930074170257365389947333 6736888906923256010615125)
            ·
              refine ⟨19736979219501726593599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6736888906923256010615125 19736979219501726593599)
              ·
                rfl

theorem cell23_3113448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 10].length) (baseStart_3113448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113448 prefixEnd_3113448 := by exact prefixLift 3113448
  have htrace : WordTrace (prefixWord ++ tailWord_3113448) baseStart_3113448 baseEnd_3113448 := by
    simpa [prefixWord, tailWord_3113448, baseEnd_3113448] using wordTrace_append hprefix tailTrace_3113448
  have hstable : (prefixWord ++ tailWord_3113448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113448).length < 2 ^ (prefixWord ++ tailWord_3113448).sum := by decide
  have hdescent : baseEnd_3113448 < baseStart_3113448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113459 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 1, 2, 2]
def baseStart_3113459 : Nat := 118140960795 + 3113459 * 2 ^ 59
def prefixEnd_3113459 : Nat := 4983230072969 + 3 ^ 40 * 3113459 * 2
def baseEnd_3113459 : Nat := 1598700965066839311043969

theorem tailTrace_3113459 : CollatzResearch.WordTrace tailWord_3113459 prefixEnd_3113459 1598700965066839311043969 := by
  unfold tailWord_3113459
  simp only [CollatzResearch.WordTrace]
  refine ⟨113557178827477254308607431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75704785884984836205738287 113557178827477254308607431)
  ·
    refine ⟨170335768241215881462911147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113557178827477254308607431 170335768241215881462911147)
    ·
      refine ⟨255503652361823822194366721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170335768241215881462911147 255503652361823822194366721)
      ·
        refine ⟨191627739271367866645775041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255503652361823822194366721 191627739271367866645775041)
        ·
          refine ⟨143720804453525899984331281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191627739271367866645775041 143720804453525899984331281)
          ·
            refine ⟨107790603340144424988248461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143720804453525899984331281 107790603340144424988248461)
            ·
              refine ⟨40421476252554159370593173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107790603340144424988248461 40421476252554159370593173)
              ·
                refine ⟨1894756699338476220496555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40421476252554159370593173 1894756699338476220496555)
                ·
                  refine ⟨2842135049007714330744833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894756699338476220496555 2842135049007714330744833)
                  ·
                    refine ⟨2131601286755785748058625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2842135049007714330744833 2131601286755785748058625)
                    ·
                      refine ⟨1598700965066839311043969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131601286755785748058625 1598700965066839311043969)
                      ·
                        rfl

theorem cell23_3113459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 2, 2].length) (baseStart_3113459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113459 prefixEnd_3113459 := by exact prefixLift 3113459
  have htrace : WordTrace (prefixWord ++ tailWord_3113459) baseStart_3113459 baseEnd_3113459 := by
    simpa [prefixWord, tailWord_3113459, baseEnd_3113459] using wordTrace_append hprefix tailTrace_3113459
  have hstable : (prefixWord ++ tailWord_3113459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113459).length < 2 ^ (prefixWord ++ tailWord_3113459).sum := by decide
  have hdescent : baseEnd_3113459 < baseStart_3113459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113479 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3113479 : Nat := 118140960795 + 3113479 * 2 ^ 59
def prefixEnd_3113479 : Nat := 4983230072969 + 3 ^ 40 * 3113479 * 2
def baseEnd_3113479 : Nat := 1598711234679929232793877

theorem tailTrace_3113479 : CollatzResearch.WordTrace tailWord_3113479 prefixEnd_3113479 1598711234679929232793877 := by
  unfold tailWord_3113479
  simp only [CollatzResearch.WordTrace]
  refine ⟨113557908287404797724335491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75705272191603198482890327 113557908287404797724335491)
  ·
    refine ⟨170336862431107196586503237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113557908287404797724335491 170336862431107196586503237)
    ·
      refine ⟨31938161705832599359969357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170336862431107196586503237 31938161705832599359969357)
      ·
        refine ⟨11976810639687224759988509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31938161705832599359969357 11976810639687224759988509)
        ·
          refine ⟨4491303989882709284995691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11976810639687224759988509 4491303989882709284995691)
          ·
            refine ⟨6736955984824063927493537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491303989882709284995691 6736955984824063927493537)
            ·
              refine ⟨5052716988618047945620153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6736955984824063927493537 5052716988618047945620153)
              ·
                refine ⟨3789537741463535959215115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052716988618047945620153 3789537741463535959215115)
                ·
                  refine ⟨5684306612195303938822673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789537741463535959215115 5684306612195303938822673)
                  ·
                    refine ⟨4263229959146477954117005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5684306612195303938822673 4263229959146477954117005)
                    ·
                      refine ⟨1598711234679929232793877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4263229959146477954117005 1598711234679929232793877)
                      ·
                        rfl

theorem cell23_3113479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3113479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113479 prefixEnd_3113479 := by exact prefixLift 3113479
  have htrace : WordTrace (prefixWord ++ tailWord_3113479) baseStart_3113479 baseEnd_3113479 := by
    simpa [prefixWord, tailWord_3113479, baseEnd_3113479] using wordTrace_append hprefix tailTrace_3113479
  have hstable : (prefixWord ++ tailWord_3113479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113479).length < 2 ^ (prefixWord ++ tailWord_3113479).sum := by decide
  have hdescent : baseEnd_3113479 < baseStart_3113479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113526 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3113526 : Nat := 118140960795 + 3113526 * 2 ^ 59
def prefixEnd_3113526 : Nat := 4983230072969 + 3 ^ 40 * 3113526 * 2
def baseEnd_3113526 : Nat := 1598735368270690548906161

theorem tailTrace_3113526 : CollatzResearch.WordTrace tailWord_3113526 prefixEnd_3113526 1598735368270690548906161 := by
  unfold tailWord_3113526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097476407389657796956027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75706415012156349834197621 7097476407389657796956027)
  ·
    refine ⟨10646214611084486695434041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097476407389657796956027 10646214611084486695434041)
    ·
      refine ⟨7984660958313365021575531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10646214611084486695434041 7984660958313365021575531)
      ·
        refine ⟨11976991437470047532363297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984660958313365021575531 11976991437470047532363297)
        ·
          refine ⟨8982743578102535649272473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11976991437470047532363297 8982743578102535649272473)
          ·
            refine ⟨6737057683576901736954355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8982743578102535649272473 6737057683576901736954355)
            ·
              refine ⟨10105586525365352605431533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737057683576901736954355 10105586525365352605431533)
              ·
                refine ⟨3789594947012007227036825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10105586525365352605431533 3789594947012007227036825)
                ·
                  refine ⟨2842196210259005420277619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789594947012007227036825 2842196210259005420277619)
                  ·
                    refine ⟨4263294315388508130416429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2842196210259005420277619 4263294315388508130416429)
                    ·
                      refine ⟨1598735368270690548906161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4263294315388508130416429 1598735368270690548906161)
                      ·
                        rfl

theorem cell23_3113526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3113526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113526 prefixEnd_3113526 := by exact prefixLift 3113526
  have htrace : WordTrace (prefixWord ++ tailWord_3113526) baseStart_3113526 baseEnd_3113526 := by
    simpa [prefixWord, tailWord_3113526, baseEnd_3113526] using wordTrace_append hprefix tailTrace_3113526
  have hstable : (prefixWord ++ tailWord_3113526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113526).length < 2 ^ (prefixWord ++ tailWord_3113526).sum := by decide
  have hdescent : baseEnd_3113526 < baseStart_3113526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113549 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3113549 : Nat := 118140960795 + 3113549 * 2 ^ 59
def prefixEnd_3113549 : Nat := 4983230072969 + 3 ^ 40 * 3113549 * 2
def baseEnd_3113549 : Nat := 1598747178325743958918555

theorem tailTrace_3113549 : CollatzResearch.WordTrace tailWord_3113549 prefixEnd_3113549 1598747178325743958918555 := by
  unfold tailWord_3113549
  simp only [CollatzResearch.WordTrace]
  refine ⟨113560461397151199679383701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75706974264767466452922467 113560461397151199679383701)
  ·
    refine ⟨5323146627991462484971111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113560461397151199679383701 5323146627991462484971111)
    ·
      refine ⟨7984719941987193727456667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5323146627991462484971111 7984719941987193727456667)
      ·
        refine ⟨11977079912980790591185001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984719941987193727456667 11977079912980790591185001)
        ·
          refine ⟨8982809934735592943388751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11977079912980790591185001 8982809934735592943388751)
          ·
            refine ⟨13474214902103389415083127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982809934735592943388751 13474214902103389415083127)
            ·
              refine ⟨20211322353155084122624691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13474214902103389415083127 20211322353155084122624691)
              ·
                refine ⟨30316983529732626183937037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20211322353155084122624691 30316983529732626183937037)
                ·
                  refine ⟨11368868823649734818976389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30316983529732626183937037 11368868823649734818976389)
                  ·
                    refine ⟨2131662904434325278558073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11368868823649734818976389 2131662904434325278558073)
                    ·
                      refine ⟨1598747178325743958918555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131662904434325278558073 1598747178325743958918555)
                      ·
                        rfl

theorem cell23_3113549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3113549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113549 prefixEnd_3113549 := by exact prefixLift 3113549
  have htrace : WordTrace (prefixWord ++ tailWord_3113549) baseStart_3113549 baseEnd_3113549 := by
    simpa [prefixWord, tailWord_3113549, baseEnd_3113549] using wordTrace_append hprefix tailTrace_3113549
  have hstable : (prefixWord ++ tailWord_3113549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113549).length < 2 ^ (prefixWord ++ tailWord_3113549).sum := by decide
  have hdescent : baseEnd_3113549 < baseStart_3113549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113572 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 5]
def baseStart_3113572 : Nat := 118140960795 + 3113572 * 2 ^ 59
def prefixEnd_3113572 : Nat := 4983230072969 + 3 ^ 40 * 3113572 * 2
def baseEnd_3113572 : Nat := 177639887597866374325661

theorem tailTrace_3113572 : CollatzResearch.WordTrace tailWord_3113572 prefixEnd_3113572 177639887597866374325661 := by
  unfold tailWord_3113572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56780650138033937303735485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75707533517378583071647313 56780650138033937303735485)
  ·
    refine ⟨21292743801762726488900807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56780650138033937303735485 21292743801762726488900807)
    ·
      refine ⟨31939115702644089733351211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21292743801762726488900807 31939115702644089733351211)
      ·
        refine ⟨47908673553966134600026817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31939115702644089733351211 47908673553966134600026817)
        ·
          refine ⟨35931505165474600950020113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47908673553966134600026817 35931505165474600950020113)
          ·
            refine ⟨26948628874105950712515085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35931505165474600950020113 26948628874105950712515085)
            ·
              refine ⟨10105735827789731517193157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26948628874105950712515085 10105735827789731517193157)
              ·
                refine ⟨1894825467710574659473717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10105735827789731517193157 1894825467710574659473717)
                ·
                  refine ⟨177639887597866374325661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894825467710574659473717 177639887597866374325661)
                  ·
                    rfl

theorem cell23_3113572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_3113572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113572 prefixEnd_3113572 := by exact prefixLift 3113572
  have htrace : WordTrace (prefixWord ++ tailWord_3113572) baseStart_3113572 baseEnd_3113572 := by
    simpa [prefixWord, tailWord_3113572, baseEnd_3113572] using wordTrace_append hprefix tailTrace_3113572
  have hstable : (prefixWord ++ tailWord_3113572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113572).length < 2 ^ (prefixWord ++ tailWord_3113572).sum := by decide
  have hdescent : baseEnd_3113572 < baseStart_3113572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113582 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3113582 : Nat := 118140960795 + 3113582 * 2 ^ 59
def prefixEnd_3113582 : Nat := 4983230072969 + 3 ^ 40 * 3113582 * 2
def baseEnd_3113582 : Nat := 1598764123187342329805903

theorem tailTrace_3113582 : CollatzResearch.WordTrace tailWord_3113582 prefixEnd_3113582 1598764123187342329805903 := by
  unfold tailWord_3113582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195208125753955789416875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75707776670687764210223333 14195208125753955789416875)
  ·
    refine ⟨21292812188630933684125313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14195208125753955789416875 21292812188630933684125313)
    ·
      refine ⟨15969609141473200263093985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21292812188630933684125313 15969609141473200263093985)
      ·
        refine ⟨11977206856104900197320489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15969609141473200263093985 11977206856104900197320489)
        ·
          refine ⟨8982905142078675147990367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11977206856104900197320489 8982905142078675147990367)
          ·
            refine ⟨13474357713118012721985551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8982905142078675147990367 13474357713118012721985551)
            ·
              refine ⟨20211536569677019082978327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13474357713118012721985551 20211536569677019082978327)
              ·
                refine ⟨30317304854515528624467491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20211536569677019082978327 30317304854515528624467491)
                ·
                  refine ⟨45475957281773292936701237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30317304854515528624467491 45475957281773292936701237)
                  ·
                    refine ⟨4263370995166246212815741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45475957281773292936701237 4263370995166246212815741)
                    ·
                      refine ⟨1598764123187342329805903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4263370995166246212815741 1598764123187342329805903)
                      ·
                        rfl

theorem cell23_3113582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3113582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113582 prefixEnd_3113582 := by exact prefixLift 3113582
  have htrace : WordTrace (prefixWord ++ tailWord_3113582) baseStart_3113582 baseEnd_3113582 := by
    simpa [prefixWord, tailWord_3113582, baseEnd_3113582] using wordTrace_append hprefix tailTrace_3113582
  have hstable : (prefixWord ++ tailWord_3113582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113582).length < 2 ^ (prefixWord ++ tailWord_3113582).sum := by decide
  have hdescent : baseEnd_3113582 < baseStart_3113582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113675 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 7, 5]
def baseStart_3113675 : Nat := 118140960795 + 3113675 * 2 ^ 59
def prefixEnd_3113675 : Nat := 4983230072969 + 3 ^ 40 * 3113675 * 2
def baseEnd_3113675 : Nat := 532937292296070155314325

theorem tailTrace_3113675 : CollatzResearch.WordTrace tailWord_3113675 prefixEnd_3113675 532937292296070155314325 := by
  unfold tailWord_3113675
  simp only [CollatzResearch.WordTrace]
  refine ⟨113565056994694723198470479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75710037996463148798980319 113565056994694723198470479)
  ·
    refine ⟨170347585492042084797705719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113565056994694723198470479 170347585492042084797705719)
    ·
      refine ⟨255521378238063127196558579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170347585492042084797705719 255521378238063127196558579)
      ·
        refine ⟨383282067357094690794837869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255521378238063127196558579 383282067357094690794837869)
        ·
          refine ⟨143730775258910509048064201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383282067357094690794837869 143730775258910509048064201)
          ·
            refine ⟨107798081444182881786048151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143730775258910509048064201 107798081444182881786048151)
            ·
              refine ⟨161697122166274322679072227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107798081444182881786048151 161697122166274322679072227)
              ·
                refine ⟨242545683249411484018608341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161697122166274322679072227 242545683249411484018608341)
                ·
                  refine ⟨5684664451158081656686133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242545683249411484018608341 5684664451158081656686133)
                  ·
                    refine ⟨532937292296070155314325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5684664451158081656686133 532937292296070155314325)
                    ·
                      rfl

theorem cell23_3113675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 5].length) (baseStart_3113675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113675 prefixEnd_3113675 := by exact prefixLift 3113675
  have htrace : WordTrace (prefixWord ++ tailWord_3113675) baseStart_3113675 baseEnd_3113675 := by
    simpa [prefixWord, tailWord_3113675, baseEnd_3113675] using wordTrace_append hprefix tailTrace_3113675
  have hstable : (prefixWord ++ tailWord_3113675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113675).length < 2 ^ (prefixWord ++ tailWord_3113675).sum := by decide
  have hdescent : baseEnd_3113675 < baseStart_3113675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113712 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_3113712 : Nat := 118140960795 + 3113712 * 2 ^ 59
def prefixEnd_3113712 : Nat := 4983230072969 + 3 ^ 40 * 3113712 * 2
def baseEnd_3113712 : Nat := 1598830875672426821180305

theorem tailTrace_3113712 : CollatzResearch.WordTrace tailWord_3113712 prefixEnd_3113712 1598830875672426821180305 := by
  unfold tailWord_3113712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56783203247780339258783695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75710937663707119011711593 56783203247780339258783695)
  ·
    refine ⟨85174804871670508888175543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56783203247780339258783695 85174804871670508888175543)
    ·
      refine ⟨127762207307505763332263315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85174804871670508888175543 127762207307505763332263315)
      ·
        refine ⟨191643310961258644998394973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127762207307505763332263315 191643310961258644998394973)
        ·
          refine ⟨71866241610471991874398115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191643310961258644998394973 71866241610471991874398115)
          ·
            refine ⟨107799362415707987811597173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71866241610471991874398115 107799362415707987811597173)
            ·
              refine ⟨10106190226472623857337235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107799362415707987811597173 10106190226472623857337235)
              ·
                refine ⟨15159285339708935786005853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10106190226472623857337235 15159285339708935786005853)
                ·
                  refine ⟨5684732002390850919752195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15159285339708935786005853 5684732002390850919752195)
                  ·
                    refine ⟨8527098003586276379628293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5684732002390850919752195 8527098003586276379628293)
                    ·
                      refine ⟨1598830875672426821180305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8527098003586276379628293 1598830875672426821180305)
                      ·
                        rfl

theorem cell23_3113712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_3113712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113712 prefixEnd_3113712 := by exact prefixLift 3113712
  have htrace : WordTrace (prefixWord ++ tailWord_3113712) baseStart_3113712 baseEnd_3113712 := by
    simpa [prefixWord, tailWord_3113712, baseEnd_3113712] using wordTrace_append hprefix tailTrace_3113712
  have hstable : (prefixWord ++ tailWord_3113712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113712).length < 2 ^ (prefixWord ++ tailWord_3113712).sum := by decide
  have hdescent : baseEnd_3113712 < baseStart_3113712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113722 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_3113722 : Nat := 118140960795 + 3113722 * 2 ^ 59
def prefixEnd_3113722 : Nat := 4983230072969 + 3 ^ 40 * 3113722 * 2
def baseEnd_3113722 : Nat := 532945336826323927351753

theorem tailTrace_3113722 : CollatzResearch.WordTrace tailWord_3113722 prefixEnd_3113722 532945336826323927351753 := by
  unfold tailWord_3113722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28391692806381112556357855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75711180817016300150287613 28391692806381112556357855)
  ·
    refine ⟨42587539209571668834536783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28391692806381112556357855 42587539209571668834536783)
    ·
      refine ⟨63881308814357503251805175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42587539209571668834536783 63881308814357503251805175)
      ·
        refine ⟨95821963221536254877707763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63881308814357503251805175 95821963221536254877707763)
        ·
          refine ⟨143732944832304382316561645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95821963221536254877707763 143732944832304382316561645)
          ·
            refine ⟨53899854312114143368710617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143732944832304382316561645 53899854312114143368710617)
            ·
              refine ⟨40424890734085607526532963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53899854312114143368710617 40424890734085607526532963)
              ·
                refine ⟨60637336101128411289799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40424890734085607526532963 60637336101128411289799445)
                ·
                  refine ⟨2842375129740394279209349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60637336101128411289799445 2842375129740394279209349)
                  ·
                    refine ⟨532945336826323927351753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842375129740394279209349 532945336826323927351753)
                    ·
                      rfl

theorem cell23_3113722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_3113722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113722 prefixEnd_3113722 := by exact prefixLift 3113722
  have htrace : WordTrace (prefixWord ++ tailWord_3113722) baseStart_3113722 baseEnd_3113722 := by
    simpa [prefixWord, tailWord_3113722, baseEnd_3113722] using wordTrace_append hprefix tailTrace_3113722
  have hstable : (prefixWord ++ tailWord_3113722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113722).length < 2 ^ (prefixWord ++ tailWord_3113722).sum := by decide
  have hdescent : baseEnd_3113722 < baseStart_3113722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113742 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3113742 : Nat := 118140960795 + 3113742 * 2 ^ 59
def prefixEnd_3113742 : Nat := 4983230072969 + 3 ^ 40 * 3113742 * 2
def baseEnd_3113742 : Nat := 1598846280092061703805167

theorem tailTrace_3113742 : CollatzResearch.WordTrace tailWord_3113742 prefixEnd_3113742 1598846280092061703805167 := by
  unfold tailWord_3113742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195937585681499205144935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75711667123634662427439653 14195937585681499205144935)
  ·
    refine ⟨21293906378522248807717403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14195937585681499205144935 21293906378522248807717403)
    ·
      refine ⟨31940859567783373211576105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293906378522248807717403 31940859567783373211576105)
      ·
        refine ⟨23955644675837529908682079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31940859567783373211576105 23955644675837529908682079)
        ·
          refine ⟨35933467013756294863023119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23955644675837529908682079 35933467013756294863023119)
          ·
            refine ⟨53900200520634442294534679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35933467013756294863023119 53900200520634442294534679)
            ·
              refine ⟨80850300780951663441802019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53900200520634442294534679 80850300780951663441802019)
              ·
                refine ⟨121275451171427495162703029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80850300780951663441802019 121275451171427495162703029)
                ·
                  refine ⟨11369573547321327671503409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121275451171427495162703029 11369573547321327671503409)
                  ·
                    refine ⟨8527180160490995753627557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11369573547321327671503409 8527180160490995753627557)
                    ·
                      refine ⟨1598846280092061703805167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8527180160490995753627557 1598846280092061703805167)
                      ·
                        rfl

theorem cell23_3113742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3113742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113742 prefixEnd_3113742 := by exact prefixLift 3113742
  have htrace : WordTrace (prefixWord ++ tailWord_3113742) baseStart_3113742 baseEnd_3113742 := by
    simpa [prefixWord, tailWord_3113742, baseEnd_3113742] using wordTrace_append hprefix tailTrace_3113742
  have hstable : (prefixWord ++ tailWord_3113742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113742).length < 2 ^ (prefixWord ++ tailWord_3113742).sum := by decide
  have hdescent : baseEnd_3113742 < baseStart_3113742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113759 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_3113759 : Nat := 118140960795 + 3113759 * 2 ^ 59
def prefixEnd_3113759 : Nat := 4983230072969 + 3 ^ 40 * 3113759 * 2
def baseEnd_3113759 : Nat := 1598855009263188137292589

theorem tailTrace_3113759 : CollatzResearch.WordTrace tailWord_3113759 prefixEnd_3113759 1598855009263188137292589 := by
  unfold tailWord_3113759
  simp only [CollatzResearch.WordTrace]
  refine ⟨113568120726390405544528331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75712080484260270363018887 113568120726390405544528331)
  ·
    refine ⟨170352181089585608316792497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113568120726390405544528331 170352181089585608316792497)
    ·
      refine ⟨127764135817189206237594373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170352181089585608316792497 127764135817189206237594373)
      ·
        refine ⟨23955775465722976169548945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127764135817189206237594373 23955775465722976169548945)
        ·
          refine ⟨17966831599292232127161709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23955775465722976169548945 17966831599292232127161709)
          ·
            refine ⟨6737561849734587047685641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17966831599292232127161709 6737561849734587047685641)
            ·
              refine ⟨5053171387300940285764231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6737561849734587047685641 5053171387300940285764231)
              ·
                refine ⟨7579757080951410428646347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053171387300940285764231 7579757080951410428646347)
                ·
                  refine ⟨11369635621427115642969521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7579757080951410428646347 11369635621427115642969521)
                  ·
                    refine ⟨8527226716070336732227141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11369635621427115642969521 8527226716070336732227141)
                    ·
                      refine ⟨1598855009263188137292589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8527226716070336732227141 1598855009263188137292589)
                      ·
                        rfl

theorem cell23_3113759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_3113759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113759 prefixEnd_3113759 := by exact prefixLift 3113759
  have htrace : WordTrace (prefixWord ++ tailWord_3113759) baseStart_3113759 baseEnd_3113759 := by
    simpa [prefixWord, tailWord_3113759, baseEnd_3113759] using wordTrace_append hprefix tailTrace_3113759
  have hstable : (prefixWord ++ tailWord_3113759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113759).length < 2 ^ (prefixWord ++ tailWord_3113759).sum := by decide
  have hdescent : baseEnd_3113759 < baseStart_3113759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113779 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3]
def baseStart_3113779 : Nat := 118140960795 + 3113779 * 2 ^ 59
def prefixEnd_3113779 : Nat := 4983230072969 + 3 ^ 40 * 3113779 * 2
def baseEnd_3113779 : Nat := 1598865278876278059042497

theorem tailTrace_3113779 : CollatzResearch.WordTrace tailWord_3113779 prefixEnd_3113779 1598865278876278059042497 := by
  unfold tailWord_3113779
  simp only [CollatzResearch.WordTrace]
  refine ⟨113568850186317948960256391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75712566790878632640170927 113568850186317948960256391)
  ·
    refine ⟨170353275279476923440384587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113568850186317948960256391 170353275279476923440384587)
    ·
      refine ⟨255529912919215385160576881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170353275279476923440384587 255529912919215385160576881)
      ·
        refine ⟨191647434689411538870432661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255529912919215385160576881 191647434689411538870432661)
        ·
          refine ⟨8983473501066165884551531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191647434689411538870432661 8983473501066165884551531)
          ·
            refine ⟨13475210251599248826827297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8983473501066165884551531 13475210251599248826827297)
            ·
              refine ⟨10106407688699436620120473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13475210251599248826827297 10106407688699436620120473)
              ·
                refine ⟨7579805766524577465090355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10106407688699436620120473 7579805766524577465090355)
                ·
                  refine ⟨11369708649786866197635533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7579805766524577465090355 11369708649786866197635533)
                  ·
                    refine ⟨4263640743670074824113325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11369708649786866197635533 4263640743670074824113325)
                    ·
                      refine ⟨1598865278876278059042497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4263640743670074824113325 1598865278876278059042497)
                      ·
                        rfl

theorem cell23_3113779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_3113779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113779 prefixEnd_3113779 := by exact prefixLift 3113779
  have htrace : WordTrace (prefixWord ++ tailWord_3113779) baseStart_3113779 baseEnd_3113779 := by
    simpa [prefixWord, tailWord_3113779, baseEnd_3113779] using wordTrace_append hprefix tailTrace_3113779
  have hstable : (prefixWord ++ tailWord_3113779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113779).length < 2 ^ (prefixWord ++ tailWord_3113779).sum := by decide
  have hdescent : baseEnd_3113779 < baseStart_3113779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113780 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3113780 : Nat := 118140960795 + 3113780 * 2 ^ 59
def prefixEnd_3113780 : Nat := 4983230072969 + 3 ^ 40 * 3113780 * 2
def baseEnd_3113780 : Nat := 1598865792356932555129993

theorem tailTrace_3113780 : CollatzResearch.WordTrace tailWord_3113780 prefixEnd_3113780 1598865792356932555129993 := by
  unfold tailWord_3113780
  simp only [CollatzResearch.WordTrace]
  refine ⟨56784443329657163065521397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75712591106209550754028529 56784443329657163065521397)
  ·
    refine ⟨5323541562155359037392631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56784443329657163065521397 5323541562155359037392631)
    ·
      refine ⟨7985312343233038556088947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5323541562155359037392631 7985312343233038556088947)
      ·
        refine ⟨11977968514849557834133421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985312343233038556088947 11977968514849557834133421)
        ·
          refine ⟨4491738193068584187800033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11977968514849557834133421 4491738193068584187800033)
          ·
            refine ⟨3368803644801438140850025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4491738193068584187800033 3368803644801438140850025)
            ·
              refine ⟨2526602733601078605637519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368803644801438140850025 2526602733601078605637519)
              ·
                refine ⟨3789904100401617908456279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526602733601078605637519 3789904100401617908456279)
                ·
                  refine ⟨5684856150602426862684419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789904100401617908456279 5684856150602426862684419)
                  ·
                    refine ⟨8527284225903640294026629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5684856150602426862684419 8527284225903640294026629)
                    ·
                      refine ⟨1598865792356932555129993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8527284225903640294026629 1598865792356932555129993)
                      ·
                        rfl

theorem cell23_3113780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3113780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113780 prefixEnd_3113780 := by exact prefixLift 3113780
  have htrace : WordTrace (prefixWord ++ tailWord_3113780) baseStart_3113780 baseEnd_3113780 := by
    simpa [prefixWord, tailWord_3113780, baseEnd_3113780] using wordTrace_append hprefix tailTrace_3113780
  have hstable : (prefixWord ++ tailWord_3113780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113780).length < 2 ^ (prefixWord ++ tailWord_3113780).sum := by decide
  have hdescent : baseEnd_3113780 < baseStart_3113780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113790 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_3113790 : Nat := 118140960795 + 3113790 * 2 ^ 59
def prefixEnd_3113790 : Nat := 4983230072969 + 3 ^ 40 * 3113790 * 2
def baseEnd_3113790 : Nat := 532956975721159172001649

theorem tailTrace_3113790 : CollatzResearch.WordTrace tailWord_3113790 prefixEnd_3113790 532956975721159172001649 := by
  unfold tailWord_3113790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14196156423659762229863353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75712834259518731892604549 14196156423659762229863353)
  ·
    refine ⟨10647117317744821672397515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14196156423659762229863353 10647117317744821672397515)
    ·
      refine ⟨15970675976617232508596273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10647117317744821672397515 15970675976617232508596273)
      ·
        refine ⟨11978006982462924381447205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15970675976617232508596273 11978006982462924381447205)
        ·
          refine ⟨2245876309211798321521351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11978006982462924381447205 2245876309211798321521351)
          ·
            refine ⟨3368814463817697482282027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245876309211798321521351 3368814463817697482282027)
            ·
              refine ⟨5053221695726546223423041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368814463817697482282027 5053221695726546223423041)
              ·
                refine ⟨3789916271794909667567281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053221695726546223423041 3789916271794909667567281)
                ·
                  refine ⟨2842437203846182250675461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789916271794909667567281 2842437203846182250675461)
                  ·
                    refine ⟨532956975721159172001649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842437203846182250675461 532956975721159172001649)
                    ·
                      rfl

theorem cell23_3113790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_3113790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113790 prefixEnd_3113790 := by exact prefixLift 3113790
  have htrace : WordTrace (prefixWord ++ tailWord_3113790) baseStart_3113790 baseEnd_3113790 := by
    simpa [prefixWord, tailWord_3113790, baseEnd_3113790] using wordTrace_append hprefix tailTrace_3113790
  have hstable : (prefixWord ++ tailWord_3113790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113790).length < 2 ^ (prefixWord ++ tailWord_3113790).sum := by decide
  have hdescent : baseEnd_3113790 < baseStart_3113790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113802 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3113802 : Nat := 118140960795 + 3113802 * 2 ^ 59
def prefixEnd_3113802 : Nat := 4983230072969 + 3 ^ 40 * 3113802 * 2
def baseEnd_3113802 : Nat := 1598877088931331469054891

theorem tailTrace_3113802 : CollatzResearch.WordTrace tailWord_3113802 prefixEnd_3113802 1598877088931331469054891 := by
  unfold tailWord_3113802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28392422266308655972085915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75713126043489749258895773 28392422266308655972085915)
  ·
    refine ⟨42588633399462983958128873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28392422266308655972085915 42588633399462983958128873)
    ·
      refine ⟨31941475049597237968596655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42588633399462983958128873 31941475049597237968596655)
      ·
        refine ⟨47912212574395856952894983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31941475049597237968596655 47912212574395856952894983)
        ·
          refine ⟨71868318861593785429342475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47912212574395856952894983 71868318861593785429342475)
          ·
            refine ⟨107802478292390678144013713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71868318861593785429342475 107802478292390678144013713)
            ·
              refine ⟨80851858719293008608010285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107802478292390678144013713 80851858719293008608010285)
              ·
                refine ⟨30319447019734878228003857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80851858719293008608010285 30319447019734878228003857)
                ·
                  refine ⟨22739585264801158671002893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30319447019734878228003857 22739585264801158671002893)
                  ·
                    refine ⟨8527344474300434501626085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22739585264801158671002893 8527344474300434501626085)
                    ·
                      refine ⟨1598877088931331469054891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8527344474300434501626085 1598877088931331469054891)
                      ·
                        rfl

theorem cell23_3113802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3113802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113802 prefixEnd_3113802 := by exact prefixLift 3113802
  have htrace : WordTrace (prefixWord ++ tailWord_3113802) baseStart_3113802 baseEnd_3113802 := by
    simpa [prefixWord, tailWord_3113802, baseEnd_3113802] using wordTrace_append hprefix tailTrace_3113802
  have hstable : (prefixWord ++ tailWord_3113802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113802).length < 2 ^ (prefixWord ++ tailWord_3113802).sum := by decide
  have hdescent : baseEnd_3113802 < baseStart_3113802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113813 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_3113813 : Nat := 118140960795 + 3113813 * 2 ^ 59
def prefixEnd_3113813 : Nat := 4983230072969 + 3 ^ 40 * 3113813 * 2
def baseEnd_3113813 : Nat := 1598882737218530926017341

theorem tailTrace_3113813 : CollatzResearch.WordTrace tailWord_3113813 prefixEnd_3113813 1598882737218530926017341 := by
  unfold tailWord_3113813
  simp only [CollatzResearch.WordTrace]
  refine ⟨113570090268194772766994093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75713393512129848511329395 113570090268194772766994093)
  ·
    refine ⟨42588783850573039787622785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113570090268194772766994093 42588783850573039787622785)
    ·
      refine ⟨31941587887929779840717089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42588783850573039787622785 31941587887929779840717089)
      ·
        refine ⟨23956190915947334880537817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31941587887929779840717089 23956190915947334880537817)
        ·
          refine ⟨17967143186960501160403363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23956190915947334880537817 17967143186960501160403363)
          ·
            refine ⟨26950714780440751740605045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17967143186960501160403363 26950714780440751740605045)
            ·
              refine ⟨2526629510666320475681723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26950714780440751740605045 2526629510666320475681723)
              ·
                refine ⟨3789944265999480713522585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526629510666320475681723 3789944265999480713522585)
                ·
                  refine ⟨2842458199499610535141939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789944265999480713522585 2842458199499610535141939)
                  ·
                    refine ⟨4263687299249415802712909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2842458199499610535141939 4263687299249415802712909)
                    ·
                      refine ⟨1598882737218530926017341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4263687299249415802712909 1598882737218530926017341)
                      ·
                        rfl

theorem cell23_3113813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_3113813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113813 prefixEnd_3113813 := by exact prefixLift 3113813
  have htrace : WordTrace (prefixWord ++ tailWord_3113813) baseStart_3113813 baseEnd_3113813 := by
    simpa [prefixWord, tailWord_3113813, baseEnd_3113813] using wordTrace_append hprefix tailTrace_3113813
  have hstable : (prefixWord ++ tailWord_3113813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113813).length < 2 ^ (prefixWord ++ tailWord_3113813).sum := by decide
  have hdescent : baseEnd_3113813 < baseStart_3113813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113836 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_3113836 : Nat := 118140960795 + 3113836 * 2 ^ 59
def prefixEnd_3113836 : Nat := 4983230072969 + 3 ^ 40 * 3113836 * 2
def baseEnd_3113836 : Nat := 1598894547273584336029735

theorem tailTrace_3113836 : CollatzResearch.WordTrace tailWord_3113836 prefixEnd_3113836 1598894547273584336029735 := by
  unfold tailWord_3113836
  simp only [CollatzResearch.WordTrace]
  refine ⟨56785464573555723847540681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75713952764740965130054241 56785464573555723847540681)
  ·
    refine ⟨42589098430166792885655511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56785464573555723847540681 42589098430166792885655511)
    ·
      refine ⟨63883647645250189328483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42589098430166792885655511 63883647645250189328483267)
      ·
        refine ⟨95825471467875283992724901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63883647645250189328483267 95825471467875283992724901)
        ·
          refine ⟨17967275900226615748635919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95825471467875283992724901 17967275900226615748635919)
          ·
            refine ⟨26950913850339923622953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17967275900226615748635919 26950913850339923622953879)
            ·
              refine ⟨40426370775509885434430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26950913850339923622953879 40426370775509885434430819)
              ·
                refine ⟨60639556163264828151646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40426370775509885434430819 60639556163264828151646229)
                ·
                  refine ⟨2842479195153038819608417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60639556163264828151646229 2842479195153038819608417)
                  ·
                    refine ⟨2131859396364779114706313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2842479195153038819608417 2131859396364779114706313)
                    ·
                      refine ⟨1598894547273584336029735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131859396364779114706313 1598894547273584336029735)
                      ·
                        rfl

theorem cell23_3113836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_3113836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113836 prefixEnd_3113836 := by exact prefixLift 3113836
  have htrace : WordTrace (prefixWord ++ tailWord_3113836) baseStart_3113836 baseEnd_3113836 := by
    simpa [prefixWord, tailWord_3113836, baseEnd_3113836] using wordTrace_append hprefix tailTrace_3113836
  have hstable : (prefixWord ++ tailWord_3113836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113836).length < 2 ^ (prefixWord ++ tailWord_3113836).sum := by decide
  have hdescent : baseEnd_3113836 < baseStart_3113836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113842 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3113842 : Nat := 118140960795 + 3113842 * 2 ^ 59
def prefixEnd_3113842 : Nat := 4983230072969 + 3 ^ 40 * 3113842 * 2
def baseEnd_3113842 : Nat := 177655292017501256950523

theorem tailTrace_3113842 : CollatzResearch.WordTrace tailWord_3113842 prefixEnd_3113842 177655292017501256950523 := by
  unfold tailWord_3113842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28392786996272427679949945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75714098656726473813199853 28392786996272427679949945)
  ·
    refine ⟨21294590247204320759962459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28392786996272427679949945 21294590247204320759962459)
    ·
      refine ⟨31941885370806481139943689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21294590247204320759962459 31941885370806481139943689)
      ·
        refine ⟨23956414028104860854957767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31941885370806481139943689 23956414028104860854957767)
        ·
          refine ⟨35934621042157291282436651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23956414028104860854957767 35934621042157291282436651)
          ·
            refine ⟨53901931563235936923654977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35934621042157291282436651 53901931563235936923654977)
            ·
              refine ⟨40426448672426952692741233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53901931563235936923654977 40426448672426952692741233)
              ·
                refine ⟨30319836504320214519555925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40426448672426952692741233 30319836504320214519555925)
                ·
                  refine ⟨177655292017501256950523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30319836504320214519555925 177655292017501256950523)
                  ·
                    rfl

theorem cell23_3113842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3113842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113842 prefixEnd_3113842 := by exact prefixLift 3113842
  have htrace : WordTrace (prefixWord ++ tailWord_3113842) baseStart_3113842 baseEnd_3113842 := by
    simpa [prefixWord, tailWord_3113842, baseEnd_3113842] using wordTrace_append hprefix tailTrace_3113842
  have hstable : (prefixWord ++ tailWord_3113842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113842).length < 2 ^ (prefixWord ++ tailWord_3113842).sum := by decide
  have hdescent : baseEnd_3113842 < baseStart_3113842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113946 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_3113946 : Nat := 118140960795 + 3113946 * 2 ^ 59
def prefixEnd_3113946 : Nat := 4983230072969 + 3 ^ 40 * 3113946 * 2
def baseEnd_3113946 : Nat := 1598951030145578905654229

theorem tailTrace_3113946 : CollatzResearch.WordTrace tailWord_3113946 prefixEnd_3113946 1598951030145578905654229 := by
  unfold tailWord_3113946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393735294178234120396423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75716627451141957654390461 28393735294178234120396423)
  ·
    refine ⟨42590602941267351180594635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28393735294178234120396423 42590602941267351180594635)
    ·
      refine ⟨63885904411901026770891953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42590602941267351180594635 63885904411901026770891953)
      ·
        refine ⟨47914428308925770078168965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63885904411901026770891953 47914428308925770078168965)
        ·
          refine ⟨8983955307923581889656681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47914428308925770078168965 8983955307923581889656681)
          ·
            refine ⟨6737966480942686417242511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8983955307923581889656681 6737966480942686417242511)
            ·
              refine ⟨10106949721414029625863767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737966480942686417242511 10106949721414029625863767)
              ·
                refine ⟨15160424582121044438795651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10106949721414029625863767 15160424582121044438795651)
                ·
                  refine ⟨22740636873181566658193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15160424582121044438795651 22740636873181566658193477)
                  ·
                    refine ⟨4263869413721543748411277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22740636873181566658193477 4263869413721543748411277)
                    ·
                      refine ⟨1598951030145578905654229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4263869413721543748411277 1598951030145578905654229)
                      ·
                        rfl

theorem cell23_3113946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_3113946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113946 prefixEnd_3113946 := by exact prefixLift 3113946
  have htrace : WordTrace (prefixWord ++ tailWord_3113946) baseStart_3113946 baseEnd_3113946 := by
    simpa [prefixWord, tailWord_3113946, baseEnd_3113946] using wordTrace_append hprefix tailTrace_3113946
  have hstable : (prefixWord ++ tailWord_3113946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113946).length < 2 ^ (prefixWord ++ tailWord_3113946).sum := by decide
  have hdescent : baseEnd_3113946 < baseStart_3113946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113966 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_3113966 : Nat := 118140960795 + 3113966 * 2 ^ 59
def prefixEnd_3113966 : Nat := 4983230072969 + 3 ^ 40 * 3113966 * 2
def baseEnd_3113966 : Nat := 177662366639852091933793

theorem tailTrace_3113966 : CollatzResearch.WordTrace tailWord_3113966 prefixEnd_3113966 177662366639852091933793 := by
  unfold tailWord_3113966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14196958829580059987164219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75717113757760319931542501 14196958829580059987164219)
  ·
    refine ⟨21295438244370089980746329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14196958829580059987164219 21295438244370089980746329)
    ·
      refine ⟨15971578683277567485559747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21295438244370089980746329 15971578683277567485559747)
      ·
        refine ⟨23957368024916351228339621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15971578683277567485559747 23957368024916351228339621)
        ·
          refine ⟨4492006504671815855313679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23957368024916351228339621 4492006504671815855313679)
          ·
            refine ⟨6738009757007723782970519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492006504671815855313679 6738009757007723782970519)
            ·
              refine ⟨10107014635511585674455779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738009757007723782970519 10107014635511585674455779)
              ·
                refine ⟨15160521953267378511683669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107014635511585674455779 15160521953267378511683669)
                ·
                  refine ⟨177662366639852091933793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15160521953267378511683669 177662366639852091933793)
                  ·
                    rfl

theorem cell23_3113966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_3113966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113966 prefixEnd_3113966 := by exact prefixLift 3113966
  have htrace : WordTrace (prefixWord ++ tailWord_3113966) baseStart_3113966 baseEnd_3113966 := by
    simpa [prefixWord, tailWord_3113966, baseEnd_3113966] using wordTrace_append hprefix tailTrace_3113966
  have hstable : (prefixWord ++ tailWord_3113966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113966).length < 2 ^ (prefixWord ++ tailWord_3113966).sum := by decide
  have hdescent : baseEnd_3113966 < baseStart_3113966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113969 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_3113969 : Nat := 118140960795 + 3113969 * 2 ^ 59
def prefixEnd_3113969 : Nat := 4983230072969 + 3 ^ 40 * 3113969 * 2
def baseEnd_3113969 : Nat := 1598962840200632315666623

theorem tailTrace_3113969 : CollatzResearch.WordTrace tailWord_3113969 prefixEnd_3113969 1598962840200632315666623 := by
  unfold tailWord_3113969
  simp only [CollatzResearch.WordTrace]
  refine ⟨113575780055629611409672961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75717186703753074273115307 113575780055629611409672961)
  ·
    refine ⟨85181835041722208557254721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113575780055629611409672961 85181835041722208557254721)
    ·
      refine ⟨63886376281291656417941041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85181835041722208557254721 63886376281291656417941041)
      ·
        refine ⟨47914782210968742313455781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63886376281291656417941041 47914782210968742313455781)
        ·
          refine ⟨8984021664556639183772959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47914782210968742313455781 8984021664556639183772959)
          ·
            refine ⟨13476032496834958775659439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984021664556639183772959 13476032496834958775659439)
            ·
              refine ⟨20214048745252438163489159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476032496834958775659439 20214048745252438163489159)
              ·
                refine ⟨30321073117878657245233739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20214048745252438163489159 30321073117878657245233739)
                ·
                  refine ⟨45481609676817985867850609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30321073117878657245233739 45481609676817985867850609)
                  ·
                    refine ⟨34111207257613489400887957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45481609676817985867850609 34111207257613489400887957)
                    ·
                      refine ⟨1598962840200632315666623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34111207257613489400887957 1598962840200632315666623)
                      ·
                        rfl

theorem cell23_3113969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_3113969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113969 prefixEnd_3113969 := by exact prefixLift 3113969
  have htrace : WordTrace (prefixWord ++ tailWord_3113969) baseStart_3113969 baseEnd_3113969 := by
    simpa [prefixWord, tailWord_3113969, baseEnd_3113969] using wordTrace_append hprefix tailTrace_3113969
  have hstable : (prefixWord ++ tailWord_3113969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113969).length < 2 ^ (prefixWord ++ tailWord_3113969).sum := by decide
  have hdescent : baseEnd_3113969 < baseStart_3113969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113970 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3113970 : Nat := 118140960795 + 3113970 * 2 ^ 59
def prefixEnd_3113970 : Nat := 4983230072969 + 3 ^ 40 * 3113970 * 2
def baseEnd_3113970 : Nat := 532987784560428937251373

theorem tailTrace_3113970 : CollatzResearch.WordTrace tailWord_3113970 prefixEnd_3113970 532987784560428937251373 := by
  unfold tailWord_3113970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393954132156497145114841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75717211019083992386972909 28393954132156497145114841)
  ·
    refine ⟨21295465599117372858836131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28393954132156497145114841 21295465599117372858836131)
    ·
      refine ⟨31943198398676059288254197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21295465599117372858836131 31943198398676059288254197)
      ·
        refine ⟨2994674849875880558273831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31943198398676059288254197 2994674849875880558273831)
        ·
          refine ⟨4492012274813820837410747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994674849875880558273831 4492012274813820837410747)
          ·
            refine ⟨6738018412220731256116121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492012274813820837410747 6738018412220731256116121)
            ·
              refine ⟨5053513809165548442087091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6738018412220731256116121 5053513809165548442087091)
              ·
                refine ⟨7580270713748322663130637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053513809165548442087091 7580270713748322663130637)
                ·
                  refine ⟨2842601517655620998673989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7580270713748322663130637 2842601517655620998673989)
                  ·
                    refine ⟨532987784560428937251373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842601517655620998673989 532987784560428937251373)
                    ·
                      rfl

theorem cell23_3113970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3113970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113970 prefixEnd_3113970 := by exact prefixLift 3113970
  have htrace : WordTrace (prefixWord ++ tailWord_3113970) baseStart_3113970 baseEnd_3113970 := by
    simpa [prefixWord, tailWord_3113970, baseEnd_3113970] using wordTrace_append hprefix tailTrace_3113970
  have hstable : (prefixWord ++ tailWord_3113970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113970).length < 2 ^ (prefixWord ++ tailWord_3113970).sum := by decide
  have hdescent : baseEnd_3113970 < baseStart_3113970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113996 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_3113996 : Nat := 118140960795 + 3113996 * 2 ^ 59
def prefixEnd_3113996 : Nat := 4983230072969 + 3 ^ 40 * 3113996 * 2
def baseEnd_3113996 : Nat := 532992234726101236676333

theorem tailTrace_3113996 : CollatzResearch.WordTrace tailWord_3113996 prefixEnd_3113996 532992234726101236676333 := by
  unfold tailWord_3113996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56788382413265897510452921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75717843217687863347270561 56788382413265897510452921)
  ·
    refine ⟨42591286809949423132839691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56788382413265897510452921 42591286809949423132839691)
    ·
      refine ⟨63886930214924134699259537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42591286809949423132839691 63886930214924134699259537)
      ·
        refine ⟨47915197661193101024444653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63886930214924134699259537 47915197661193101024444653)
        ·
          refine ⟨17968199122947412884166745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47915197661193101024444653 17968199122947412884166745)
          ·
            refine ⟨13476149342210559663125059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17968199122947412884166745 13476149342210559663125059)
            ·
              refine ⟨20214224013315839494687589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476149342210559663125059 20214224013315839494687589)
              ·
                refine ⟨3790167002496719905253923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20214224013315839494687589 3790167002496719905253923)
                ·
                  refine ⟨5685250503745079857880885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790167002496719905253923 5685250503745079857880885)
                  ·
                    refine ⟨532992234726101236676333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5685250503745079857880885 532992234726101236676333)
                    ·
                      rfl

theorem cell23_3113996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_3113996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3113996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3113996 prefixEnd_3113996 := by exact prefixLift 3113996
  have htrace : WordTrace (prefixWord ++ tailWord_3113996) baseStart_3113996 baseEnd_3113996 := by
    simpa [prefixWord, tailWord_3113996, baseEnd_3113996] using wordTrace_append hprefix tailTrace_3113996
  have hstable : (prefixWord ++ tailWord_3113996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113996).length < 2 ^ (prefixWord ++ tailWord_3113996).sum := by decide
  have hdescent : baseEnd_3113996 < baseStart_3113996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114009 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_3114009 : Nat := 118140960795 + 3114009 * 2 ^ 59
def prefixEnd_3114009 : Nat := 4983230072969 + 3 ^ 40 * 3114009 * 2
def baseEnd_3114009 : Nat := 532994459808937386388813

theorem tailTrace_3114009 : CollatzResearch.WordTrace tailWord_3114009 prefixEnd_3114009 532994459808937386388813 := by
  unfold tailWord_3114009
  simp only [CollatzResearch.WordTrace]
  refine ⟨113577238975484698241129081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75718159316989798827419387 113577238975484698241129081)
  ·
    refine ⟨85182929231613523680846811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113577238975484698241129081 85182929231613523680846811)
    ·
      refine ⟨127774393847420285521270217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85182929231613523680846811 127774393847420285521270217)
      ·
        refine ⟨95830795385565214140952663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127774393847420285521270217 95830795385565214140952663)
        ·
          refine ⟨143746193078347821211428995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95830795385565214140952663 143746193078347821211428995)
          ·
            refine ⟨215619289617521731817143493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143746193078347821211428995 215619289617521731817143493)
            ·
              refine ⟨40428616803285324715714405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215619289617521731817143493 40428616803285324715714405)
              ·
                refine ⟨7580365650615998384196451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40428616803285324715714405 7580365650615998384196451)
                ·
                  refine ⟨11370548475923997576294677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7580365650615998384196451 11370548475923997576294677)
                  ·
                    refine ⟨532994459808937386388813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11370548475923997576294677 532994459808937386388813)
                    ·
                      rfl

theorem cell23_3114009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_3114009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114009 prefixEnd_3114009 := by exact prefixLift 3114009
  have htrace : WordTrace (prefixWord ++ tailWord_3114009) baseStart_3114009 baseEnd_3114009 := by
    simpa [prefixWord, tailWord_3114009, baseEnd_3114009] using wordTrace_append hprefix tailTrace_3114009
  have hstable : (prefixWord ++ tailWord_3114009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114009).length < 2 ^ (prefixWord ++ tailWord_3114009).sum := by decide
  have hdescent : baseEnd_3114009 < baseStart_3114009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114020 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3114020 : Nat := 118140960795 + 3114020 * 2 ^ 59
def prefixEnd_3114020 : Nat := 4983230072969 + 3 ^ 40 * 3114020 * 2
def baseEnd_3114020 : Nat := 1598989027714011616128889

theorem tailTrace_3114020 : CollatzResearch.WordTrace tailWord_3114020 prefixEnd_3114020 1598989027714011616128889 := by
  unfold tailWord_3114020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56788820089222423559889757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75718426785629898079853009 56788820089222423559889757)
  ·
    refine ⟨21295807533458408834958659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56788820089222423559889757 21295807533458408834958659)
    ·
      refine ⟨31943711300187613252437989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21295807533458408834958659 31943711300187613252437989)
      ·
        refine ⟨5989445868785177484832123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31943711300187613252437989 5989445868785177484832123)
        ·
          refine ⟨8984168803177766227248185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989445868785177484832123 8984168803177766227248185)
          ·
            refine ⟨6738126602383324670436139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8984168803177766227248185 6738126602383324670436139)
            ·
              refine ⟨10107189903574987005654209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738126602383324670436139 10107189903574987005654209)
              ·
                refine ⟨7580392427681240254240657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10107189903574987005654209 7580392427681240254240657)
                ·
                  refine ⟨5685294320760930190680493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7580392427681240254240657 5685294320760930190680493)
                  ·
                    refine ⟨2131985370285348821505185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5685294320760930190680493 2131985370285348821505185)
                    ·
                      refine ⟨1598989027714011616128889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2131985370285348821505185 1598989027714011616128889)
                      ·
                        rfl

theorem cell23_3114020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3114020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114020 prefixEnd_3114020 := by exact prefixLift 3114020
  have htrace : WordTrace (prefixWord ++ tailWord_3114020) baseStart_3114020 baseEnd_3114020 := by
    simpa [prefixWord, tailWord_3114020, baseEnd_3114020] using wordTrace_append hprefix tailTrace_3114020
  have hstable : (prefixWord ++ tailWord_3114020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114020).length < 2 ^ (prefixWord ++ tailWord_3114020).sum := by decide
  have hdescent : baseEnd_3114020 < baseStart_3114020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114053 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_3114053 : Nat := 118140960795 + 3114053 * 2 ^ 59
def prefixEnd_3114053 : Nat := 4983230072969 + 3 ^ 40 * 3114053 * 2
def baseEnd_3114053 : Nat := 1599005972575609987016237

theorem tailTrace_3114053 : CollatzResearch.WordTrace tailWord_3114053 prefixEnd_3114053 1599005972575609987016237 := by
  unfold tailWord_3114053
  simp only [CollatzResearch.WordTrace]
  refine ⟨113578843787325293755730813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75719229191550195837153875 113578843787325293755730813)
  ·
    refine ⟨42592066420246985158399055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113578843787325293755730813 42592066420246985158399055)
    ·
      refine ⟨63888099630370477737598583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592066420246985158399055 63888099630370477737598583)
      ·
        refine ⟨95832149445555716606397875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63888099630370477737598583 95832149445555716606397875)
        ·
          refine ⟨143748224168333574909596813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95832149445555716606397875 143748224168333574909596813)
          ·
            refine ⟨53905584063125090591098805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143748224168333574909596813 53905584063125090591098805)
            ·
              refine ⟨5053648505917977242915513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53905584063125090591098805 5053648505917977242915513)
              ·
                refine ⟨3790236379438482932186635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053648505917977242915513 3790236379438482932186635)
                ·
                  refine ⟨5685354569157724398279953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790236379438482932186635 5685354569157724398279953)
                  ·
                    refine ⟨4264015926868293298709965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5685354569157724398279953 4264015926868293298709965)
                    ·
                      refine ⟨1599005972575609987016237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4264015926868293298709965 1599005972575609987016237)
                      ·
                        rfl

theorem cell23_3114053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_3114053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114053 prefixEnd_3114053 := by exact prefixLift 3114053
  have htrace : WordTrace (prefixWord ++ tailWord_3114053) baseStart_3114053 baseEnd_3114053 := by
    simpa [prefixWord, tailWord_3114053, baseEnd_3114053] using wordTrace_append hprefix tailTrace_3114053
  have hstable : (prefixWord ++ tailWord_3114053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114053).length < 2 ^ (prefixWord ++ tailWord_3114053).sum := by decide
  have hdescent : baseEnd_3114053 < baseStart_3114053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114077 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3114077 : Nat := 118140960795 + 3114077 * 2 ^ 59
def prefixEnd_3114077 : Nat := 4983230072969 + 3 ^ 40 * 3114077 * 2
def baseEnd_3114077 : Nat := 533006098703772631038709

theorem tailTrace_3114077 : CollatzResearch.WordTrace tailWord_3114077 prefixEnd_3114077 533006098703772631038709 := by
  unfold tailWord_3114077
  simp only [CollatzResearch.WordTrace]
  refine ⟨113579719139238345854604485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75719812759492230569736323 113579719139238345854604485)
  ·
    refine ⟨21296197338607189847738341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113579719139238345854604485 21296197338607189847738341)
    ·
      refine ⟨3993037000988848096450939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21296197338607189847738341 3993037000988848096450939)
      ·
        refine ⟨5989555501483272144676409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993037000988848096450939 5989555501483272144676409)
        ·
          refine ⟨4492166626112454108507307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5989555501483272144676409 4492166626112454108507307)
          ·
            refine ⟨6738249939168681162760961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492166626112454108507307 6738249939168681162760961)
            ·
              refine ⟨5053687454376510872070721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6738249939168681162760961 5053687454376510872070721)
              ·
                refine ⟨3790265590782383154053041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053687454376510872070721 3790265590782383154053041)
                ·
                  refine ⟨2842699193086787365539781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790265590782383154053041 2842699193086787365539781)
                  ·
                    refine ⟨533006098703772631038709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842699193086787365539781 533006098703772631038709)
                    ·
                      rfl

theorem cell23_3114077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3114077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114077 prefixEnd_3114077 := by exact prefixLift 3114077
  have htrace : WordTrace (prefixWord ++ tailWord_3114077) baseStart_3114077 baseEnd_3114077 := by
    simpa [prefixWord, tailWord_3114077, baseEnd_3114077] using wordTrace_append hprefix tailTrace_3114077
  have hstable : (prefixWord ++ tailWord_3114077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114077).length < 2 ^ (prefixWord ++ tailWord_3114077).sum := by decide
  have hdescent : baseEnd_3114077 < baseStart_3114077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114078 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3114078 : Nat := 118140960795 + 3114078 * 2 ^ 59
def prefixEnd_3114078 : Nat := 4983230072969 + 3 ^ 40 * 3114078 * 2
def baseEnd_3114078 : Nat := 1599018809591972389203623

theorem tailTrace_3114078 : CollatzResearch.WordTrace tailWord_3114078 prefixEnd_3114078 1599018809591972389203623 := by
  unfold tailWord_3114078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197469451529340378173861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75719837074823148683593925 14197469451529340378173861)
  ·
    refine ⟨2662025522161751320907599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14197469451529340378173861 2662025522161751320907599)
    ·
      refine ⟨3993038283242626981361399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2662025522161751320907599 3993038283242626981361399)
      ·
        refine ⟨5989557424863940472042099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993038283242626981361399 5989557424863940472042099)
        ·
          refine ⟨8984336137295910708063149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989557424863940472042099 8984336137295910708063149)
          ·
            refine ⟨3369126051485966515523681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8984336137295910708063149 3369126051485966515523681)
            ·
              refine ⟨2526844538614474886642761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3369126051485966515523681 2526844538614474886642761)
              ·
                refine ⟨1895133403960856164982071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526844538614474886642761 1895133403960856164982071)
                ·
                  refine ⟨2842700105941284247473107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895133403960856164982071 2842700105941284247473107)
                  ·
                    refine ⟨4264050158911926371209661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2842700105941284247473107 4264050158911926371209661)
                    ·
                      refine ⟨1599018809591972389203623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4264050158911926371209661 1599018809591972389203623)
                      ·
                        rfl

theorem cell23_3114078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3114078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114078 prefixEnd_3114078 := by exact prefixLift 3114078
  have htrace : WordTrace (prefixWord ++ tailWord_3114078) baseStart_3114078 baseEnd_3114078 := by
    simpa [prefixWord, tailWord_3114078, baseEnd_3114078] using wordTrace_append hprefix tailTrace_3114078
  have hstable : (prefixWord ++ tailWord_3114078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114078).length < 2 ^ (prefixWord ++ tailWord_3114078).sum := by decide
  have hdescent : baseEnd_3114078 < baseStart_3114078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114156 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_3114156 : Nat := 118140960795 + 3114156 * 2 ^ 59
def prefixEnd_3114156 : Nat := 4983230072969 + 3 ^ 40 * 3114156 * 2
def baseEnd_3114156 : Nat := 1599058861083023084028263

theorem tailTrace_3114156 : CollatzResearch.WordTrace tailWord_3114156 prefixEnd_3114156 1599058861083023084028263 := by
  unfold tailWord_3114156
  simp only [CollatzResearch.WordTrace]
  refine ⟨56791300252976071173365161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75721733670634761564486881 56791300252976071173365161)
  ·
    refine ⟨42593475189732053380023871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56791300252976071173365161 42593475189732053380023871)
    ·
      refine ⟨63890212784598080070035807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42593475189732053380023871 63890212784598080070035807)
      ·
        refine ⟨95835319176897120105053711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63890212784598080070035807 95835319176897120105053711)
        ·
          refine ⟨143752978765345680157580567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95835319176897120105053711 143752978765345680157580567)
          ·
            refine ⟨215629468148018520236370851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143752978765345680157580567 215629468148018520236370851)
            ·
              refine ⟨323444202222027780354556277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215629468148018520236370851 323444202222027780354556277)
              ·
                refine ⟨30322893958315104408239651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323444202222027780354556277 30322893958315104408239651)
                ·
                  refine ⟨45484340937472656612359477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30322893958315104408239651 45484340937472656612359477)
                  ·
                    refine ⟨4264156962888061557408701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45484340937472656612359477 4264156962888061557408701)
                    ·
                      refine ⟨1599058861083023084028263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4264156962888061557408701 1599058861083023084028263)
                      ·
                        rfl

theorem cell23_3114156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_3114156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114156 prefixEnd_3114156 := by exact prefixLift 3114156
  have htrace : WordTrace (prefixWord ++ tailWord_3114156) baseStart_3114156 baseEnd_3114156 := by
    simpa [prefixWord, tailWord_3114156, baseEnd_3114156] using wordTrace_append hprefix tailTrace_3114156
  have hstable : (prefixWord ++ tailWord_3114156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114156).length < 2 ^ (prefixWord ++ tailWord_3114156).sum := by decide
  have hdescent : baseEnd_3114156 < baseStart_3114156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114197 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 5]
def baseStart_3114197 : Nat := 118140960795 + 3114197 * 2 ^ 59
def prefixEnd_3114197 : Nat := 4983230072969 + 3 ^ 40 * 3114197 * 2
def baseEnd_3114197 : Nat := 177675545976650824846175

theorem tailTrace_3114197 : CollatzResearch.WordTrace tailWord_3114197 prefixEnd_3114197 177675545976650824846175 := by
  unfold tailWord_3114197
  simp only [CollatzResearch.WordTrace]
  refine ⟨113584095898803606348972845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75722730599202404232648563 113584095898803606348972845)
  ·
    refine ⟨42594035962051352380864817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113584095898803606348972845 42594035962051352380864817)
    ·
      refine ⟨31945526971538514285648613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42594035962051352380864817 31945526971538514285648613)
      ·
        refine ⟨5989786307163471428559115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31945526971538514285648613 5989786307163471428559115)
        ·
          refine ⟨8984679460745207142838673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989786307163471428559115 8984679460745207142838673)
          ·
            refine ⟨6738509595558905357129005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8984679460745207142838673 6738509595558905357129005)
            ·
              refine ⟨2526941098334589508923377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6738509595558905357129005 2526941098334589508923377)
              ·
                refine ⟨1895205823750942131692533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526941098334589508923377 1895205823750942131692533)
                ·
                  refine ⟨177675545976650824846175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895205823750942131692533 177675545976650824846175)
                  ·
                    rfl

theorem cell23_3114197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_3114197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114197 prefixEnd_3114197 := by exact prefixLift 3114197
  have htrace : WordTrace (prefixWord ++ tailWord_3114197) baseStart_3114197 baseEnd_3114197 := by
    simpa [prefixWord, tailWord_3114197, baseEnd_3114197] using wordTrace_append hprefix tailTrace_3114197
  have hstable : (prefixWord ++ tailWord_3114197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114197).length < 2 ^ (prefixWord ++ tailWord_3114197).sum := by decide
  have hdescent : baseEnd_3114197 < baseStart_3114197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114230 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3114230 : Nat := 118140960795 + 3114230 * 2 ^ 59
def prefixEnd_3114230 : Nat := 4983230072969 + 3 ^ 40 * 3114230 * 2
def baseEnd_3114230 : Nat := 1599096858651455794502923

theorem tailTrace_3114230 : CollatzResearch.WordTrace tailWord_3114230 prefixEnd_3114230 1599096858651455794502923 := by
  unfold tailWord_3114230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7099081219230253311557759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75723533005122701989949429 7099081219230253311557759)
  ·
    refine ⟨10648621828845379967336639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7099081219230253311557759 10648621828845379967336639)
    ·
      refine ⟨15972932743268069951004959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10648621828845379967336639 15972932743268069951004959)
      ·
        refine ⟨23959399114902104926507439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15972932743268069951004959 23959399114902104926507439)
        ·
          refine ⟨35939098672353157389761159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959399114902104926507439 35939098672353157389761159)
          ·
            refine ⟨53908648008529736084641739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35939098672353157389761159 53908648008529736084641739)
            ·
              refine ⟨80862972012794604126962609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53908648008529736084641739 80862972012794604126962609)
              ·
                refine ⟨60647229009595953095221957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80862972012794604126962609 60647229009595953095221957)
                ·
                  refine ⟨11371355439299241205354117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60647229009595953095221957 11371355439299241205354117)
                  ·
                    refine ⟨2132129144868607726003897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11371355439299241205354117 2132129144868607726003897)
                    ·
                      refine ⟨1599096858651455794502923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132129144868607726003897 1599096858651455794502923)
                      ·
                        rfl

theorem cell23_3114230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3114230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114230 prefixEnd_3114230 := by exact prefixLift 3114230
  have htrace : WordTrace (prefixWord ++ tailWord_3114230) baseStart_3114230 baseEnd_3114230 := by
    simpa [prefixWord, tailWord_3114230, baseEnd_3114230] using wordTrace_append hprefix tailTrace_3114230
  have hstable : (prefixWord ++ tailWord_3114230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114230).length < 2 ^ (prefixWord ++ tailWord_3114230).sum := by decide
  have hdescent : baseEnd_3114230 < baseStart_3114230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114240 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 1, 4]
def baseStart_3114240 : Nat := 118140960795 + 3114240 * 2 ^ 59
def prefixEnd_3114240 : Nat := 4983230072969 + 3 ^ 40 * 3114240 * 2
def baseEnd_3114240 : Nat := 533033997819333585125959

theorem tailTrace_3114240 : CollatzResearch.WordTrace tailWord_3114240 prefixEnd_3114240 533033997819333585125959 := by
  unfold tailWord_3114240
  simp only [CollatzResearch.WordTrace]
  refine ⟨56792832118823912346394087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75723776158431883128525449 56792832118823912346394087)
  ·
    refine ⟨85189248178235868519591131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56792832118823912346394087 85189248178235868519591131)
    ·
      refine ⟨127783872267353802779386697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85189248178235868519591131 127783872267353802779386697)
      ·
        refine ⟨95837904200515352084540023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127783872267353802779386697 95837904200515352084540023)
        ·
          refine ⟨143756856300773028126810035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95837904200515352084540023 143756856300773028126810035)
          ·
            refine ⟨215635284451159542190215053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143756856300773028126810035 215635284451159542190215053)
            ·
              refine ⟨80863231669184828321330645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215635284451159542190215053 80863231669184828321330645)
              ·
                refine ⟨1895231992246519413781187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80863231669184828321330645 1895231992246519413781187)
                ·
                  refine ⟨2842847988369779120671781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895231992246519413781187 2842847988369779120671781)
                  ·
                    refine ⟨533033997819333585125959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842847988369779120671781 533033997819333585125959)
                    ·
                      rfl

theorem cell23_3114240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 4].length) (baseStart_3114240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114240 prefixEnd_3114240 := by exact prefixLift 3114240
  have htrace : WordTrace (prefixWord ++ tailWord_3114240) baseStart_3114240 baseEnd_3114240 := by
    simpa [prefixWord, tailWord_3114240, baseEnd_3114240] using wordTrace_append hprefix tailTrace_3114240
  have hstable : (prefixWord ++ tailWord_3114240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114240).length < 2 ^ (prefixWord ++ tailWord_3114240).sum := by decide
  have hdescent : baseEnd_3114240 < baseStart_3114240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114300 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_3114300 : Nat := 118140960795 + 3114300 * 2 ^ 59
def prefixEnd_3114300 : Nat := 4983230072969 + 3 ^ 40 * 3114300 * 2
def baseEnd_3114300 : Nat := 533044267432423506875867

theorem tailTrace_3114300 : CollatzResearch.WordTrace tailWord_3114300 prefixEnd_3114300 533044267432423506875867 := by
  unfold tailWord_3114300
  simp only [CollatzResearch.WordTrace]
  refine ⟨56793926308715227469986177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75725235078286969959981569 56793926308715227469986177)
  ·
    refine ⟨42595444731536420602489633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56793926308715227469986177 42595444731536420602489633)
    ·
      refine ⟨31946583548652315451867225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42595444731536420602489633 31946583548652315451867225)
      ·
        refine ⟨23959937661489236588900419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31946583548652315451867225 23959937661489236588900419)
        ·
          refine ⟨35939906492233854883350629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959937661489236588900419 35939906492233854883350629)
          ·
            refine ⟨6738732467293847790628243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35939906492233854883350629 6738732467293847790628243)
            ·
              refine ⟨10108098700940771685942365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738732467293847790628243 10108098700940771685942365)
              ·
                refine ⟨3790537012852789382228387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10108098700940771685942365 3790537012852789382228387)
                ·
                  refine ⟨5685805519279184073342581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790537012852789382228387 5685805519279184073342581)
                  ·
                    refine ⟨533044267432423506875867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5685805519279184073342581 533044267432423506875867)
                    ·
                      rfl

theorem cell23_3114300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_3114300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114300 prefixEnd_3114300 := by exact prefixLift 3114300
  have htrace : WordTrace (prefixWord ++ tailWord_3114300) baseStart_3114300 baseEnd_3114300 := by
    simpa [prefixWord, tailWord_3114300, baseEnd_3114300] using wordTrace_append hprefix tailTrace_3114300
  have hstable : (prefixWord ++ tailWord_3114300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114300).length < 2 ^ (prefixWord ++ tailWord_3114300).sum := by decide
  have hdescent : baseEnd_3114300 < baseStart_3114300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114323 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5]
def baseStart_3114323 : Nat := 118140960795 + 3114323 * 2 ^ 59
def prefixEnd_3114323 : Nat := 4983230072969 + 3 ^ 40 * 3114323 * 2
def baseEnd_3114323 : Nat := 1599144612352323930639995

theorem tailTrace_3114323 : CollatzResearch.WordTrace tailWord_3114323 prefixEnd_3114323 1599144612352323930639995 := by
  unfold tailWord_3114323
  simp only [CollatzResearch.WordTrace]
  refine ⟨113588691496347129868059623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75725794330898086578706415 113588691496347129868059623)
  ·
    refine ⟨170383037244520694802089435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113588691496347129868059623 170383037244520694802089435)
    ·
      refine ⟨255574555866781042203134153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170383037244520694802089435 255574555866781042203134153)
      ·
        refine ⟨191680916900085781652350615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255574555866781042203134153 191680916900085781652350615)
        ·
          refine ⟨287521375350128672478525923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191680916900085781652350615 287521375350128672478525923)
          ·
            refine ⟨431282063025193008717788885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287521375350128672478525923 431282063025193008717788885)
            ·
              refine ⟨10108173352152961141823177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 431282063025193008717788885 10108173352152961141823177)
              ·
                refine ⟨7581130014114720856367383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10108173352152961141823177 7581130014114720856367383)
                ·
                  refine ⟨11371695021172081284551075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581130014114720856367383 11371695021172081284551075)
                  ·
                    refine ⟨17057542531758121926826613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11371695021172081284551075 17057542531758121926826613)
                    ·
                      refine ⟨1599144612352323930639995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17057542531758121926826613 1599144612352323930639995)
                      ·
                        rfl

theorem cell23_3114323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_3114323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114323 prefixEnd_3114323 := by exact prefixLift 3114323
  have htrace : WordTrace (prefixWord ++ tailWord_3114323) baseStart_3114323 baseEnd_3114323 := by
    simpa [prefixWord, tailWord_3114323, baseEnd_3114323] using wordTrace_append hprefix tailTrace_3114323
  have hstable : (prefixWord ++ tailWord_3114323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114323).length < 2 ^ (prefixWord ++ tailWord_3114323).sum := by decide
  have hdescent : baseEnd_3114323 < baseStart_3114323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114330 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_3114330 : Nat := 118140960795 + 3114330 * 2 ^ 59
def prefixEnd_3114330 : Nat := 4983230072969 + 3 ^ 40 * 3114330 * 2
def baseEnd_3114330 : Nat := 533049402238968467750821

theorem tailTrace_3114330 : CollatzResearch.WordTrace tailWord_3114330 prefixEnd_3114330 533049402238968467750821 := by
  unfold tailWord_3114330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28397236701830442515891111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75725964538214513375709629 28397236701830442515891111)
  ·
    refine ⟨42595855052745663773836667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28397236701830442515891111 42595855052745663773836667)
    ·
      refine ⟨63893782579118495660755001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42595855052745663773836667 63893782579118495660755001)
      ·
        refine ⟨47920336934338871745566251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63893782579118495660755001 47920336934338871745566251)
        ·
          refine ⟨71880505401508307618349377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47920336934338871745566251 71880505401508307618349377)
          ·
            refine ⟨53910379051131230713762033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71880505401508307618349377 53910379051131230713762033)
            ·
              refine ⟨40432784288348423035321525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53910379051131230713762033 40432784288348423035321525)
              ·
                refine ⟨3790573527032664659561393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40432784288348423035321525 3790573527032664659561393)
                ·
                  refine ⟨2842930145274498494671045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790573527032664659561393 2842930145274498494671045)
                  ·
                    refine ⟨533049402238968467750821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2842930145274498494671045 533049402238968467750821)
                    ·
                      rfl

theorem cell23_3114330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_3114330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114330 prefixEnd_3114330 := by exact prefixLift 3114330
  have htrace : WordTrace (prefixWord ++ tailWord_3114330) baseStart_3114330 baseEnd_3114330 := by
    simpa [prefixWord, tailWord_3114330, baseEnd_3114330] using wordTrace_append hprefix tailTrace_3114330
  have hstable : (prefixWord ++ tailWord_3114330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114330).length < 2 ^ (prefixWord ++ tailWord_3114330).sum := by decide
  have hdescent : baseEnd_3114330 < baseStart_3114330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114357 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3114357 : Nat := 118140960795 + 3114357 * 2 ^ 59
def prefixEnd_3114357 : Nat := 4983230072969 + 3 ^ 40 * 3114357 * 2
def baseEnd_3114357 : Nat := 1599162070694576797614839

theorem tailTrace_3114357 : CollatzResearch.WordTrace tailWord_3114357 prefixEnd_3114357 1599162070694576797614839 := by
  unfold tailWord_3114357
  simp only [CollatzResearch.WordTrace]
  refine ⟨113589931578223953674797325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75726621052149302449864883 113589931578223953674797325)
  ·
    refine ⟨42596224341833982628048997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113589931578223953674797325 42596224341833982628048997)
    ·
      refine ⟨7986792064093871742759187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42596224341833982628048997 7986792064093871742759187)
      ·
        refine ⟨11980188096140807614138781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7986792064093871742759187 11980188096140807614138781)
        ·
          refine ⟨4492570536052802855302043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11980188096140807614138781 4492570536052802855302043)
          ·
            refine ⟨6738855804079204282953065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492570536052802855302043 6738855804079204282953065)
            ·
              refine ⟨5054141853059403212214799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6738855804079204282953065 5054141853059403212214799)
              ·
                refine ⟨7581212779589104818322199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054141853059403212214799 7581212779589104818322199)
                ·
                  refine ⟨11371819169383657227483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581212779589104818322199 11371819169383657227483299)
                  ·
                    refine ⟨17057728754075485841224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11371819169383657227483299 17057728754075485841224949)
                    ·
                      refine ⟨1599162070694576797614839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17057728754075485841224949 1599162070694576797614839)
                      ·
                        rfl

theorem cell23_3114357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3114357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114357 prefixEnd_3114357 := by exact prefixLift 3114357
  have htrace : WordTrace (prefixWord ++ tailWord_3114357) baseStart_3114357 baseEnd_3114357 := by
    simpa [prefixWord, tailWord_3114357, baseEnd_3114357] using wordTrace_append hprefix tailTrace_3114357
  have hstable : (prefixWord ++ tailWord_3114357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114357).length < 2 ^ (prefixWord ++ tailWord_3114357).sum := by decide
  have hdescent : baseEnd_3114357 < baseStart_3114357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114440 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3114440 : Nat := 118140960795 + 3114440 * 2 ^ 59
def prefixEnd_3114440 : Nat := 4983230072969 + 3 ^ 40 * 3114440 * 2
def baseEnd_3114440 : Nat := 1599204689588899972876957

theorem tailTrace_3114440 : CollatzResearch.WordTrace tailWord_3114440 prefixEnd_3114440 1599204689588899972876957 := by
  unfold tailWord_3114440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56796479418461629425034387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75728639224615505900045849 56796479418461629425034387)
  ·
    refine ⟨85194719127692444137551581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56796479418461629425034387 85194719127692444137551581)
    ·
      refine ⟨31948019672884666551581843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85194719127692444137551581 31948019672884666551581843)
      ·
        refine ⟨47922029509326999827372765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31948019672884666551581843 47922029509326999827372765)
        ·
          refine ⟨17970761065997624935264787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47922029509326999827372765 17970761065997624935264787)
          ·
            refine ⟨26956141598996437402897181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17970761065997624935264787 26956141598996437402897181)
            ·
              refine ⟨10108553099623664026086443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26956141598996437402897181 10108553099623664026086443)
              ·
                refine ⟨15162829649435496039129665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108553099623664026086443 15162829649435496039129665)
                ·
                  refine ⟨11372122237076622029347249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15162829649435496039129665 11372122237076622029347249)
                  ·
                    refine ⟨8529091677807466522010437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11372122237076622029347249 8529091677807466522010437)
                    ·
                      refine ⟨1599204689588899972876957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8529091677807466522010437 1599204689588899972876957)
                      ·
                        rfl

theorem cell23_3114440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3114440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114440 prefixEnd_3114440 := by exact prefixLift 3114440
  have htrace : WordTrace (prefixWord ++ tailWord_3114440) baseStart_3114440 baseEnd_3114440 := by
    simpa [prefixWord, tailWord_3114440, baseEnd_3114440] using wordTrace_append hprefix tailTrace_3114440
  have hstable : (prefixWord ++ tailWord_3114440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114440).length < 2 ^ (prefixWord ++ tailWord_3114440).sum := by decide
  have hdescent : baseEnd_3114440 < baseStart_3114440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114444 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3114444 : Nat := 118140960795 + 3114444 * 2 ^ 59
def prefixEnd_3114444 : Nat := 4983230072969 + 3 ^ 40 * 3114444 * 2
def baseEnd_3114444 : Nat := 1599206743511517957226939

theorem tailTrace_3114444 : CollatzResearch.WordTrace tailWord_3114444 prefixEnd_3114444 1599206743511517957226939 := by
  unfold tailWord_3114444
  simp only [CollatzResearch.WordTrace]
  refine ⟨56796552364454383766607193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75728736485939178355476257 56796552364454383766607193)
  ·
    refine ⟨42597414273340787824955395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56796552364454383766607193 42597414273340787824955395)
    ·
      refine ⟨63896121410011181737433093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42597414273340787824955395 63896121410011181737433093)
      ·
        refine ⟨11980522764377096575768705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63896121410011181737433093 11980522764377096575768705)
        ·
          refine ⟨8985392073282822431826529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11980522764377096575768705 8985392073282822431826529)
          ·
            refine ⟨6739044054962116823869897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985392073282822431826529 6739044054962116823869897)
            ·
              refine ⟨5054283041221587617902423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739044054962116823869897 5054283041221587617902423)
              ·
                refine ⟨7581424561832381426853635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054283041221587617902423 7581424561832381426853635)
                ·
                  refine ⟨11372136842748572140280453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581424561832381426853635 11372136842748572140280453)
                  ·
                    refine ⟨2132275658015357276302585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11372136842748572140280453 2132275658015357276302585)
                    ·
                      refine ⟨1599206743511517957226939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132275658015357276302585 1599206743511517957226939)
                      ·
                        rfl

theorem cell23_3114444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3114444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114444 prefixEnd_3114444 := by exact prefixLift 3114444
  have htrace : WordTrace (prefixWord ++ tailWord_3114444) baseStart_3114444 baseEnd_3114444 := by
    simpa [prefixWord, tailWord_3114444, baseEnd_3114444] using wordTrace_append hprefix tailTrace_3114444
  have hstable : (prefixWord ++ tailWord_3114444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114444).length < 2 ^ (prefixWord ++ tailWord_3114444).sum := by decide
  have hdescent : baseEnd_3114444 < baseStart_3114444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114467 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 5]
def baseStart_3114467 : Nat := 118140960795 + 3114467 * 2 ^ 59
def prefixEnd_3114467 : Nat := 4983230072969 + 3 ^ 40 * 3114467 * 2
def baseEnd_3114467 : Nat := 177690950396285707471037

theorem tailTrace_3114467 : CollatzResearch.WordTrace tailWord_3114467 prefixEnd_3114467 177690950396285707471037 := by
  unfold tailWord_3114467
  simp only [CollatzResearch.WordTrace]
  refine ⟨113593943607825442461301655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75729295738550294974201103 113593943607825442461301655)
  ·
    refine ⟨170390915411738163691952483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113593943607825442461301655 170390915411738163691952483)
    ·
      refine ⟨255586373117607245537928725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170390915411738163691952483 255586373117607245537928725)
      ·
        refine ⟨11980611239887839634590409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255586373117607245537928725 11980611239887839634590409)
        ·
          refine ⟨8985458429915879725942807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11980611239887839634590409 8985458429915879725942807)
          ·
            refine ⟨13478187644873819588914211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985458429915879725942807 13478187644873819588914211)
            ·
              refine ⟨20217281467310729383371317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13478187644873819588914211 20217281467310729383371317)
              ·
                refine ⟨1895370137560380879691061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20217281467310729383371317 1895370137560380879691061)
                ·
                  refine ⟨177690950396285707471037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895370137560380879691061 177690950396285707471037)
                  ·
                    rfl

theorem cell23_3114467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 5].length) (baseStart_3114467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114467 prefixEnd_3114467 := by exact prefixLift 3114467
  have htrace : WordTrace (prefixWord ++ tailWord_3114467) baseStart_3114467 baseEnd_3114467 := by
    simpa [prefixWord, tailWord_3114467, baseEnd_3114467] using wordTrace_append hprefix tailTrace_3114467
  have hstable : (prefixWord ++ tailWord_3114467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114467).length < 2 ^ (prefixWord ++ tailWord_3114467).sum := by decide
  have hdescent : baseEnd_3114467 < baseStart_3114467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114530 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3114530 : Nat := 118140960795 + 3114530 * 2 ^ 59
def prefixEnd_3114530 : Nat := 4983230072969 + 3 ^ 40 * 3114530 * 2
def baseEnd_3114530 : Nat := 1599250902847804620751543

theorem tailTrace_3114530 : CollatzResearch.WordTrace tailWord_3114530 prefixEnd_3114530 1599250902847804620751543 := by
  unfold tailWord_3114530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28399060351649301055211261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75730827604398136147230029 28399060351649301055211261)
  ·
    refine ⟨10649647631868487895704223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28399060351649301055211261 10649647631868487895704223)
    ·
      refine ⟨15974471447802731843556335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10649647631868487895704223 15974471447802731843556335)
      ·
        refine ⟨23961707171704097765334503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15974471447802731843556335 23961707171704097765334503)
        ·
          refine ⟨35942560757556146648001755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23961707171704097765334503 35942560757556146648001755)
          ·
            refine ⟨53913841136334219972002633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35942560757556146648001755 53913841136334219972002633)
            ·
              refine ⟨40435380852250664979001975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53913841136334219972002633 40435380852250664979001975)
              ·
                refine ⟨60653071278375997468502963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40435380852250664979001975 60653071278375997468502963)
                ·
                  refine ⟨90979606917563996202754445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60653071278375997468502963 90979606917563996202754445)
                  ·
                    refine ⟨34117352594086498576032917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90979606917563996202754445 34117352594086498576032917)
                    ·
                      refine ⟨1599250902847804620751543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34117352594086498576032917 1599250902847804620751543)
                      ·
                        rfl

theorem cell23_3114530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3114530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114530 prefixEnd_3114530 := by exact prefixLift 3114530
  have htrace : WordTrace (prefixWord ++ tailWord_3114530) baseStart_3114530 baseEnd_3114530 := by
    simpa [prefixWord, tailWord_3114530, baseEnd_3114530] using wordTrace_append hprefix tailTrace_3114530
  have hstable : (prefixWord ++ tailWord_3114530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114530).length < 2 ^ (prefixWord ++ tailWord_3114530).sum := by decide
  have hdescent : baseEnd_3114530 < baseStart_3114530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114607 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 6, 2]
def baseStart_3114607 : Nat := 118140960795 + 3114607 * 2 ^ 59
def prefixEnd_3114607 : Nat := 4983230072969 + 3 ^ 40 * 3114607 * 2
def baseEnd_3114607 : Nat := 1599290440858200819488689

theorem tailTrace_3114607 : CollatzResearch.WordTrace tailWord_3114607 prefixEnd_3114607 1599290440858200819488689 := by
  unfold tailWord_3114607
  simp only [CollatzResearch.WordTrace]
  refine ⟨113599049827318246371398075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75732699884878830914265383 113599049827318246371398075)
  ·
    refine ⟨170398574740977369557097113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113599049827318246371398075 170398574740977369557097113)
    ·
      refine ⟨127798931055733027167822835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170398574740977369557097113 127798931055733027167822835)
      ·
        refine ⟨191698396583599540751734253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127798931055733027167822835 191698396583599540751734253)
        ·
          refine ⟨71886898718849827781900345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191698396583599540751734253 71886898718849827781900345)
          ·
            refine ⟨53915174039137370836425259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71886898718849827781900345 53915174039137370836425259)
            ·
              refine ⟨80872761058706056254637889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53915174039137370836425259 80872761058706056254637889)
              ·
                refine ⟨60654570794029542190978417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80872761058706056254637889 60654570794029542190978417)
                ·
                  refine ⟨45490928095522156643233813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60654570794029542190978417 45490928095522156643233813)
                  ·
                    refine ⟨2132387254477601092651585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45490928095522156643233813 2132387254477601092651585)
                    ·
                      refine ⟨1599290440858200819488689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132387254477601092651585 1599290440858200819488689)
                      ·
                        rfl

theorem cell23_3114607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6, 2].length) (baseStart_3114607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114607 prefixEnd_3114607 := by exact prefixLift 3114607
  have htrace : WordTrace (prefixWord ++ tailWord_3114607) baseStart_3114607 baseEnd_3114607 := by
    simpa [prefixWord, tailWord_3114607, baseEnd_3114607] using wordTrace_append hprefix tailTrace_3114607
  have hstable : (prefixWord ++ tailWord_3114607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114607).length < 2 ^ (prefixWord ++ tailWord_3114607).sum := by decide
  have hdescent : baseEnd_3114607 < baseStart_3114607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114617 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_3114617 : Nat := 118140960795 + 3114617 * 2 ^ 59
def prefixEnd_3114617 : Nat := 4983230072969 + 3 ^ 40 * 3114617 * 2
def baseEnd_3114617 : Nat := 533098525221581926787881

theorem tailTrace_3114617 : CollatzResearch.WordTrace tailWord_3114617 prefixEnd_3114617 533098525221581926787881 := by
  unfold tailWord_3114617
  simp only [CollatzResearch.WordTrace]
  refine ⟨113599414557282018079262105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75732943038188012052841403 113599414557282018079262105)
  ·
    refine ⟨85199560917961513559446579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113599414557282018079262105 85199560917961513559446579)
    ·
      refine ⟨127799341376942270339169869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85199560917961513559446579 127799341376942270339169869)
      ·
        refine ⟨47924753016353351377188701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127799341376942270339169869 47924753016353351377188701)
        ·
          refine ⟨17971782381132506766445763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47924753016353351377188701 17971782381132506766445763)
          ·
            refine ⟨26957673571698760149668645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17971782381132506766445763 26957673571698760149668645)
            ·
              refine ⟨5054563794693517528062871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26957673571698760149668645 5054563794693517528062871)
              ·
                refine ⟨7581845692040276292094307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054563794693517528062871 7581845692040276292094307)
                ·
                  refine ⟨11372768538060414438141461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581845692040276292094307 11372768538060414438141461)
                  ·
                    refine ⟨533098525221581926787881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11372768538060414438141461 533098525221581926787881)
                    ·
                      rfl

theorem cell23_3114617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_3114617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114617 prefixEnd_3114617 := by exact prefixLift 3114617
  have htrace : WordTrace (prefixWord ++ tailWord_3114617) baseStart_3114617 baseEnd_3114617 := by
    simpa [prefixWord, tailWord_3114617, baseEnd_3114617] using wordTrace_append hprefix tailTrace_3114617
  have hstable : (prefixWord ++ tailWord_3114617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114617).length < 2 ^ (prefixWord ++ tailWord_3114617).sum := by decide
  have hdescent : baseEnd_3114617 < baseStart_3114617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114628 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_3114628 : Nat := 118140960795 + 3114628 * 2 ^ 59
def prefixEnd_3114628 : Nat := 4983230072969 + 3 ^ 40 * 3114628 * 2
def baseEnd_3114628 : Nat := 1599301223951945237326093

theorem tailTrace_3114628 : CollatzResearch.WordTrace tailWord_3114628 prefixEnd_3114628 1599301223951945237326093 := by
  unfold tailWord_3114628
  simp only [CollatzResearch.WordTrace]
  refine ⟨56799907880121083478956269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75733210506828111305275025 56799907880121083478956269)
  ·
    refine ⟨21299965455045406304608601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56799907880121083478956269 21299965455045406304608601)
    ·
      refine ⟨15974974091284054728456451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21299965455045406304608601 15974974091284054728456451)
      ·
        refine ⟨23962461136926082092684677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15974974091284054728456451 23962461136926082092684677)
        ·
          refine ⟨4492961463173640392378377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23962461136926082092684677 4492961463173640392378377)
          ·
            refine ⟨3369721097380230294283783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4492961463173640392378377 3369721097380230294283783)
            ·
              refine ⟨5054581646070345441425675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369721097380230294283783 5054581646070345441425675)
              ·
                refine ⟨7581872469105518162138513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054581646070345441425675 7581872469105518162138513)
                ·
                  refine ⟨5686404351829138621603885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581872469105518162138513 5686404351829138621603885)
                  ·
                    refine ⟨2132401631935926983101457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5686404351829138621603885 2132401631935926983101457)
                    ·
                      refine ⟨1599301223951945237326093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132401631935926983101457 1599301223951945237326093)
                      ·
                        rfl

theorem cell23_3114628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_3114628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114628 prefixEnd_3114628 := by exact prefixLift 3114628
  have htrace : WordTrace (prefixWord ++ tailWord_3114628) baseStart_3114628 baseEnd_3114628 := by
    simpa [prefixWord, tailWord_3114628, baseEnd_3114628] using wordTrace_append hprefix tailTrace_3114628
  have hstable : (prefixWord ++ tailWord_3114628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114628).length < 2 ^ (prefixWord ++ tailWord_3114628).sum := by decide
  have hdescent : baseEnd_3114628 < baseStart_3114628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114674 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3114674 : Nat := 118140960795 + 3114674 * 2 ^ 59
def prefixEnd_3114674 : Nat := 4983230072969 + 3 ^ 40 * 3114674 * 2
def baseEnd_3114674 : Nat := 1599324844062052057350881

theorem tailTrace_3114674 : CollatzResearch.WordTrace tailWord_3114674 prefixEnd_3114674 1599324844062052057350881 := by
  unfold tailWord_3114674
  simp only [CollatzResearch.WordTrace]
  refine ⟨28400373379518879203521769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75734329012050344542724717 28400373379518879203521769)
  ·
    refine ⟨21300280034639159402641327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28400373379518879203521769 21300280034639159402641327)
    ·
      refine ⟨31950420051958739103961991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21300280034639159402641327 31950420051958739103961991)
      ·
        refine ⟨47925630077938108655942987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31950420051958739103961991 47925630077938108655942987)
        ·
          refine ⟨71888445116907162983914481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47925630077938108655942987 71888445116907162983914481)
          ·
            refine ⟨53916333837680372237935861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71888445116907162983914481 53916333837680372237935861)
            ·
              refine ⟨5054656297282534897306487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53916333837680372237935861 5054656297282534897306487)
              ·
                refine ⟨7581984445923802345959731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054656297282534897306487 7581984445923802345959731)
                ·
                  refine ⟨11372976668885703518939597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7581984445923802345959731 11372976668885703518939597)
                  ·
                    refine ⟨4264866250832138819602349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11372976668885703518939597 4264866250832138819602349)
                    ·
                      refine ⟨1599324844062052057350881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4264866250832138819602349 1599324844062052057350881)
                      ·
                        rfl

theorem cell23_3114674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3114674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114674 prefixEnd_3114674 := by exact prefixLift 3114674
  have htrace : WordTrace (prefixWord ++ tailWord_3114674) baseStart_3114674 baseEnd_3114674 := by
    simpa [prefixWord, tailWord_3114674, baseEnd_3114674] using wordTrace_append hprefix tailTrace_3114674
  have hstable : (prefixWord ++ tailWord_3114674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114674).length < 2 ^ (prefixWord ++ tailWord_3114674).sum := by decide
  have hdescent : baseEnd_3114674 < baseStart_3114674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114678 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3114678 : Nat := 118140960795 + 3114678 * 2 ^ 59
def prefixEnd_3114678 : Nat := 4983230072969 + 3 ^ 40 * 3114678 * 2
def baseEnd_3114678 : Nat := 1599326897984670041700863

theorem tailTrace_3114678 : CollatzResearch.WordTrace tailWord_3114678 prefixEnd_3114678 1599326897984670041700863 := by
  unfold tailWord_3114678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100102463128814093577043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75734426273374016998155125 7100102463128814093577043)
  ·
    refine ⟨10650153694693221140365565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7100102463128814093577043 10650153694693221140365565)
    ·
      refine ⟨3993807635509957927637087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10650153694693221140365565 3993807635509957927637087)
      ·
        refine ⟨5990711453264936891455631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993807635509957927637087 5990711453264936891455631)
        ·
          refine ⟨8986067179897405337183447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990711453264936891455631 8986067179897405337183447)
          ·
            refine ⟨13479100769846108005775171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986067179897405337183447 13479100769846108005775171)
            ·
              refine ⟨20218651154769162008662757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13479100769846108005775171 20218651154769162008662757)
              ·
                refine ⟨3790997091519217876624267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20218651154769162008662757 3790997091519217876624267)
                ·
                  refine ⟨5686495637278826814936401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790997091519217876624267 5686495637278826814936401)
                  ·
                    refine ⟨4264871727959120111202301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5686495637278826814936401 4264871727959120111202301)
                    ·
                      refine ⟨1599326897984670041700863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4264871727959120111202301 1599326897984670041700863)
                      ·
                        rfl

theorem cell23_3114678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3114678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114678 prefixEnd_3114678 := by exact prefixLift 3114678
  have htrace : WordTrace (prefixWord ++ tailWord_3114678) baseStart_3114678 baseEnd_3114678 := by
    simpa [prefixWord, tailWord_3114678, baseEnd_3114678] using wordTrace_append hprefix tailTrace_3114678
  have hstable : (prefixWord ++ tailWord_3114678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114678).length < 2 ^ (prefixWord ++ tailWord_3114678).sum := by decide
  have hdescent : baseEnd_3114678 < baseStart_3114678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114747 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3]
def baseStart_3114747 : Nat := 118140960795 + 3114747 * 2 ^ 59
def prefixEnd_3114747 : Nat := 4983230072969 + 3 ^ 40 * 3114747 * 2
def baseEnd_3114747 : Nat := 1599362328149830271738045

theorem tailTrace_3114747 : CollatzResearch.WordTrace tailWord_3114747 prefixEnd_3114747 1599362328149830271738045 := by
  unfold tailWord_3114747
  simp only [CollatzResearch.WordTrace]
  refine ⟨113604156046811050281494495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75736104031207366854329663 113604156046811050281494495)
  ·
    refine ⟨170406234070216575422241743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113604156046811050281494495 170406234070216575422241743)
    ·
      refine ⟨255609351105324863133362615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170406234070216575422241743 255609351105324863133362615)
      ·
        refine ⟨383414026657987294700043923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255609351105324863133362615 383414026657987294700043923)
        ·
          refine ⟨575121039986980942050065885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383414026657987294700043923 575121039986980942050065885)
          ·
            refine ⟨215670389995117853268774707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575121039986980942050065885 215670389995117853268774707)
            ·
              refine ⟨323505584992676779903162061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215670389995117853268774707 323505584992676779903162061)
              ·
                refine ⟨121314594372253792463685773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323505584992676779903162061 121314594372253792463685773)
                ·
                  refine ⟨45492972889595172173882165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121314594372253792463685773 45492972889595172173882165)
                  ·
                    refine ⟨4264966208399547391301453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45492972889595172173882165 4264966208399547391301453)
                    ·
                      refine ⟨1599362328149830271738045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4264966208399547391301453 1599362328149830271738045)
                      ·
                        rfl

theorem cell23_3114747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3].length) (baseStart_3114747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114747 prefixEnd_3114747 := by exact prefixLift 3114747
  have htrace : WordTrace (prefixWord ++ tailWord_3114747) baseStart_3114747 baseEnd_3114747 := by
    simpa [prefixWord, tailWord_3114747, baseEnd_3114747] using wordTrace_append hprefix tailTrace_3114747
  have hstable : (prefixWord ++ tailWord_3114747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114747).length < 2 ^ (prefixWord ++ tailWord_3114747).sum := by decide
  have hdescent : baseEnd_3114747 < baseStart_3114747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114767 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 4, 5]
def baseStart_3114767 : Nat := 118140960795 + 3114767 * 2 ^ 59
def prefixEnd_3114767 : Nat := 4983230072969 + 3 ^ 40 * 3114767 * 2
def baseEnd_3114767 : Nat := 533124199254306731162651

theorem tailTrace_3114767 : CollatzResearch.WordTrace tailWord_3114767 prefixEnd_3114767 533124199254306731162651 := by
  unfold tailWord_3114767
  simp only [CollatzResearch.WordTrace]
  refine ⟨113604885506738593697222555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75736590337825729131481703 113604885506738593697222555)
  ·
    refine ⟨170407328260107890545833833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113604885506738593697222555 170407328260107890545833833)
    ·
      refine ⟨127805496195080917909375375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170407328260107890545833833 127805496195080917909375375)
      ·
        refine ⟨191708244292621376864063063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127805496195080917909375375 191708244292621376864063063)
        ·
          refine ⟨287562366438932065296094595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191708244292621376864063063 287562366438932065296094595)
          ·
            refine ⟨431343549658398097944141893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287562366438932065296094595 431343549658398097944141893)
            ·
              refine ⟨80876915560949643364526605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431343549658398097944141893 80876915560949643364526605)
              ·
                refine ⟨30328843335356116261697477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80876915560949643364526605 30328843335356116261697477)
                ·
                  refine ⟨5686658125379271799068277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30328843335356116261697477 5686658125379271799068277)
                  ·
                    refine ⟨533124199254306731162651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5686658125379271799068277 533124199254306731162651)
                    ·
                      rfl

theorem cell23_3114767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_3114767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114767 prefixEnd_3114767 := by exact prefixLift 3114767
  have htrace : WordTrace (prefixWord ++ tailWord_3114767) baseStart_3114767 baseEnd_3114767 := by
    simpa [prefixWord, tailWord_3114767, baseEnd_3114767] using wordTrace_append hprefix tailTrace_3114767
  have hstable : (prefixWord ++ tailWord_3114767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114767).length < 2 ^ (prefixWord ++ tailWord_3114767).sum := by decide
  have hdescent : baseEnd_3114767 < baseStart_3114767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114782 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3114782 : Nat := 118140960795 + 3114782 * 2 ^ 59
def prefixEnd_3114782 : Nat := 4983230072969 + 3 ^ 40 * 3114782 * 2
def baseEnd_3114782 : Nat := 1599380299972737634800385

theorem tailTrace_3114782 : CollatzResearch.WordTrace tailWord_3114782 prefixEnd_3114782 1599380299972737634800385 := by
  unfold tailWord_3114782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14200679075210531407377325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75736955067789500839345733 14200679075210531407377325)
  ·
    refine ⟨5325254653203949277766497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14200679075210531407377325 5325254653203949277766497)
    ·
      refine ⟨3993940989902961958324873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5325254653203949277766497 3993940989902961958324873)
      ·
        refine ⟨2995455742427221468743655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3993940989902961958324873 2995455742427221468743655)
        ·
          refine ⟨4493183613640832203115483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995455742427221468743655 4493183613640832203115483)
          ·
            refine ⟨6739775420461248304673225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493183613640832203115483 6739775420461248304673225)
            ·
              refine ⟨5054831565345936228504919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739775420461248304673225 5054831565345936228504919)
              ·
                refine ⟨7582247348018904342757379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054831565345936228504919 7582247348018904342757379)
                ·
                  refine ⟨11373371022028356514136069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7582247348018904342757379 11373371022028356514136069)
                  ·
                    refine ⟨2132507066630316846400513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11373371022028356514136069 2132507066630316846400513)
                    ·
                      refine ⟨1599380299972737634800385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132507066630316846400513 1599380299972737634800385)
                      ·
                        rfl

theorem cell23_3114782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3114782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114782 prefixEnd_3114782 := by exact prefixLift 3114782
  have htrace : WordTrace (prefixWord ++ tailWord_3114782) baseStart_3114782 baseEnd_3114782 := by
    simpa [prefixWord, tailWord_3114782, baseEnd_3114782] using wordTrace_append hprefix tailTrace_3114782
  have hstable : (prefixWord ++ tailWord_3114782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114782).length < 2 ^ (prefixWord ++ tailWord_3114782).sum := by decide
  have hdescent : baseEnd_3114782 < baseStart_3114782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114801 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_3114801 : Nat := 118140960795 + 3114801 * 2 ^ 59
def prefixEnd_3114801 : Nat := 4983230072969 + 3 ^ 40 * 3114801 * 2
def baseEnd_3114801 : Nat := 533130018701724353487599

theorem tailTrace_3114801 : CollatzResearch.WordTrace tailWord_3114801 prefixEnd_3114801 533130018701724353487599 := by
  unfold tailWord_3114801
  simp only [CollatzResearch.WordTrace]
  refine ⟨113606125588615417503960257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75737417059076945002640171 113606125588615417503960257)
  ·
    refine ⟨85204594191461563127970193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113606125588615417503960257 85204594191461563127970193)
    ·
      refine ⟨63903445643596172345977645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85204594191461563127970193 63903445643596172345977645)
      ·
        refine ⟨23963792116348564629741617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63903445643596172345977645 23963792116348564629741617)
        ·
          refine ⟨17972844087261423472306213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23963792116348564629741617 17972844087261423472306213)
          ·
            refine ⟨3369908266361516901057415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17972844087261423472306213 3369908266361516901057415)
            ·
              refine ⟨5054862399542275351586123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369908266361516901057415 5054862399542275351586123)
              ·
                refine ⟨7582293599313413027379185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054862399542275351586123 7582293599313413027379185)
                ·
                  refine ⟨5686720199485059770534389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7582293599313413027379185 5686720199485059770534389)
                  ·
                    refine ⟨533130018701724353487599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5686720199485059770534389 533130018701724353487599)
                    ·
                      rfl

theorem cell23_3114801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_3114801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114801 prefixEnd_3114801 := by exact prefixLift 3114801
  have htrace : WordTrace (prefixWord ++ tailWord_3114801) baseStart_3114801 baseEnd_3114801 := by
    simpa [prefixWord, tailWord_3114801, baseEnd_3114801] using wordTrace_append hprefix tailTrace_3114801
  have hstable : (prefixWord ++ tailWord_3114801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114801).length < 2 ^ (prefixWord ++ tailWord_3114801).sum := by decide
  have hdescent : baseEnd_3114801 < baseStart_3114801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114807 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3114807 : Nat := 118140960795 + 3114807 * 2 ^ 59
def prefixEnd_3114807 : Nat := 4983230072969 + 3 ^ 40 * 3114807 * 2
def baseEnd_3114807 : Nat := 1599393136989100036987769

theorem tailTrace_3114807 : CollatzResearch.WordTrace tailWord_3114807 prefixEnd_3114807 1599393136989100036987769 := by
  unfold tailWord_3114807
  simp only [CollatzResearch.WordTrace]
  refine ⟨113606344426593680528678675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75737562951062453685785783 113606344426593680528678675)
  ·
    refine ⟨170409516639890520793018013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113606344426593680528678675 170409516639890520793018013)
    ·
      refine ⟨63903568739958945297381755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170409516639890520793018013 63903568739958945297381755)
      ·
        refine ⟨95855353109938417946072633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63903568739958945297381755 95855353109938417946072633)
        ·
          refine ⟨71891514832453813459554475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95855353109938417946072633 71891514832453813459554475)
          ·
            refine ⟨107837272248680720189331713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71891514832453813459554475 107837272248680720189331713)
            ·
              refine ⟨80877954186510540141998785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107837272248680720189331713 80877954186510540141998785)
              ·
                refine ⟨60658465639882905106499089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80877954186510540141998785 60658465639882905106499089)
                ·
                  refine ⟨45493849229912178829874317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60658465639882905106499089 45493849229912178829874317)
                  ·
                    refine ⟨17060193461217067061202869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45493849229912178829874317 17060193461217067061202869)
                    ·
                      refine ⟨1599393136989100036987769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17060193461217067061202869 1599393136989100036987769)
                      ·
                        rfl

theorem cell23_3114807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3114807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114807 prefixEnd_3114807 := by exact prefixLift 3114807
  have htrace : WordTrace (prefixWord ++ tailWord_3114807) baseStart_3114807 baseEnd_3114807 := by
    simpa [prefixWord, tailWord_3114807, baseEnd_3114807] using wordTrace_append hprefix tailTrace_3114807
  have hstable : (prefixWord ++ tailWord_3114807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114807).length < 2 ^ (prefixWord ++ tailWord_3114807).sum := by decide
  have hdescent : baseEnd_3114807 < baseStart_3114807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114857 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_3114857 : Nat := 118140960795 + 3114857 * 2 ^ 59
def prefixEnd_3114857 : Nat := 4983230072969 + 3 ^ 40 * 3114857 * 2
def baseEnd_3114857 : Nat := 533139603673941613787513

theorem tailTrace_3114857 : CollatzResearch.WordTrace tailWord_3114857 prefixEnd_3114857 533139603673941613787513 := by
  unfold tailWord_3114857
  simp only [CollatzResearch.WordTrace]
  refine ⟨113608168076412539067998825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75738778717608359378665883 113608168076412539067998825)
  ·
    refine ⟨85206126057309404300999119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113608168076412539067998825 85206126057309404300999119)
    ·
      refine ⟨127809189085964106451498679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85206126057309404300999119 127809189085964106451498679)
      ·
        refine ⟨191713783628946159677248019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127809189085964106451498679 191713783628946159677248019)
        ·
          refine ⟨287570675443419239515872029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191713783628946159677248019 287570675443419239515872029)
          ·
            refine ⟨107839003291282214818452011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287570675443419239515872029 107839003291282214818452011)
            ·
              refine ⟨161758504936923322227678017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107839003291282214818452011 161758504936923322227678017)
              ·
                refine ⟨121318878702692491670758513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161758504936923322227678017 121318878702692491670758513)
                ·
                  refine ⟨90989159027019368753068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121318878702692491670758513 90989159027019368753068885)
                  ·
                    refine ⟨533139603673941613787513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 90989159027019368753068885 533139603673941613787513)
                    ·
                      rfl

theorem cell23_3114857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_3114857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114857 prefixEnd_3114857 := by exact prefixLift 3114857
  have htrace : WordTrace (prefixWord ++ tailWord_3114857) baseStart_3114857 baseEnd_3114857 := by
    simpa [prefixWord, tailWord_3114857, baseEnd_3114857] using wordTrace_append hprefix tailTrace_3114857
  have hstable : (prefixWord ++ tailWord_3114857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114857).length < 2 ^ (prefixWord ++ tailWord_3114857).sum := by decide
  have hdescent : baseEnd_3114857 < baseStart_3114857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114908 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3114908 : Nat := 118140960795 + 3114908 * 2 ^ 59
def prefixEnd_3114908 : Nat := 4983230072969 + 3 ^ 40 * 3114908 * 2
def baseEnd_3114908 : Nat := 533148332845068047274935

theorem tailTrace_3114908 : CollatzResearch.WordTrace tailWord_3114908 prefixEnd_3114908 533148332845068047274935 := by
  unfold tailWord_3114908
  simp only [CollatzResearch.WordTrace]
  refine ⟨56805014099613887389052689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75740018799485183185403585 56805014099613887389052689)
  ·
    refine ⟨42603760574710415541789517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56805014099613887389052689 42603760574710415541789517)
    ·
      refine ⟨15976410215516405828171069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42603760574710415541789517 15976410215516405828171069)
      ·
        refine ⟨5991153830818652185564151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15976410215516405828171069 5991153830818652185564151)
        ·
          refine ⟨8986730746227978278346227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991153830818652185564151 8986730746227978278346227)
          ·
            refine ⟨13480096119341967417519341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986730746227978278346227 13480096119341967417519341)
            ·
              refine ⟨5055036044753237781569753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13480096119341967417519341 5055036044753237781569753)
              ·
                refine ⟨3791277033564928336177315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055036044753237781569753 3791277033564928336177315)
                ·
                  refine ⟨5686915550347392504265973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791277033564928336177315 5686915550347392504265973)
                  ·
                    refine ⟨533148332845068047274935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5686915550347392504265973 533148332845068047274935)
                    ·
                      rfl

theorem cell23_3114908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3114908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114908 prefixEnd_3114908 := by exact prefixLift 3114908
  have htrace : WordTrace (prefixWord ++ tailWord_3114908) baseStart_3114908 baseEnd_3114908 := by
    simpa [prefixWord, tailWord_3114908, baseEnd_3114908] using wordTrace_append hprefix tailTrace_3114908
  have hstable : (prefixWord ++ tailWord_3114908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114908).length < 2 ^ (prefixWord ++ tailWord_3114908).sum := by decide
  have hdescent : baseEnd_3114908 < baseStart_3114908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114954 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3114954 : Nat := 118140960795 + 3114954 * 2 ^ 59
def prefixEnd_3114954 : Nat := 4983230072969 + 3 ^ 40 * 3114954 * 2
def baseEnd_3114954 : Nat := 1599468618645310961849593

theorem tailTrace_3114954 : CollatzResearch.WordTrace tailWord_3114954 prefixEnd_3114954 1599468618645310961849593 := by
  unfold tailWord_3114954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402926489265281158569979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75741137304707416422853277 28402926489265281158569979)
  ·
    refine ⟨42604389733897921737854969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28402926489265281158569979 42604389733897921737854969)
    ·
      refine ⟨31953292300423441303391227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42604389733897921737854969 31953292300423441303391227)
      ·
        refine ⟨47929938450635161955086841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31953292300423441303391227 47929938450635161955086841)
        ·
          refine ⟨35947453837976371466315131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47929938450635161955086841 35947453837976371466315131)
          ·
            refine ⟨53921180756964557199472697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35947453837976371466315131 53921180756964557199472697)
            ·
              refine ⟨40440885567723417899604523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53921180756964557199472697 40440885567723417899604523)
              ·
                refine ⟨60661328351585126849406785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40440885567723417899604523 60661328351585126849406785)
                ·
                  refine ⟨45495996263688845137055089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60661328351585126849406785 45495996263688845137055089)
                  ·
                    refine ⟨34121997197766633852791317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45495996263688845137055089 34121997197766633852791317)
                    ·
                      refine ⟨1599468618645310961849593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34121997197766633852791317 1599468618645310961849593)
                      ·
                        rfl

theorem cell23_3114954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3114954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114954 prefixEnd_3114954 := by exact prefixLift 3114954
  have htrace : WordTrace (prefixWord ++ tailWord_3114954) baseStart_3114954 baseEnd_3114954 := by
    simpa [prefixWord, tailWord_3114954, baseEnd_3114954] using wordTrace_append hprefix tailTrace_3114954
  have hstable : (prefixWord ++ tailWord_3114954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114954).length < 2 ^ (prefixWord ++ tailWord_3114954).sum := by decide
  have hdescent : baseEnd_3114954 < baseStart_3114954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114962 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3114962 : Nat := 118140960795 + 3114962 * 2 ^ 59
def prefixEnd_3114962 : Nat := 4983230072969 + 3 ^ 40 * 3114962 * 2
def baseEnd_3114962 : Nat := 1599472726490546930549557

theorem tailTrace_3114962 : CollatzResearch.WordTrace tailWord_3114962 prefixEnd_3114962 1599472726490546930549557 := by
  unfold tailWord_3114962
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402999435258035500142785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75741331827354761333714093 28402999435258035500142785)
  ·
    refine ⟨21302249576443526625107089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28402999435258035500142785 21302249576443526625107089)
    ·
      refine ⟨15976687182332644968830317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21302249576443526625107089 15976687182332644968830317)
      ·
        refine ⟨5991257693374741863311369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15976687182332644968830317 5991257693374741863311369)
        ·
          refine ⟨4493443270031056397483527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5991257693374741863311369 4493443270031056397483527)
          ·
            refine ⟨6740164905046584596225291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493443270031056397483527 6740164905046584596225291)
            ·
              refine ⟨10110247357569876894337937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740164905046584596225291 10110247357569876894337937)
              ·
                refine ⟨7582685518177407670753453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10110247357569876894337937 7582685518177407670753453)
                ·
                  refine ⟨2843507069316527876532545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7582685518177407670753453 2843507069316527876532545)
                  ·
                    refine ⟨2132630301987395907399409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2843507069316527876532545 2132630301987395907399409)
                    ·
                      refine ⟨1599472726490546930549557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132630301987395907399409 1599472726490546930549557)
                      ·
                        rfl

theorem cell23_3114962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3114962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114962 prefixEnd_3114962 := by exact prefixLift 3114962
  have htrace : WordTrace (prefixWord ++ tailWord_3114962) baseStart_3114962 baseEnd_3114962 := by
    simpa [prefixWord, tailWord_3114962, baseEnd_3114962] using wordTrace_append hprefix tailTrace_3114962
  have hstable : (prefixWord ++ tailWord_3114962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114962).length < 2 ^ (prefixWord ++ tailWord_3114962).sum := by decide
  have hdescent : baseEnd_3114962 < baseStart_3114962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114989 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_3114989 : Nat := 118140960795 + 3114989 * 2 ^ 59
def prefixEnd_3114989 : Nat := 4983230072969 + 3 ^ 40 * 3114989 * 2
def baseEnd_3114989 : Nat := 533162196822739441637311

theorem tailTrace_3114989 : CollatzResearch.WordTrace tailWord_3114989 prefixEnd_3114989 533162196822739441637311 := by
  unfold tailWord_3114989
  simp only [CollatzResearch.WordTrace]
  refine ⟨113612982511934325611804021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75741988341289550407869347 113612982511934325611804021)
  ·
    refine ⟨10651217110493843026106627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113612982511934325611804021 10651217110493843026106627)
    ·
      refine ⟨15976825665740764539159941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10651217110493843026106627 15976825665740764539159941)
      ·
        refine ⟨2995654812326393351092489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15976825665740764539159941 2995654812326393351092489)
        ·
          refine ⟨2246741109244795013319367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2995654812326393351092489 2246741109244795013319367)
          ·
            refine ⟨3370111663867192519979051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246741109244795013319367 3370111663867192519979051)
            ·
              refine ⟨5055167495800788779968577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370111663867192519979051 5055167495800788779968577)
              ·
                refine ⟨3791375621850591584976433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055167495800788779968577 3791375621850591584976433)
                ·
                  refine ⟨2843531716387943688732325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3791375621850591584976433 2843531716387943688732325)
                  ·
                    refine ⟨533162196822739441637311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2843531716387943688732325 533162196822739441637311)
                    ·
                      rfl

theorem cell23_3114989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_3114989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3114989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3114989 prefixEnd_3114989 := by exact prefixLift 3114989
  have htrace : WordTrace (prefixWord ++ tailWord_3114989) baseStart_3114989 baseEnd_3114989 := by
    simpa [prefixWord, tailWord_3114989, baseEnd_3114989] using wordTrace_append hprefix tailTrace_3114989
  have hstable : (prefixWord ++ tailWord_3114989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114989).length < 2 ^ (prefixWord ++ tailWord_3114989).sum := by decide
  have hdescent : baseEnd_3114989 < baseStart_3114989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115012 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3115012 : Nat := 118140960795 + 3115012 * 2 ^ 59
def prefixEnd_3115012 : Nat := 4983230072969 + 3 ^ 40 * 3115012 * 2
def baseEnd_3115012 : Nat := 1599498400523271734924327

theorem tailTrace_3115012 : CollatzResearch.WordTrace tailWord_3115012 prefixEnd_3115012 1599498400523271734924327 := by
  unfold tailWord_3115012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56806910695425500269945645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75742547593900667026594193 56806910695425500269945645)
  ·
    refine ⟨21302591510784562601229617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56806910695425500269945645 21302591510784562601229617)
    ·
      refine ⟨15976943633088421950922213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21302591510784562601229617 15976943633088421950922213)
      ·
        refine ⟨2995676931204079115797915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15976943633088421950922213 2995676931204079115797915)
        ·
          refine ⟨4493515396806118673696873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995676931204079115797915 4493515396806118673696873)
          ·
            refine ⟨3370136547604589005272655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4493515396806118673696873 3370136547604589005272655)
            ·
              refine ⟨5055204821406883507908983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370136547604589005272655 5055204821406883507908983)
              ·
                refine ⟨7582807232110325261863475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055204821406883507908983 7582807232110325261863475)
                ·
                  refine ⟨11374210848165487892795213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7582807232110325261863475 11374210848165487892795213)
                  ·
                    refine ⟨4265329068062057959798205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11374210848165487892795213 4265329068062057959798205)
                    ·
                      refine ⟨1599498400523271734924327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4265329068062057959798205 1599498400523271734924327)
                      ·
                        rfl

theorem cell23_3115012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3115012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115012 prefixEnd_3115012 := by exact prefixLift 3115012
  have htrace : WordTrace (prefixWord ++ tailWord_3115012) baseStart_3115012 baseEnd_3115012 := by
    simpa [prefixWord, tailWord_3115012, baseEnd_3115012] using wordTrace_append hprefix tailTrace_3115012
  have hstable : (prefixWord ++ tailWord_3115012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115012).length < 2 ^ (prefixWord ++ tailWord_3115012).sum := by decide
  have hdescent : baseEnd_3115012 < baseStart_3115012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115051 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3]
def baseStart_3115051 : Nat := 118140960795 + 3115051 * 2 ^ 59
def prefixEnd_3115051 : Nat := 4983230072969 + 3 ^ 40 * 3115051 * 2
def baseEnd_3115051 : Nat := 1599518426268797082336647

theorem tailTrace_3115051 : CollatzResearch.WordTrace tailWord_3115051 prefixEnd_3115051 1599518426268797082336647 := by
  unfold tailWord_3115051
  simp only [CollatzResearch.WordTrace]
  refine ⟨113615243837709710200561007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75743495891806473467040671 113615243837709710200561007)
  ·
    refine ⟨170422865756564565300841511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113615243837709710200561007 170422865756564565300841511)
    ·
      refine ⟨255634298634846847951262267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170422865756564565300841511 255634298634846847951262267)
      ·
        refine ⟨383451447952270271926893401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255634298634846847951262267 383451447952270271926893401)
        ·
          refine ⟨287588585964202703945170051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383451447952270271926893401 287588585964202703945170051)
          ·
            refine ⟨431382878946304055917755077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287588585964202703945170051 431382878946304055917755077)
            ·
              refine ⟨80884289802432010484579077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431382878946304055917755077 80884289802432010484579077)
              ·
                refine ⟨15165804337956001965858577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80884289802432010484579077 15165804337956001965858577)
                ·
                  refine ⟨11374353253467001474393933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15165804337956001965858577 11374353253467001474393933)
                  ·
                    refine ⟨4265382470050125552897725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11374353253467001474393933 4265382470050125552897725)
                    ·
                      refine ⟨1599518426268797082336647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4265382470050125552897725 1599518426268797082336647)
                      ·
                        rfl

theorem cell23_3115051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3].length) (baseStart_3115051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115051 prefixEnd_3115051 := by exact prefixLift 3115051
  have htrace : WordTrace (prefixWord ++ tailWord_3115051) baseStart_3115051 baseEnd_3115051 := by
    simpa [prefixWord, tailWord_3115051, baseEnd_3115051] using wordTrace_append hprefix tailTrace_3115051
  have hstable : (prefixWord ++ tailWord_3115051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115051).length < 2 ^ (prefixWord ++ tailWord_3115051).sum := by decide
  have hdescent : baseEnd_3115051 < baseStart_3115051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115058 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_3115058 : Nat := 118140960795 + 3115058 * 2 ^ 59
def prefixEnd_3115058 : Nat := 4983230072969 + 3 ^ 40 * 3115058 * 2
def baseEnd_3115058 : Nat := 177724668959264283883235

theorem tailTrace_3115058 : CollatzResearch.WordTrace tailWord_3115058 prefixEnd_3115058 177724668959264283883235 := by
  unfold tailWord_3115058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28403874787171087599016457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75743666099122900264043885 28403874787171087599016457)
  ·
    refine ⟨21302906090378315699262343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28403874787171087599016457 21302906090378315699262343)
    ·
      refine ⟨31954359135567473548893515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21302906090378315699262343 31954359135567473548893515)
      ·
        refine ⟨47931538703351210323340273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31954359135567473548893515 47931538703351210323340273)
        ·
          refine ⟨35948654027513407742505205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47931538703351210323340273 35948654027513407742505205)
          ·
            refine ⟨3370186315079381975859863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35948654027513407742505205 3370186315079381975859863)
            ·
              refine ⟨5055279472619072963789795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370186315079381975859863 5055279472619072963789795)
              ·
                refine ⟨7582919208928609445684693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055279472619072963789795 7582919208928609445684693)
                ·
                  refine ⟨177724668959264283883235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7582919208928609445684693 177724668959264283883235)
                  ·
                    rfl

theorem cell23_3115058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_3115058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115058 prefixEnd_3115058 := by exact prefixLift 3115058
  have htrace : WordTrace (prefixWord ++ tailWord_3115058) baseStart_3115058 baseEnd_3115058 := by
    simpa [prefixWord, tailWord_3115058, baseEnd_3115058] using wordTrace_append hprefix tailTrace_3115058
  have hstable : (prefixWord ++ tailWord_3115058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115058).length < 2 ^ (prefixWord ++ tailWord_3115058).sum := by decide
  have hdescent : baseEnd_3115058 < baseStart_3115058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115108 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_3115108 : Nat := 118140960795 + 3115108 * 2 ^ 59
def prefixEnd_3115108 : Nat := 4983230072969 + 3 ^ 40 * 3115108 * 2
def baseEnd_3115108 : Nat := 1599547694666103359323885

theorem tailTrace_3115108 : CollatzResearch.WordTrace tailWord_3115108 prefixEnd_3115108 1599547694666103359323885 := by
  unfold tailWord_3115108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56808661399251604467692989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75744881865668805956923985 56808661399251604467692989)
  ·
    refine ⟨21303248024719351675384871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56808661399251604467692989 21303248024719351675384871)
    ·
      refine ⟨31954872037079027513077307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21303248024719351675384871 31954872037079027513077307)
      ·
        refine ⟨47932308055618541269615961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31954872037079027513077307 47932308055618541269615961)
        ·
          refine ⟨35949231041713905952211971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47932308055618541269615961 35949231041713905952211971)
          ·
            refine ⟨53923846562570858928317957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35949231041713905952211971 53923846562570858928317957)
            ·
              refine ⟨10110721230482036049059617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53923846562570858928317957 10110721230482036049059617)
              ·
                refine ⟨7583040922861527036794713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10110721230482036049059617 7583040922861527036794713)
                ·
                  refine ⟨5687280692146145277596035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7583040922861527036794713 5687280692146145277596035)
                  ·
                    refine ⟨8530921038219217916394053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5687280692146145277596035 8530921038219217916394053)
                    ·
                      refine ⟨1599547694666103359323885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8530921038219217916394053 1599547694666103359323885)
                      ·
                        rfl

theorem cell23_3115108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_3115108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115108 prefixEnd_3115108 := by exact prefixLift 3115108
  have htrace : WordTrace (prefixWord ++ tailWord_3115108) baseStart_3115108 baseEnd_3115108 := by
    simpa [prefixWord, tailWord_3115108, baseEnd_3115108] using wordTrace_append hprefix tailTrace_3115108
  have hstable : (prefixWord ++ tailWord_3115108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115108).length < 2 ^ (prefixWord ++ tailWord_3115108).sum := by decide
  have hdescent : baseEnd_3115108 < baseStart_3115108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115111 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3115111 : Nat := 118140960795 + 3115111 * 2 ^ 59
def prefixEnd_3115111 : Nat := 4983230072969 + 3 ^ 40 * 3115111 * 2
def baseEnd_3115111 : Nat := 1599549235108066847586371

theorem tailTrace_3115111 : CollatzResearch.WordTrace tailWord_3115111 prefixEnd_3115111 1599549235108066847586371 := by
  unfold tailWord_3115111
  simp only [CollatzResearch.WordTrace]
  refine ⟨113617432217492340447745187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75744954811661560298496791 113617432217492340447745187)
  ·
    refine ⟨170426148326238510671617781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113617432217492340447745187 170426148326238510671617781)
    ·
      refine ⟨15977451405584860375464167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170426148326238510671617781 15977451405584860375464167)
      ·
        refine ⟨23966177108377290563196251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977451405584860375464167 23966177108377290563196251)
        ·
          refine ⟨35949265662565935844794377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23966177108377290563196251 35949265662565935844794377)
          ·
            refine ⟨26961949246924451883595783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35949265662565935844794377 26961949246924451883595783)
            ·
              refine ⟨40442923870386677825393675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26961949246924451883595783 40442923870386677825393675)
              ·
                refine ⟨60664385805580016738090513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40442923870386677825393675 60664385805580016738090513)
                ·
                  refine ⟨45498289354185012553567885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60664385805580016738090513 45498289354185012553567885)
                  ·
                    refine ⟨17061858507819379707587957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45498289354185012553567885 17061858507819379707587957)
                    ·
                      refine ⟨1599549235108066847586371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17061858507819379707587957 1599549235108066847586371)
                      ·
                        rfl

theorem cell23_3115111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3115111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115111 prefixEnd_3115111 := by exact prefixLift 3115111
  have htrace : WordTrace (prefixWord ++ tailWord_3115111) baseStart_3115111 baseEnd_3115111 := by
    simpa [prefixWord, tailWord_3115111, baseEnd_3115111] using wordTrace_append hprefix tailTrace_3115111
  have hstable : (prefixWord ++ tailWord_3115111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115111).length < 2 ^ (prefixWord ++ tailWord_3115111).sum := by decide
  have hdescent : baseEnd_3115111 < baseStart_3115111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115165 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 6]
def baseStart_3115165 : Nat := 118140960795 + 3115165 * 2 ^ 59
def prefixEnd_3115165 : Nat := 4983230072969 + 3 ^ 40 * 3115165 * 2
def baseEnd_3115165 : Nat := 177730773673712181812347

theorem tailTrace_3115165 : CollatzResearch.WordTrace tailWord_3115165 prefixEnd_3115165 177730773673712181812347 := by
  unfold tailWord_3115165
  simp only [CollatzResearch.WordTrace]
  refine ⟨113619401759296707670210949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75746267839531138446807299 113619401759296707670210949)
  ·
    refine ⟨21303637829868132688164553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113619401759296707670210949 21303637829868132688164553)
    ·
      refine ⟨15977728372401099516123415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21303637829868132688164553 15977728372401099516123415)
      ·
        refine ⟨23966592558601649274185123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977728372401099516123415 23966592558601649274185123)
        ·
          refine ⟨35949888837902473911277685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23966592558601649274185123 35949888837902473911277685)
          ·
            refine ⟨3370302078553356929182283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35949888837902473911277685 3370302078553356929182283)
            ·
              refine ⟨5055453117830035393773425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370302078553356929182283 5055453117830035393773425)
              ·
                refine ⟨3791589838372526545330069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055453117830035393773425 3791589838372526545330069)
                ·
                  refine ⟨177730773673712181812347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3791589838372526545330069 177730773673712181812347)
                  ·
                    rfl

theorem cell23_3115165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_3115165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115165 prefixEnd_3115165 := by exact prefixLift 3115165
  have htrace : WordTrace (prefixWord ++ tailWord_3115165) baseStart_3115165 baseEnd_3115165 := by
    simpa [prefixWord, tailWord_3115165, baseEnd_3115165] using wordTrace_append hprefix tailTrace_3115165
  have hstable : (prefixWord ++ tailWord_3115165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115165).length < 2 ^ (prefixWord ++ tailWord_3115165).sum := by decide
  have hdescent : baseEnd_3115165 < baseStart_3115165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115248 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_3115248 : Nat := 118140960795 + 3115248 * 2 ^ 59
def prefixEnd_3115248 : Nat := 4983230072969 + 3 ^ 40 * 3115248 * 2
def baseEnd_3115248 : Nat := 1599619581957732811573241

theorem tailTrace_3115248 : CollatzResearch.WordTrace tailWord_3115248 prefixEnd_3115248 1599619581957732811573241 := by
  unfold tailWord_3115248
  simp only [CollatzResearch.WordTrace]
  refine ⟨56811214508998006422741199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75748286011997341896988265 56811214508998006422741199)
  ·
    refine ⟨85216821763497009634111799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56811214508998006422741199 85216821763497009634111799)
    ·
      refine ⟨127825232645245514451167699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85216821763497009634111799 127825232645245514451167699)
      ·
        refine ⟨191737848967868271676751549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127825232645245514451167699 191737848967868271676751549)
        ·
          refine ⟨71901693362950601878781831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191737848967868271676751549 71901693362950601878781831)
          ·
            refine ⟨107852540044425902818172747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71901693362950601878781831 107852540044425902818172747)
            ·
              refine ⟨161778810066638854227259121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107852540044425902818172747 161778810066638854227259121)
              ·
                refine ⟨121334107549979140670444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161778810066638854227259121 121334107549979140670444341)
                ·
                  refine ⟨11375072582810544437854157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121334107549979140670444341 11375072582810544437854157)
                  ·
                    refine ⟨4265652218553954164195309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11375072582810544437854157 4265652218553954164195309)
                    ·
                      refine ⟨1599619581957732811573241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4265652218553954164195309 1599619581957732811573241)
                      ·
                        rfl

theorem cell23_3115248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_3115248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115248 prefixEnd_3115248 := by exact prefixLift 3115248
  have htrace : WordTrace (prefixWord ++ tailWord_3115248) baseStart_3115248 baseEnd_3115248 := by
    simpa [prefixWord, tailWord_3115248, baseEnd_3115248] using wordTrace_append hprefix tailTrace_3115248
  have hstable : (prefixWord ++ tailWord_3115248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115248).length < 2 ^ (prefixWord ++ tailWord_3115248).sum := by decide
  have hdescent : baseEnd_3115248 < baseStart_3115248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115265 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3115265 : Nat := 118140960795 + 3115265 * 2 ^ 59
def prefixEnd_3115265 : Nat := 4983230072969 + 3 ^ 40 * 3115265 * 2
def baseEnd_3115265 : Nat := 1599628311128859245060663

theorem tailTrace_3115265 : CollatzResearch.WordTrace tailWord_3115265 prefixEnd_3115265 1599628311128859245060663 := by
  unfold tailWord_3115265
  simp only [CollatzResearch.WordTrace]
  refine ⟨113623049058934424748851249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75748699372622949832567499 113623049058934424748851249)
  ·
    refine ⟨85217286794200818561638437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113623049058934424748851249 85217286794200818561638437)
    ·
      refine ⟨15978241273912653480307207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85217286794200818561638437 15978241273912653480307207)
      ·
        refine ⟨23967361910868980220460811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15978241273912653480307207 23967361910868980220460811)
        ·
          refine ⟨35951042866303470330691217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23967361910868980220460811 35951042866303470330691217)
          ·
            refine ⟨26963282149727602748018413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35951042866303470330691217 26963282149727602748018413)
            ·
              refine ⟨10111230806147851030506905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26963282149727602748018413 10111230806147851030506905)
              ·
                refine ⟨7583423104610888272880179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10111230806147851030506905 7583423104610888272880179)
                ·
                  refine ⟨11375134656916332409320269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583423104610888272880179 11375134656916332409320269)
                  ·
                    refine ⟨4265675496343624653495101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11375134656916332409320269 4265675496343624653495101)
                    ·
                      refine ⟨1599628311128859245060663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4265675496343624653495101 1599628311128859245060663)
                      ·
                        rfl

theorem cell23_3115265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3115265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115265 prefixEnd_3115265 := by exact prefixLift 3115265
  have htrace : WordTrace (prefixWord ++ tailWord_3115265) baseStart_3115265 baseEnd_3115265 := by
    simpa [prefixWord, tailWord_3115265, baseEnd_3115265] using wordTrace_append hprefix tailTrace_3115265
  have hstable : (prefixWord ++ tailWord_3115265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115265).length < 2 ^ (prefixWord ++ tailWord_3115265).sum := by decide
  have hdescent : baseEnd_3115265 < baseStart_3115265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115288 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3115288 : Nat := 118140960795 + 3115288 * 2 ^ 59
def prefixEnd_3115288 : Nat := 4983230072969 + 3 ^ 40 * 3115288 * 2
def baseEnd_3115288 : Nat := 1599640121183912655073057

theorem tailTrace_3115288 : CollatzResearch.WordTrace tailWord_3115288 prefixEnd_3115288 1599640121183912655073057 := by
  unfold tailWord_3115288
  simp only [CollatzResearch.WordTrace]
  refine ⟨56811943968925549838469259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75749258625234066451292345 56811943968925549838469259)
  ·
    refine ⟨85217915953388324757703889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56811943968925549838469259 85217915953388324757703889)
    ·
      refine ⟨63913436965041243568277917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85217915953388324757703889 63913436965041243568277917)
      ·
        refine ⟨23967538861890466338104219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63913436965041243568277917 23967538861890466338104219)
        ·
          refine ⟨35951308292835699507156329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23967538861890466338104219 35951308292835699507156329)
          ·
            refine ⟨26963481219626774630367247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35951308292835699507156329 26963481219626774630367247)
            ·
              refine ⟨40445221829440161945550871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26963481219626774630367247 40445221829440161945550871)
              ·
                refine ⟨60667832744160242918326307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40445221829440161945550871 60667832744160242918326307)
                ·
                  refine ⟨91001749116240364377489461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60667832744160242918326307 91001749116240364377489461)
                  ·
                    refine ⟨8531413979647534160389637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91001749116240364377489461 8531413979647534160389637)
                    ·
                      refine ⟨1599640121183912655073057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8531413979647534160389637 1599640121183912655073057)
                      ·
                        rfl

theorem cell23_3115288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3115288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115288 prefixEnd_3115288 := by exact prefixLift 3115288
  have htrace : WordTrace (prefixWord ++ tailWord_3115288) baseStart_3115288 baseEnd_3115288 := by
    simpa [prefixWord, tailWord_3115288, baseEnd_3115288] using wordTrace_append hprefix tailTrace_3115288
  have hstable : (prefixWord ++ tailWord_3115288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115288).length < 2 ^ (prefixWord ++ tailWord_3115288).sum := by decide
  have hdescent : baseEnd_3115288 < baseStart_3115288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115308 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3115308 : Nat := 118140960795 + 3115308 * 2 ^ 59
def prefixEnd_3115308 : Nat := 4983230072969 + 3 ^ 40 * 3115308 * 2
def baseEnd_3115308 : Nat := 1599650390797002576822965

theorem tailTrace_3115308 : CollatzResearch.WordTrace tailWord_3115308 prefixEnd_3115308 1599650390797002576822965 := by
  unfold tailWord_3115308
  simp only [CollatzResearch.WordTrace]
  refine ⟨56812308698889321546333289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75749744931852428728444385 56812308698889321546333289)
  ·
    refine ⟨42609231524166991159749967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56812308698889321546333289 42609231524166991159749967)
    ·
      refine ⟨63913847286250486739624951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42609231524166991159749967 63913847286250486739624951)
      ·
        refine ⟨95870770929375730109437427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63913847286250486739624951 95870770929375730109437427)
        ·
          refine ⟨143806156394063595164156141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95870770929375730109437427 143806156394063595164156141)
          ·
            refine ⟨53927308647773848186558553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143806156394063595164156141 53927308647773848186558553)
            ·
              refine ⟨40445481485830386139918915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53927308647773848186558553 40445481485830386139918915)
              ·
                refine ⟨60668222228745579209878373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40445481485830386139918915 60668222228745579209878373)
                ·
                  refine ⟨11375291667889796101852195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60668222228745579209878373 11375291667889796101852195)
                  ·
                    refine ⟨17062937501834694152778293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11375291667889796101852195 17062937501834694152778293)
                    ·
                      refine ⟨1599650390797002576822965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17062937501834694152778293 1599650390797002576822965)
                      ·
                        rfl

theorem cell23_3115308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3115308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115308 prefixEnd_3115308 := by exact prefixLift 3115308
  have htrace : WordTrace (prefixWord ++ tailWord_3115308) baseStart_3115308 baseEnd_3115308 := by
    simpa [prefixWord, tailWord_3115308, baseEnd_3115308] using wordTrace_append hprefix tailTrace_3115308
  have hstable : (prefixWord ++ tailWord_3115308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115308).length < 2 ^ (prefixWord ++ tailWord_3115308).sum := by decide
  have hdescent : baseEnd_3115308 < baseStart_3115308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115322 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_3115322 : Nat := 118140960795 + 3115322 * 2 ^ 59
def prefixEnd_3115322 : Nat := 4983230072969 + 3 ^ 40 * 3115322 * 2
def baseEnd_3115322 : Nat := 1599657579526165522047901

theorem tailTrace_3115322 : CollatzResearch.WordTrace tailWord_3115322 prefixEnd_3115322 1599657579526165522047901 := by
  unfold tailWord_3115322
  simp only [CollatzResearch.WordTrace]
  refine ⟨28406282004931980870919055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75750085346485282322450813 28406282004931980870919055)
  ·
    refine ⟨42609423007397971306378583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28406282004931980870919055 42609423007397971306378583)
    ·
      refine ⟨63914134511096956959567875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42609423007397971306378583 63914134511096956959567875)
      ·
        refine ⟨95871201766645435439351813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63914134511096956959567875 95871201766645435439351813)
        ·
          refine ⟨17975850331246019144878465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95871201766645435439351813 17975850331246019144878465)
          ·
            refine ⟨13481887748434514358658849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17975850331246019144878465 13481887748434514358658849)
            ·
              refine ⟨10111415811325885768994137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13481887748434514358658849 10111415811325885768994137)
              ·
                refine ⟨7583561858494414326745603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10111415811325885768994137 7583561858494414326745603)
                ·
                  refine ⟨11375342787741621490118405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583561858494414326745603 11375342787741621490118405)
                  ·
                    refine ⟨2132876772701554029397201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11375342787741621490118405 2132876772701554029397201)
                    ·
                      refine ⟨1599657579526165522047901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132876772701554029397201 1599657579526165522047901)
                      ·
                        rfl

theorem cell23_3115322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_3115322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115322 prefixEnd_3115322 := by exact prefixLift 3115322
  have htrace : WordTrace (prefixWord ++ tailWord_3115322) baseStart_3115322 baseEnd_3115322 := by
    simpa [prefixWord, tailWord_3115322, baseEnd_3115322] using wordTrace_append hprefix tailTrace_3115322
  have hstable : (prefixWord ++ tailWord_3115322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115322).length < 2 ^ (prefixWord ++ tailWord_3115322).sum := by decide
  have hdescent : baseEnd_3115322 < baseStart_3115322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115326 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_3115326 : Nat := 118140960795 + 3115326 * 2 ^ 59
def prefixEnd_3115326 : Nat := 4983230072969 + 3 ^ 40 * 3115326 * 2
def baseEnd_3115326 : Nat := 1599659633448783506397883

theorem tailTrace_3115326 : CollatzResearch.WordTrace tailWord_3115326 prefixEnd_3115326 1599659633448783506397883 := by
  unfold tailWord_3115326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203159238964179020852729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75750182607808954777881221 14203159238964179020852729)
  ·
    refine ⟨10652369429223134265639547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14203159238964179020852729 10652369429223134265639547)
    ·
      refine ⟨15978554143834701398459321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10652369429223134265639547 15978554143834701398459321)
      ·
        refine ⟨11983915607876026048844491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15978554143834701398459321 11983915607876026048844491)
        ·
          refine ⟨17975873411814039073266737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983915607876026048844491 17975873411814039073266737)
          ·
            refine ⟨13481905058860529304950053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17975873411814039073266737 13481905058860529304950053)
            ·
              refine ⟨2527857198536349244678135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13481905058860529304950053 2527857198536349244678135)
              ·
                refine ⟨3791785797804523867017203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527857198536349244678135 3791785797804523867017203)
                ·
                  refine ⟨5687678696706785800525805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791785797804523867017203 5687678696706785800525805)
                  ·
                    refine ⟨2132879511265044675197177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5687678696706785800525805 2132879511265044675197177)
                    ·
                      refine ⟨1599659633448783506397883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2132879511265044675197177 1599659633448783506397883)
                      ·
                        rfl

theorem cell23_3115326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_3115326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115326 prefixEnd_3115326 := by exact prefixLift 3115326
  have htrace : WordTrace (prefixWord ++ tailWord_3115326) baseStart_3115326 baseEnd_3115326 := by
    simpa [prefixWord, tailWord_3115326, baseEnd_3115326] using wordTrace_append hprefix tailTrace_3115326
  have hstable : (prefixWord ++ tailWord_3115326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115326).length < 2 ^ (prefixWord ++ tailWord_3115326).sum := by decide
  have hdescent : baseEnd_3115326 < baseStart_3115326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115345 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 7]
def baseStart_3115345 : Nat := 118140960795 + 3115345 * 2 ^ 59
def prefixEnd_3115345 : Nat := 4983230072969 + 3 ^ 40 * 3115345 * 2
def baseEnd_3115345 : Nat := 177741043286802103562255

theorem tailTrace_3115345 : CollatzResearch.WordTrace tailWord_3115345 prefixEnd_3115345 177741043286802103562255 := by
  unfold tailWord_3115345
  simp only [CollatzResearch.WordTrace]
  refine ⟨113625966898644598411763489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75750644599096398941175659 113625966898644598411763489)
  ·
    refine ⟨85219475173983448808822617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113625966898644598411763489 85219475173983448808822617)
    ·
      refine ⟨63914606380487586606616963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85219475173983448808822617 63914606380487586606616963)
      ·
        refine ⟨95871909570731379909925445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63914606380487586606616963 95871909570731379909925445)
        ·
          refine ⟨17975983044512133733111021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95871909570731379909925445 17975983044512133733111021)
          ·
            refine ⟨6740993641692050149916633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17975983044512133733111021 6740993641692050149916633)
            ·
              refine ⟨5055745231269037612437475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6740993641692050149916633 5055745231269037612437475)
              ·
                refine ⟨7583617846903556418656213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055745231269037612437475 7583617846903556418656213)
                ·
                  refine ⟨177741043286802103562255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7583617846903556418656213 177741043286802103562255)
                  ·
                    rfl

theorem cell23_3115345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_3115345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115345 prefixEnd_3115345 := by exact prefixLift 3115345
  have htrace : WordTrace (prefixWord ++ tailWord_3115345) baseStart_3115345 baseEnd_3115345 := by
    simpa [prefixWord, tailWord_3115345, baseEnd_3115345] using wordTrace_append hprefix tailTrace_3115345
  have hstable : (prefixWord ++ tailWord_3115345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115345).length < 2 ^ (prefixWord ++ tailWord_3115345).sum := by decide
  have hdescent : baseEnd_3115345 < baseStart_3115345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115415 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3115415 : Nat := 118140960795 + 3115415 * 2 ^ 59
def prefixEnd_3115415 : Nat := 4983230072969 + 3 ^ 40 * 3115415 * 2
def baseEnd_3115415 : Nat := 1599705333227033658184973

theorem tailTrace_3115415 : CollatzResearch.WordTrace tailWord_3115415 prefixEnd_3115415 1599705333227033658184973 := by
  unfold tailWord_3115415
  simp only [CollatzResearch.WordTrace]
  refine ⟨113628520008391000366811699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75752346672260666911207799 113628520008391000366811699)
  ·
    refine ⟨170442780012586500550217549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113628520008391000366811699 170442780012586500550217549)
    ·
      refine ⟨63916042504719937706331581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170442780012586500550217549 63916042504719937706331581)
      ·
        refine ⟨23968515939269976639874343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63916042504719937706331581 23968515939269976639874343)
        ·
          refine ⟨35952773908904964959811515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23968515939269976639874343 35952773908904964959811515)
          ·
            refine ⟨53929160863357447439717273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35952773908904964959811515 53929160863357447439717273)
            ·
              refine ⟨40446870647518085579787955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53929160863357447439717273 40446870647518085579787955)
              ·
                refine ⟨60670305971277128369681933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40446870647518085579787955 60670305971277128369681933)
                ·
                  refine ⟨22751364739228923138630725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60670305971277128369681933 22751364739228923138630725)
                  ·
                    refine ⟨4265880888605423088493261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22751364739228923138630725 4265880888605423088493261)
                    ·
                      refine ⟨1599705333227033658184973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4265880888605423088493261 1599705333227033658184973)
                      ·
                        rfl

theorem cell23_3115415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3115415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115415 prefixEnd_3115415 := by exact prefixLift 3115415
  have htrace : WordTrace (prefixWord ++ tailWord_3115415) baseStart_3115415 baseEnd_3115415 := by
    simpa [prefixWord, tailWord_3115415, baseEnd_3115415] using wordTrace_append hprefix tailTrace_3115415
  have hstable : (prefixWord ++ tailWord_3115415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115415).length < 2 ^ (prefixWord ++ tailWord_3115415).sum := by decide
  have hdescent : baseEnd_3115415 < baseStart_3115415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115452 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 6]
def baseStart_3115452 : Nat := 118140960795 + 3115452 * 2 ^ 59
def prefixEnd_3115452 : Nat := 4983230072969 + 3 ^ 40 * 3115452 * 2
def baseEnd_3115452 : Nat := 177747148001250001491367

theorem tailTrace_3115452 : CollatzResearch.WordTrace tailWord_3115452 prefixEnd_3115452 177747148001250001491367 := by
  unfold tailWord_3115452
  simp only [CollatzResearch.WordTrace]
  refine ⟨56814934754628477842954305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75753246339504637123939073 56814934754628477842954305)
  ·
    refine ⟨42611201065971358382215729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56814934754628477842954305 42611201065971358382215729)
    ·
      refine ⟨31958400799478518786661797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42611201065971358382215729 31958400799478518786661797)
      ·
        refine ⟨5992200149902222272499087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31958400799478518786661797 5992200149902222272499087)
        ·
          refine ⟨8988300224853333408748631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992200149902222272499087 8988300224853333408748631)
          ·
            refine ⟨13482450337280000113122947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988300224853333408748631 13482450337280000113122947)
            ·
              refine ⟨20223675505920000169684421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13482450337280000113122947 20223675505920000169684421)
              ·
                refine ⟨3791939157360000031815829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20223675505920000169684421 3791939157360000031815829)
                ·
                  refine ⟨177747148001250001491367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3791939157360000031815829 177747148001250001491367)
                  ·
                    rfl

theorem cell23_3115452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_3115452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115452 prefixEnd_3115452 := by exact prefixLift 3115452
  have htrace : WordTrace (prefixWord ++ tailWord_3115452) baseStart_3115452 baseEnd_3115452 := by
    simpa [prefixWord, tailWord_3115452, baseEnd_3115452] using wordTrace_append hprefix tailTrace_3115452
  have hstable : (prefixWord ++ tailWord_3115452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115452).length < 2 ^ (prefixWord ++ tailWord_3115452).sum := by decide
  have hdescent : baseEnd_3115452 < baseStart_3115452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115465 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_3115465 : Nat := 118140960795 + 3115465 * 2 ^ 59
def prefixEnd_3115465 : Nat := 4983230072969 + 3 ^ 40 * 3115465 * 2
def baseEnd_3115465 : Nat := 533243669086586154186581

theorem tailTrace_3115465 : CollatzResearch.WordTrace tailWord_3115465 prefixEnd_3115465 533243669086586154186581 := by
  unfold tailWord_3115465
  simp only [CollatzResearch.WordTrace]
  refine ⟨113630343658209858906131849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75753562438806572604087899 113630343658209858906131849)
  ·
    refine ⟨85222757743657394179598887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113630343658209858906131849 85222757743657394179598887)
    ·
      refine ⟨127834136615486091269398331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85222757743657394179598887 127834136615486091269398331)
      ·
        refine ⟨191751204923229136904097497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127834136615486091269398331 191751204923229136904097497)
        ·
          refine ⟨143813403692421852678073123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191751204923229136904097497 143813403692421852678073123)
          ·
            refine ⟨215720105538632779017109685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143813403692421852678073123 215720105538632779017109685)
            ·
              refine ⟨20223759894246823032854033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215720105538632779017109685 20223759894246823032854033)
              ·
                refine ⟨15167819920685117274640525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20223759894246823032854033 15167819920685117274640525)
                ·
                  refine ⟨5687932470256918977990197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15167819920685117274640525 5687932470256918977990197)
                  ·
                    refine ⟨533243669086586154186581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5687932470256918977990197 533243669086586154186581)
                    ·
                      rfl

theorem cell23_3115465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_3115465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115465 prefixEnd_3115465 := by exact prefixLift 3115465
  have htrace : WordTrace (prefixWord ++ tailWord_3115465) baseStart_3115465 baseEnd_3115465 := by
    simpa [prefixWord, tailWord_3115465, baseEnd_3115465] using wordTrace_append hprefix tailTrace_3115465
  have hstable : (prefixWord ++ tailWord_3115465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115465).length < 2 ^ (prefixWord ++ tailWord_3115465).sum := by decide
  have hdescent : baseEnd_3115465 < baseStart_3115465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115482 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_3115482 : Nat := 118140960795 + 3115482 * 2 ^ 59
def prefixEnd_3115482 : Nat := 4983230072969 + 3 ^ 40 * 3115482 * 2
def baseEnd_3115482 : Nat := 533246578810294965349055

theorem tailTrace_3115482 : CollatzResearch.WordTrace tailWord_3115482 prefixEnd_3115482 533246578810294965349055 := by
  unfold tailWord_3115482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28407740924787067702375175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75753975799432180539667133 28407740924787067702375175)
  ·
    refine ⟨42611611387180601553562763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28407740924787067702375175 42611611387180601553562763)
    ·
      refine ⟨63917417080770902330344145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42611611387180601553562763 63917417080770902330344145)
      ·
        refine ⟨47938062810578176747758109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63917417080770902330344145 47938062810578176747758109)
        ·
          refine ⟨17976773553966816280409291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47938062810578176747758109 17976773553966816280409291)
          ·
            refine ⟨26965160330950224420613937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17976773553966816280409291 26965160330950224420613937)
            ·
              refine ⟨20223870248212668315460453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26965160330950224420613937 20223870248212668315460453)
              ·
                refine ⟨3791975671539875309148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20223870248212668315460453 3791975671539875309148835)
                ·
                  refine ⟨5687963507309812963723253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791975671539875309148835 5687963507309812963723253)
                  ·
                    refine ⟨533246578810294965349055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5687963507309812963723253 533246578810294965349055)
                    ·
                      rfl

theorem cell23_3115482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_3115482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115482 prefixEnd_3115482 := by exact prefixLift 3115482
  have htrace : WordTrace (prefixWord ++ tailWord_3115482) baseStart_3115482 baseEnd_3115482 := by
    simpa [prefixWord, tailWord_3115482, baseEnd_3115482] using wordTrace_append hprefix tailTrace_3115482
  have hstable : (prefixWord ++ tailWord_3115482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115482).length < 2 ^ (prefixWord ++ tailWord_3115482).sum := by decide
  have hdescent : baseEnd_3115482 < baseStart_3115482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115490 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3115490 : Nat := 118140960795 + 3115490 * 2 ^ 59
def prefixEnd_3115490 : Nat := 4983230072969 + 3 ^ 40 * 3115490 * 2
def baseEnd_3115490 : Nat := 533247948092040288249043

theorem tailTrace_3115490 : CollatzResearch.WordTrace tailWord_3115490 prefixEnd_3115490 533247948092040288249043 := by
  unfold tailWord_3115490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28407813870779822043947981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75754170322079525450527949 28407813870779822043947981)
  ·
    refine ⟨10652930201542433266480493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28407813870779822043947981 10652930201542433266480493)
    ·
      refine ⟨3994848825578412474930185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10652930201542433266480493 3994848825578412474930185)
      ·
        refine ⟨2996136619183809356197639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3994848825578412474930185 2996136619183809356197639)
        ·
          refine ⟨4494204928775714034296459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996136619183809356197639 4494204928775714034296459)
          ·
            refine ⟨6741307393163571051444689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494204928775714034296459 6741307393163571051444689)
            ·
              refine ⟨5055980544872678288583517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741307393163571051444689 5055980544872678288583517)
              ·
                refine ⟨1895992704327254358218819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5055980544872678288583517 1895992704327254358218819)
                ·
                  refine ⟨2843989056490881537328229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895992704327254358218819 2843989056490881537328229)
                  ·
                    refine ⟨533247948092040288249043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2843989056490881537328229 533247948092040288249043)
                    ·
                      rfl

theorem cell23_3115490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3115490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115490 prefixEnd_3115490 := by exact prefixLift 3115490
  have htrace : WordTrace (prefixWord ++ tailWord_3115490) baseStart_3115490 baseEnd_3115490 := by
    simpa [prefixWord, tailWord_3115490, baseEnd_3115490] using wordTrace_append hprefix tailTrace_3115490
  have hstable : (prefixWord ++ tailWord_3115490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115490).length < 2 ^ (prefixWord ++ tailWord_3115490).sum := by decide
  have hdescent : baseEnd_3115490 < baseStart_3115490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115496 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3115496 : Nat := 118140960795 + 3115496 * 2 ^ 59
def prefixEnd_3115496 : Nat := 4983230072969 + 3 ^ 40 * 3115496 * 2
def baseEnd_3115496 : Nat := 1599746925160047841272101

theorem tailTrace_3115496 : CollatzResearch.WordTrace tailWord_3115496 prefixEnd_3115496 1599746925160047841272101 := by
  unfold tailWord_3115496
  simp only [CollatzResearch.WordTrace]
  refine ⟨56815737160548775600255171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75754316214065034133673561 56815737160548775600255171)
  ·
    refine ⟨85223605740823163400382757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56815737160548775600255171 85223605740823163400382757)
    ·
      refine ⟨15979426076404343137571767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85223605740823163400382757 15979426076404343137571767)
      ·
        refine ⟨23969139114606514706357651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15979426076404343137571767 23969139114606514706357651)
        ·
          refine ⟨35953708671909772059536477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23969139114606514706357651 35953708671909772059536477)
          ·
            refine ⟨13482640751966164522326179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35953708671909772059536477 13482640751966164522326179)
            ·
              refine ⟨20223961127949246783489269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13482640751966164522326179 20223961127949246783489269)
              ·
                refine ⟨1895996355745241885952119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20223961127949246783489269 1895996355745241885952119)
                ·
                  refine ⟨2843994533617862828928179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895996355745241885952119 2843994533617862828928179)
                  ·
                    refine ⟨4265991800426794243392269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2843994533617862828928179 4265991800426794243392269)
                    ·
                      refine ⟨1599746925160047841272101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4265991800426794243392269 1599746925160047841272101)
                      ·
                        rfl

theorem cell23_3115496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3115496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115496 prefixEnd_3115496 := by exact prefixLift 3115496
  have htrace : WordTrace (prefixWord ++ tailWord_3115496) baseStart_3115496 baseEnd_3115496 := by
    simpa [prefixWord, tailWord_3115496, baseEnd_3115496] using wordTrace_append hprefix tailTrace_3115496
  have hstable : (prefixWord ++ tailWord_3115496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115496).length < 2 ^ (prefixWord ++ tailWord_3115496).sum := by decide
  have hdescent : baseEnd_3115496 < baseStart_3115496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
