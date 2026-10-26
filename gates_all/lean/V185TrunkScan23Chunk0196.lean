import V185TrunkScan23Chunk0195

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1160661 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 8]
def baseStart_1160661 : Nat := 118140960795 + 1160661 * 2 ^ 59
def prefixEnd_1160661 : Nat := 4983230072969 + 3 ^ 40 * 1160661 * 2
def baseEnd_1160661 : Nat := 66219663325354293577747

theorem tailTrace_1160661 : CollatzResearch.WordTrace tailWord_1160661 prefixEnd_1160661 66219663325354293577747 := by
  unfold tailWord_1160661
  simp only [CollatzResearch.WordTrace]
  refine ⟨42332784448130896962401837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28221856298753931308267891 42332784448130896962401837)
  ·
    refine ⟨15874794168049086360900689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42332784448130896962401837 15874794168049086360900689)
    ·
      refine ⟨11906095626036814770675517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15874794168049086360900689 11906095626036814770675517)
      ·
        refine ⟨4464785859763805539003319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11906095626036814770675517 4464785859763805539003319)
        ·
          refine ⟨6697178789645708308504979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464785859763805539003319 6697178789645708308504979)
          ·
            refine ⟨10045768184468562462757469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697178789645708308504979 10045768184468562462757469)
            ·
              refine ⟨3767163069175710923534051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10045768184468562462757469 3767163069175710923534051)
              ·
                refine ⟨5650744603763566385301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767163069175710923534051 5650744603763566385301077)
                ·
                  refine ⟨66219663325354293577747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5650744603763566385301077 66219663325354293577747)
                  ·
                    rfl

theorem cell23_1160661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_1160661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160661 prefixEnd_1160661 := by exact prefixLift 1160661
  have htrace : WordTrace (prefixWord ++ tailWord_1160661) baseStart_1160661 baseEnd_1160661 := by
    simpa [prefixWord, tailWord_1160661, baseEnd_1160661] using wordTrace_append hprefix tailTrace_1160661
  have hstable : (prefixWord ++ tailWord_1160661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160661).length < 2 ^ (prefixWord ++ tailWord_1160661).sum := by decide
  have hdescent : baseEnd_1160661 < baseStart_1160661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160665 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 1, 4]
def baseStart_1160665 : Nat := 118140960795 + 1160665 * 2 ^ 59
def prefixEnd_1160665 : Nat := 4983230072969 + 3 ^ 40 * 1160665 * 2
def baseEnd_1160665 : Nat := 198659674616935542183235

theorem tailTrace_1160665 : CollatzResearch.WordTrace tailWord_1160665 prefixEnd_1160665 198659674616935542183235 := by
  unfold tailWord_1160665
  simp only [CollatzResearch.WordTrace]
  refine ⟨42332930340116405645547449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28221953560077603763698299 42332930340116405645547449)
  ·
    refine ⟨31749697755087304234160587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42332930340116405645547449 31749697755087304234160587)
    ·
      refine ⟨47624546632630956351240881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31749697755087304234160587 47624546632630956351240881)
      ·
        refine ⟨35718409974473217263430661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47624546632630956351240881 35718409974473217263430661)
        ·
          refine ⟨6697201870213728236893249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35718409974473217263430661 6697201870213728236893249)
          ·
            refine ⟨5022901402660296177669937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6697201870213728236893249 5022901402660296177669937)
            ·
              refine ⟨3767176051995222133252453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022901402660296177669937 3767176051995222133252453)
              ·
                refine ⟨706345509749104149984835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3767176051995222133252453 706345509749104149984835)
                ·
                  refine ⟨1059518264623656224977253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706345509749104149984835 1059518264623656224977253)
                  ·
                    refine ⟨198659674616935542183235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059518264623656224977253 198659674616935542183235)
                    ·
                      rfl

theorem cell23_1160665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 4].length) (baseStart_1160665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160665 prefixEnd_1160665 := by exact prefixLift 1160665
  have htrace : WordTrace (prefixWord ++ tailWord_1160665) baseStart_1160665 baseEnd_1160665 := by
    simpa [prefixWord, tailWord_1160665, baseEnd_1160665] using wordTrace_append hprefix tailTrace_1160665
  have hstable : (prefixWord ++ tailWord_1160665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160665).length < 2 ^ (prefixWord ++ tailWord_1160665).sum := by decide
  have hdescent : baseEnd_1160665 < baseStart_1160665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160698 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_1160698 : Nat := 118140960795 + 1160698 * 2 ^ 59
def prefixEnd_1160698 : Nat := 4983230072969 + 3 ^ 40 * 1160698 * 2
def baseEnd_1160698 : Nat := 595995968712404997437053

theorem tailTrace_1160698 : CollatzResearch.WordTrace tailWord_1160698 prefixEnd_1160698 595995968712404997437053 := by
  unfold tailWord_1160698
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583533487249213070374687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28222755965997901520999165 10583533487249213070374687)
  ·
    refine ⟨15875300230873819605562031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10583533487249213070374687 15875300230873819605562031)
    ·
      refine ⟨23812950346310729408343047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15875300230873819605562031 23812950346310729408343047)
      ·
        refine ⟨35719425519466094112514571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23812950346310729408343047 35719425519466094112514571)
        ·
          refine ⟨53579138279199141168771857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35719425519466094112514571 53579138279199141168771857)
          ·
            refine ⟨40184353709399355876578893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53579138279199141168771857 40184353709399355876578893)
            ·
              refine ⟨15069132641024758453717085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40184353709399355876578893 15069132641024758453717085)
              ·
                refine ⟨5650924740384284420143907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15069132641024758453717085 5650924740384284420143907)
                ·
                  refine ⟨8476387110576426630215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650924740384284420143907 8476387110576426630215861)
                  ·
                    refine ⟨794661291616539996582737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8476387110576426630215861 794661291616539996582737)
                    ·
                      refine ⟨595995968712404997437053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794661291616539996582737 595995968712404997437053)
                      ·
                        rfl

theorem cell23_1160698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_1160698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160698 prefixEnd_1160698 := by exact prefixLift 1160698
  have htrace : WordTrace (prefixWord ++ tailWord_1160698) baseStart_1160698 baseEnd_1160698 := by
    simpa [prefixWord, tailWord_1160698, baseEnd_1160698] using wordTrace_append hprefix tailTrace_1160698
  have hstable : (prefixWord ++ tailWord_1160698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160698).length < 2 ^ (prefixWord ++ tailWord_1160698).sum := by decide
  have hdescent : baseEnd_1160698 < baseStart_1160698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160778 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1160778 : Nat := 118140960795 + 1160778 * 2 ^ 59
def prefixEnd_1160778 : Nat := 4983230072969 + 3 ^ 40 * 1160778 * 2
def baseEnd_1160778 : Nat := 596037047164764684436685

theorem tailTrace_1160778 : CollatzResearch.WordTrace tailWord_1160778 prefixEnd_1160778 596037047164764684436685 := by
  unfold tailWord_1160778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10584262947176756486102747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28224701192471350629607325 10584262947176756486102747)
  ·
    refine ⟨15876394420765134729154121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10584262947176756486102747 15876394420765134729154121)
    ·
      refine ⟨11907295815573851046865591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15876394420765134729154121 11907295815573851046865591)
      ·
        refine ⟨17860943723360776570298387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907295815573851046865591 17860943723360776570298387)
        ·
          refine ⟨26791415585041164855447581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17860943723360776570298387 26791415585041164855447581)
          ·
            refine ⟨10046780844390436820792843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26791415585041164855447581 10046780844390436820792843)
            ·
              refine ⟨15070171266585655231189265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10046780844390436820792843 15070171266585655231189265)
              ·
                refine ⟨11302628449939241423391949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15070171266585655231189265 11302628449939241423391949)
                ·
                  refine ⟨4238485668727215533771981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11302628449939241423391949 4238485668727215533771981)
                  ·
                    refine ⟨1589432125772705825164493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4238485668727215533771981 1589432125772705825164493)
                    ·
                      refine ⟨596037047164764684436685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589432125772705825164493 596037047164764684436685)
                      ·
                        rfl

theorem cell23_1160778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1160778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160778 prefixEnd_1160778 := by exact prefixLift 1160778
  have htrace : WordTrace (prefixWord ++ tailWord_1160778) baseStart_1160778 baseEnd_1160778 := by
    simpa [prefixWord, tailWord_1160778, baseEnd_1160778] using wordTrace_append hprefix tailTrace_1160778
  have hstable : (prefixWord ++ tailWord_1160778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160778).length < 2 ^ (prefixWord ++ tailWord_1160778).sum := by decide
  have hdescent : baseEnd_1160778 < baseStart_1160778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160829 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_1160829 : Nat := 118140960795 + 1160829 * 2 ^ 59
def prefixEnd_1160829 : Nat := 4983230072969 + 3 ^ 40 * 1160829 * 2
def baseEnd_1160829 : Nat := 596063234678143984898951

theorem tailTrace_1160829 : CollatzResearch.WordTrace tailWord_1160829 prefixEnd_1160829 596063234678143984898951 := by
  unfold tailWord_1160829
  simp only [CollatzResearch.WordTrace]
  refine ⟨42338911911522261654517541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28225941274348174436345027 42338911911522261654517541)
  ·
    refine ⟨7938545983410424060222039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42338911911522261654517541 7938545983410424060222039)
    ·
      refine ⟨11907818975115636090333059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7938545983410424060222039 11907818975115636090333059)
      ·
        refine ⟨17861728462673454135499589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907818975115636090333059 17861728462673454135499589)
        ·
          refine ⟨3349074086751272650406173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17861728462673454135499589 3349074086751272650406173)
          ·
            refine ⟨1255902782531727243902315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3349074086751272650406173 1255902782531727243902315)
            ·
              refine ⟨1883854173797590865853473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255902782531727243902315 1883854173797590865853473)
              ·
                refine ⟨1412890630348193149390105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883854173797590865853473 1412890630348193149390105)
                ·
                  refine ⟨1059667972761144862042579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412890630348193149390105 1059667972761144862042579)
                  ·
                    refine ⟨1589501959141717293063869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1059667972761144862042579 1589501959141717293063869)
                    ·
                      refine ⟨596063234678143984898951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589501959141717293063869 596063234678143984898951)
                      ·
                        rfl

theorem cell23_1160829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_1160829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160829 prefixEnd_1160829 := by exact prefixLift 1160829
  have htrace : WordTrace (prefixWord ++ tailWord_1160829) baseStart_1160829 baseEnd_1160829 := by
    simpa [prefixWord, tailWord_1160829, baseEnd_1160829] using wordTrace_append hprefix tailTrace_1160829
  have hstable : (prefixWord ++ tailWord_1160829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160829).length < 2 ^ (prefixWord ++ tailWord_1160829).sum := by decide
  have hdescent : baseEnd_1160829 < baseStart_1160829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160886 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1160886 : Nat := 118140960795 + 1160886 * 2 ^ 59
def prefixEnd_1160886 : Nat := 4983230072969 + 3 ^ 40 * 1160886 * 2
def baseEnd_1160886 : Nat := 596092503075450261886189

theorem tailTrace_1160886 : CollatzResearch.WordTrace tailWord_1160886 prefixEnd_1160886 596092503075450261886189 := by
  unfold tailWord_1160886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646311929519735024333907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28227327248210506926228341 2646311929519735024333907)
  ·
    refine ⟨3969467894279602536500861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646311929519735024333907 3969467894279602536500861)
    ·
      refine ⟨1488550460354850951187823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3969467894279602536500861 1488550460354850951187823)
      ·
        refine ⟨2232825690532276426781735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488550460354850951187823 2232825690532276426781735)
        ·
          refine ⟨3349238535798414640172603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232825690532276426781735 3349238535798414640172603)
          ·
            refine ⟨5023857803697621960258905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349238535798414640172603 5023857803697621960258905)
            ·
              refine ⟨3767893352773216470194179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5023857803697621960258905 3767893352773216470194179)
              ·
                refine ⟨5651840029159824705291269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767893352773216470194179 5651840029159824705291269)
                ·
                  refine ⟨1059720005467467132242113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5651840029159824705291269 1059720005467467132242113)
                  ·
                    refine ⟨794790004100600349181585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1059720005467467132242113 794790004100600349181585)
                    ·
                      refine ⟨596092503075450261886189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794790004100600349181585 596092503075450261886189)
                      ·
                        rfl

theorem cell23_1160886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1160886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160886 prefixEnd_1160886 := by exact prefixLift 1160886
  have htrace : WordTrace (prefixWord ++ tailWord_1160886) baseStart_1160886 baseEnd_1160886 := by
    simpa [prefixWord, tailWord_1160886, baseEnd_1160886] using wordTrace_append hprefix tailTrace_1160886
  have hstable : (prefixWord ++ tailWord_1160886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160886).length < 2 ^ (prefixWord ++ tailWord_1160886).sum := by decide
  have hdescent : baseEnd_1160886 < baseStart_1160886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160895 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 5, 2]
def baseStart_1160895 : Nat := 118140960795 + 1160895 * 2 ^ 59
def prefixEnd_1160895 : Nat := 4983230072969 + 3 ^ 40 * 1160895 * 2
def baseEnd_1160895 : Nat := 596097124401340726673647

theorem tailTrace_1160895 : CollatzResearch.WordTrace tailWord_1160895 prefixEnd_1160895 596097124401340726673647 := by
  unfold tailWord_1160895
  simp only [CollatzResearch.WordTrace]
  refine ⟨42341319129283154926420139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28227546086188769950946759 42341319129283154926420139)
  ·
    refine ⟨63511978693924732389630209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42341319129283154926420139 63511978693924732389630209)
    ·
      refine ⟨47633984020443549292222657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63511978693924732389630209 47633984020443549292222657)
      ·
        refine ⟨35725488015332661969166993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47633984020443549292222657 35725488015332661969166993)
        ·
          refine ⟨26794116011499496476875245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35725488015332661969166993 26794116011499496476875245)
          ·
            refine ⟨10047793504312311178828217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26794116011499496476875245 10047793504312311178828217)
            ·
              refine ⟨7535845128234233384121163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10047793504312311178828217 7535845128234233384121163)
              ·
                refine ⟨11303767692351350076181745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7535845128234233384121163 11303767692351350076181745)
                ·
                  refine ⟨8477825769263512557136309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11303767692351350076181745 8477825769263512557136309)
                  ·
                    refine ⟨794796165868454302231529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8477825769263512557136309 794796165868454302231529)
                    ·
                      refine ⟨596097124401340726673647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794796165868454302231529 596097124401340726673647)
                      ·
                        rfl

theorem cell23_1160895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_1160895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160895 prefixEnd_1160895 := by exact prefixLift 1160895
  have htrace : WordTrace (prefixWord ++ tailWord_1160895) baseStart_1160895 baseEnd_1160895 := by
    simpa [prefixWord, tailWord_1160895, baseEnd_1160895] using wordTrace_append hprefix tailTrace_1160895
  have hstable : (prefixWord ++ tailWord_1160895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160895).length < 2 ^ (prefixWord ++ tailWord_1160895).sum := by decide
  have hdescent : baseEnd_1160895 < baseStart_1160895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160942 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_1160942 : Nat := 118140960795 + 1160942 * 2 ^ 59
def prefixEnd_1160942 : Nat := 4983230072969 + 3 ^ 40 * 1160942 * 2
def baseEnd_1160942 : Nat := 596121257992102042785931

theorem tailTrace_1160942 : CollatzResearch.WordTrace tailWord_1160942 prefixEnd_1160942 596121257992102042785931 := by
  unfold tailWord_1160942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292879170014110244172635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28228688906741921302254053 5292879170014110244172635)
  ·
    refine ⟨7939318755021165366258953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5292879170014110244172635 7939318755021165366258953)
    ·
      refine ⟨5954489066265874024694215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7939318755021165366258953 5954489066265874024694215)
      ·
        refine ⟨8931733599398811037041323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5954489066265874024694215 8931733599398811037041323)
        ·
          refine ⟨13397600399098216555561985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8931733599398811037041323 13397600399098216555561985)
          ·
            refine ⟨10048200299323662416671489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13397600399098216555561985 10048200299323662416671489)
            ·
              refine ⟨7536150224492746812503617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10048200299323662416671489 7536150224492746812503617)
              ·
                refine ⟨5652112668369560109377713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7536150224492746812503617 5652112668369560109377713)
                ·
                  refine ⟨4239084501277170082033285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5652112668369560109377713 4239084501277170082033285)
                  ·
                    refine ⟨794828343989469390381241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239084501277170082033285 794828343989469390381241)
                    ·
                      refine ⟨596121257992102042785931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794828343989469390381241 596121257992102042785931)
                      ·
                        rfl

theorem cell23_1160942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_1160942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160942 prefixEnd_1160942 := by exact prefixLift 1160942
  have htrace : WordTrace (prefixWord ++ tailWord_1160942) baseStart_1160942 baseEnd_1160942 := by
    simpa [prefixWord, tailWord_1160942, baseEnd_1160942] using wordTrace_append hprefix tailTrace_1160942
  have hstable : (prefixWord ++ tailWord_1160942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160942).length < 2 ^ (prefixWord ++ tailWord_1160942).sum := by decide
  have hdescent : baseEnd_1160942 < baseStart_1160942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160962 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1160962 : Nat := 118140960795 + 1160962 * 2 ^ 59
def prefixEnd_1160962 : Nat := 4983230072969 + 3 ^ 40 * 1160962 * 2
def baseEnd_1160962 : Nat := 596131527605191964535839

theorem tailTrace_1160962 : CollatzResearch.WordTrace tailWord_1160962 prefixEnd_1160962 596131527605191964535839 := by
  unfold tailWord_1160962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585940705010106342277285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28229175213360283579406093 10585940705010106342277285)
  ·
    refine ⟨1984863882189394939176991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10585940705010106342277285 1984863882189394939176991)
    ·
      refine ⟨2977295823284092408765487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984863882189394939176991 2977295823284092408765487)
      ·
        refine ⟨4465943734926138613148231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977295823284092408765487 4465943734926138613148231)
        ·
          refine ⟨6698915602389207919722347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465943734926138613148231 6698915602389207919722347)
          ·
            refine ⟨10048373403583811879583521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698915602389207919722347 10048373403583811879583521)
            ·
              refine ⟨7536280052687858909687641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10048373403583811879583521 7536280052687858909687641)
              ·
                refine ⟨5652210039515894182265731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7536280052687858909687641 5652210039515894182265731)
                ·
                  refine ⟨8478315059273841273398597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5652210039515894182265731 8478315059273841273398597)
                  ·
                    refine ⟨1589684073613845238762237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8478315059273841273398597 1589684073613845238762237)
                    ·
                      refine ⟨596131527605191964535839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589684073613845238762237 596131527605191964535839)
                      ·
                        rfl

theorem cell23_1160962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1160962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160962 prefixEnd_1160962 := by exact prefixLift 1160962
  have htrace : WordTrace (prefixWord ++ tailWord_1160962) baseStart_1160962 baseEnd_1160962 := by
    simpa [prefixWord, tailWord_1160962, baseEnd_1160962] using wordTrace_append hprefix tailTrace_1160962
  have hstable : (prefixWord ++ tailWord_1160962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160962).length < 2 ^ (prefixWord ++ tailWord_1160962).sum := by decide
  have hdescent : baseEnd_1160962 < baseStart_1160962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160992 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1160992 : Nat := 118140960795 + 1160992 * 2 ^ 59
def prefixEnd_1160992 : Nat := 4983230072969 + 3 ^ 40 * 1160992 * 2
def baseEnd_1160992 : Nat := 596146932024826847160701

theorem tailTrace_1160992 : CollatzResearch.WordTrace tailWord_1160992 prefixEnd_1160992 596146932024826847160701 := by
  unfold tailWord_1160992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172428504965870246350615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28229904673287826995134153 21172428504965870246350615)
  ·
    refine ⟨31758642757448805369525923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172428504965870246350615 31758642757448805369525923)
    ·
      refine ⟨47637964136173208054288885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31758642757448805369525923 47637964136173208054288885)
      ·
        refine ⟨4466059137766238255089583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47637964136173208054288885 4466059137766238255089583)
        ·
          refine ⟨6699088706649357382634375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466059137766238255089583 6699088706649357382634375)
          ·
            refine ⟨10048633059974036073951563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6699088706649357382634375 10048633059974036073951563)
            ·
              refine ⟨15072949589961054110927345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10048633059974036073951563 15072949589961054110927345)
              ·
                refine ⟨11304712192470790583195509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15072949589961054110927345 11304712192470790583195509)
                ·
                  refine ⟨1059816768044136617174579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11304712192470790583195509 1059816768044136617174579)
                  ·
                    refine ⟨1589725152066204925761869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1059816768044136617174579 1589725152066204925761869)
                    ·
                      refine ⟨596146932024826847160701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589725152066204925761869 596146932024826847160701)
                      ·
                        rfl

theorem cell23_1160992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1160992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160992 prefixEnd_1160992 := by exact prefixLift 1160992
  have htrace : WordTrace (prefixWord ++ tailWord_1160992) baseStart_1160992 baseEnd_1160992 := by
    simpa [prefixWord, tailWord_1160992, baseEnd_1160992] using wordTrace_append hprefix tailTrace_1160992
  have hstable : (prefixWord ++ tailWord_1160992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160992).length < 2 ^ (prefixWord ++ tailWord_1160992).sum := by decide
  have hdescent : baseEnd_1160992 < baseStart_1160992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161008 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_1161008 : Nat := 118140960795 + 1161008 * 2 ^ 59
def prefixEnd_1161008 : Nat := 4983230072969 + 3 ^ 40 * 1161008 * 2
def baseEnd_1161008 : Nat := 198718382571766261520209

theorem tailTrace_1161008 : CollatzResearch.WordTrace tailWord_1161008 prefixEnd_1161008 198718382571766261520209 := by
  unfold tailWord_1161008
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172720288936887612641839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28230293718582516816855785 21172720288936887612641839)
  ·
    refine ⟨31759080433405331418962759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172720288936887612641839 31759080433405331418962759)
    ·
      refine ⟨47638620650107997128444139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31759080433405331418962759 47638620650107997128444139)
      ·
        refine ⟨71457930975161995692666209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47638620650107997128444139 71457930975161995692666209)
        ·
          refine ⟨53593448231371496769499657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71457930975161995692666209 53593448231371496769499657)
          ·
            refine ⟨40195086173528622577124743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53593448231371496769499657 40195086173528622577124743)
            ·
              refine ⟨60292629260292933865687115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40195086173528622577124743 60292629260292933865687115)
              ·
                refine ⟨90438943890439400798530673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60292629260292933865687115 90438943890439400798530673)
                ·
                  refine ⟨67829207917829550598898005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90438943890439400798530673 67829207917829550598898005)
                  ·
                    refine ⟨198718382571766261520209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 67829207917829550598898005 198718382571766261520209)
                    ·
                      rfl

theorem cell23_1161008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_1161008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161008 prefixEnd_1161008 := by exact prefixLift 1161008
  have htrace : WordTrace (prefixWord ++ tailWord_1161008) baseStart_1161008 baseEnd_1161008 := by
    simpa [prefixWord, tailWord_1161008, baseEnd_1161008] using wordTrace_append hprefix tailTrace_1161008
  have hstable : (prefixWord ++ tailWord_1161008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161008).length < 2 ^ (prefixWord ++ tailWord_1161008).sum := by decide
  have hdescent : baseEnd_1161008 < baseStart_1161008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161009 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1161009 : Nat := 118140960795 + 1161009 * 2 ^ 59
def prefixEnd_1161009 : Nat := 4983230072969 + 3 ^ 40 * 1161009 * 2
def baseEnd_1161009 : Nat := 596155661195953280648123

theorem tailTrace_1161009 : CollatzResearch.WordTrace tailWord_1161009 prefixEnd_1161009 596155661195953280648123 := by
  unfold tailWord_1161009
  simp only [CollatzResearch.WordTrace]
  refine ⟨42345477050870152396070081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28230318033913434930713387 42345477050870152396070081)
  ·
    refine ⟨31759107788152614297052561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42345477050870152396070081 31759107788152614297052561)
    ·
      refine ⟨23819330841114460722789421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31759107788152614297052561 23819330841114460722789421)
      ·
        refine ⟨8932249065417922771046033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23819330841114460722789421 8932249065417922771046033)
        ·
          refine ⟨6699186799063442078284525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8932249065417922771046033 6699186799063442078284525)
          ·
            refine ⟨2512195049648790779356697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6699186799063442078284525 2512195049648790779356697)
            ·
              refine ⟨1884146287236593084517523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512195049648790779356697 1884146287236593084517523)
              ·
                refine ⟨2826219430854889626776285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884146287236593084517523 2826219430854889626776285)
                ·
                  refine ⟨1059832286570583610041107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2826219430854889626776285 1059832286570583610041107)
                  ·
                    refine ⟨1589748429855875415061661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1059832286570583610041107 1589748429855875415061661)
                    ·
                      refine ⟨596155661195953280648123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589748429855875415061661 596155661195953280648123)
                      ·
                        rfl

theorem cell23_1161009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1161009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161009 prefixEnd_1161009 := by exact prefixLift 1161009
  have htrace : WordTrace (prefixWord ++ tailWord_1161009) baseStart_1161009 baseEnd_1161009 := by
    simpa [prefixWord, tailWord_1161009, baseEnd_1161009] using wordTrace_append hprefix tailTrace_1161009
  have hstable : (prefixWord ++ tailWord_1161009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161009).length < 2 ^ (prefixWord ++ tailWord_1161009).sum := by decide
  have hdescent : baseEnd_1161009 < baseStart_1161009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161015 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1161015 : Nat := 118140960795 + 1161015 * 2 ^ 59
def prefixEnd_1161015 : Nat := 4983230072969 + 3 ^ 40 * 1161015 * 2
def baseEnd_1161015 : Nat := 596158742079880257173095

theorem tailTrace_1161015 : CollatzResearch.WordTrace tailWord_1161015 prefixEnd_1161015 596158742079880257173095 := by
  unfold tailWord_1161015
  simp only [CollatzResearch.WordTrace]
  refine ⟨42345695888848415420788499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28230463925898943613858999 42345695888848415420788499)
  ·
    refine ⟨63518543833272623131182749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42345695888848415420788499 63518543833272623131182749)
    ·
      refine ⟨23819453937477233674193531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63518543833272623131182749 23819453937477233674193531)
      ·
        refine ⟨35729180906215850511290297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23819453937477233674193531 35729180906215850511290297)
        ·
          refine ⟨26796885679661887883467723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35729180906215850511290297 26796885679661887883467723)
          ·
            refine ⟨40195328519492831825201585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26796885679661887883467723 40195328519492831825201585)
            ·
              refine ⟨30146496389619623868901189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40195328519492831825201585 30146496389619623868901189)
              ·
                refine ⟨5652468073053679475418973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30146496389619623868901189 5652468073053679475418973)
                ·
                  refine ⟨2119675527395129803282115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5652468073053679475418973 2119675527395129803282115)
                  ·
                    refine ⟨3179513291092694704923173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119675527395129803282115 3179513291092694704923173)
                    ·
                      refine ⟨596158742079880257173095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3179513291092694704923173 596158742079880257173095)
                      ·
                        rfl

theorem cell23_1161015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1161015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161015 prefixEnd_1161015 := by exact prefixLift 1161015
  have htrace : WordTrace (prefixWord ++ tailWord_1161015) baseStart_1161015 baseEnd_1161015 := by
    simpa [prefixWord, tailWord_1161015, baseEnd_1161015] using wordTrace_append hprefix tailTrace_1161015
  have hstable : (prefixWord ++ tailWord_1161015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161015).length < 2 ^ (prefixWord ++ tailWord_1161015).sum := by decide
  have hdescent : baseEnd_1161015 < baseStart_1161015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161032 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_1161032 : Nat := 118140960795 + 1161032 * 2 ^ 59
def prefixEnd_1161032 : Nat := 4983230072969 + 3 ^ 40 * 1161032 * 2
def baseEnd_1161032 : Nat := 596167471251006690660517

theorem tailTrace_1161032 : CollatzResearch.WordTrace tailWord_1161032 prefixEnd_1161032 596167471251006690660517 := by
  unfold tailWord_1161032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21173157964893413662078675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28230877286524551549438233 21173157964893413662078675)
  ·
    refine ⟨31759736947340120493118013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21173157964893413662078675 31759736947340120493118013)
    ·
      refine ⟨11909901355252545184919255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31759736947340120493118013 11909901355252545184919255)
      ·
        refine ⟨17864852032878817777378883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11909901355252545184919255 17864852032878817777378883)
        ·
          refine ⟨26797278049318226666068325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17864852032878817777378883 26797278049318226666068325)
          ·
            refine ⟨5024489634247167499887811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26797278049318226666068325 5024489634247167499887811)
            ·
              refine ⟨7536734451370751249831717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024489634247167499887811 7536734451370751249831717)
              ·
                refine ⟨1413137709632015859343447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7536734451370751249831717 1413137709632015859343447)
                ·
                  refine ⟨2119706564448023789015171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413137709632015859343447 2119706564448023789015171)
                  ·
                    refine ⟨3179559846672035683522757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119706564448023789015171 3179559846672035683522757)
                    ·
                      refine ⟨596167471251006690660517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3179559846672035683522757 596167471251006690660517)
                      ·
                        rfl

theorem cell23_1161032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_1161032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161032 prefixEnd_1161032 := by exact prefixLift 1161032
  have htrace : WordTrace (prefixWord ++ tailWord_1161032) baseStart_1161032 baseEnd_1161032 := by
    simpa [prefixWord, tailWord_1161032, baseEnd_1161032] using wordTrace_append hprefix tailTrace_1161032
  have hstable : (prefixWord ++ tailWord_1161032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161032).length < 2 ^ (prefixWord ++ tailWord_1161032).sum := by decide
  have hdescent : baseEnd_1161032 < baseStart_1161032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161042 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1161042 : Nat := 118140960795 + 1161042 * 2 ^ 59
def prefixEnd_1161042 : Nat := 4983230072969 + 3 ^ 40 * 1161042 * 2
def baseEnd_1161042 : Nat := 198724202019183883845157

theorem tailTrace_1161042 : CollatzResearch.WordTrace tailWord_1161042 prefixEnd_1161042 198724202019183883845157 := by
  unfold tailWord_1161042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586670164937649758005345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28231120439833732688014253 10586670164937649758005345)
  ·
    refine ⟨7940002623703237318504009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10586670164937649758005345 7940002623703237318504009)
    ·
      refine ⟨5955001967777427988878007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7940002623703237318504009 5955001967777427988878007)
      ·
        refine ⟨8932502951666141983317011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5955001967777427988878007 8932502951666141983317011)
        ·
          refine ⟨13398754427499212974975517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8932502951666141983317011 13398754427499212974975517)
          ·
            refine ⟨5024532910312204865615819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13398754427499212974975517 5024532910312204865615819)
            ·
              refine ⟨7536799365468307298423729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024532910312204865615819 7536799365468307298423729)
              ·
                refine ⟨5652599524101230473817797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7536799365468307298423729 5652599524101230473817797)
                ·
                  refine ⟨1059862410768980713840837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5652599524101230473817797 1059862410768980713840837)
                  ·
                    refine ⟨198724202019183883845157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059862410768980713840837 198724202019183883845157)
                    ·
                      rfl

theorem cell23_1161042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1161042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161042 prefixEnd_1161042 := by exact prefixLift 1161042
  have htrace : WordTrace (prefixWord ++ tailWord_1161042) baseStart_1161042 baseEnd_1161042 := by
    simpa [prefixWord, tailWord_1161042, baseEnd_1161042] using wordTrace_append hprefix tailTrace_1161042
  have hstable : (prefixWord ++ tailWord_1161042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161042).length < 2 ^ (prefixWord ++ tailWord_1161042).sum := by decide
  have hdescent : baseEnd_1161042 < baseStart_1161042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161055 : List Nat := [1, 1, 2, 3, 1, 6, 9]
def baseStart_1161055 : Nat := 118140960795 + 1161055 * 2 ^ 59
def prefixEnd_1161055 : Nat := 4983230072969 + 3 ^ 40 * 1161055 * 2
def baseEnd_1161055 : Nat := 7360238040815556798431

theorem tailTrace_1161055 : CollatzResearch.WordTrace tailWord_1161055 prefixEnd_1161055 7360238040815556798431 := by
  unfold tailWord_1161055
  simp only [CollatzResearch.WordTrace]
  refine ⟨42347154808703502252244619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28231436539135668168163079 42347154808703502252244619)
  ·
    refine ⟨63520732213055253378366929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42347154808703502252244619 63520732213055253378366929)
    ·
      refine ⟨47640549159791440033775197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63520732213055253378366929 47640549159791440033775197)
      ·
        refine ⟨17865205934921790012665699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47640549159791440033775197 17865205934921790012665699)
        ·
          refine ⟨26797808902382685018998549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17865205934921790012665699 26797808902382685018998549)
          ·
            refine ⟨1256147292299188360265557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26797808902382685018998549 1256147292299188360265557)
            ·
              refine ⟨7360238040815556798431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1256147292299188360265557 7360238040815556798431)
              ·
                rfl

theorem cell23_1161055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 9].length) (baseStart_1161055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161055 prefixEnd_1161055 := by exact prefixLift 1161055
  have htrace : WordTrace (prefixWord ++ tailWord_1161055) baseStart_1161055 baseEnd_1161055 := by
    simpa [prefixWord, tailWord_1161055, baseEnd_1161055] using wordTrace_append hprefix tailTrace_1161055
  have hstable : (prefixWord ++ tailWord_1161055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161055).length < 2 ^ (prefixWord ++ tailWord_1161055).sum := by decide
  have hdescent : baseEnd_1161055 < baseStart_1161055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161086 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1161086 : Nat := 118140960795 + 1161086 * 2 ^ 59
def prefixEnd_1161086 : Nat := 4983230072969 + 3 ^ 40 * 1161086 * 2
def baseEnd_1161086 : Nat := 596195199206349479385269

theorem tailTrace_1161086 : CollatzResearch.WordTrace tailWord_1161086 prefixEnd_1161086 596195199206349479385269 := by
  unfold tailWord_1161086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293535683948899318327889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28232190314394129697748741 5293535683948899318327889)
  ·
    refine ⟨3970151762961674488745917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5293535683948899318327889 3970151762961674488745917)
    ·
      refine ⟨1488806911110627933279719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3970151762961674488745917 1488806911110627933279719)
      ·
        refine ⟨2233210366665941899919579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488806911110627933279719 2233210366665941899919579)
        ·
          refine ⟨3349815549998912849879369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233210366665941899919579 3349815549998912849879369)
          ·
            refine ⟨2512361662499184637409527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349815549998912849879369 2512361662499184637409527)
            ·
              refine ⟨3768542493748776956114291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512361662499184637409527 3768542493748776956114291)
              ·
                refine ⟨5652813740623165434171437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768542493748776956114291 5652813740623165434171437)
                ·
                  refine ⟨2119805152733687037814289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5652813740623165434171437 2119805152733687037814289)
                  ·
                    refine ⟨1589853864550265278360717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2119805152733687037814289 1589853864550265278360717)
                    ·
                      refine ⟨596195199206349479385269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589853864550265278360717 596195199206349479385269)
                      ·
                        rfl

theorem cell23_1161086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1161086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161086 prefixEnd_1161086 := by exact prefixLift 1161086
  have htrace : WordTrace (prefixWord ++ tailWord_1161086) baseStart_1161086 baseEnd_1161086 := by
    simpa [prefixWord, tailWord_1161086, baseEnd_1161086] using wordTrace_append hprefix tailTrace_1161086
  have hstable : (prefixWord ++ tailWord_1161086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161086).length < 2 ^ (prefixWord ++ tailWord_1161086).sum := by decide
  have hdescent : baseEnd_1161086 < baseStart_1161086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161110 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1161110 : Nat := 118140960795 + 1161110 * 2 ^ 59
def prefixEnd_1161110 : Nat := 4983230072969 + 3 ^ 40 * 1161110 * 2
def baseEnd_1161110 : Nat := 198735840914019128495053

theorem tailTrace_1161110 : CollatzResearch.WordTrace tailWord_1161110 prefixEnd_1161110 198735840914019128495053 := by
  unfold tailWord_1161110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646822551469015415343549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28232773882336164430331189 2646822551469015415343549)
  ·
    refine ⟨992558456800880780753831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2646822551469015415343549 992558456800880780753831)
    ·
      refine ⟨1488837685201321171130747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992558456800880780753831 1488837685201321171130747)
      ·
        refine ⟨2233256527801981756696121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488837685201321171130747 2233256527801981756696121)
        ·
          refine ⟨1674942395851486317522091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233256527801981756696121 1674942395851486317522091)
          ·
            refine ⟨2512413593777229476283137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674942395851486317522091 2512413593777229476283137)
            ·
              refine ⟨1884310195332922107212353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512413593777229476283137 1884310195332922107212353)
              ·
                refine ⟨1413232646499691580409265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884310195332922107212353 1413232646499691580409265)
                ·
                  refine ⟨1059924484874768685306949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413232646499691580409265 1059924484874768685306949)
                  ·
                    refine ⟨198735840914019128495053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059924484874768685306949 198735840914019128495053)
                    ·
                      rfl

theorem cell23_1161110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1161110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161110 prefixEnd_1161110 := by exact prefixLift 1161110
  have htrace : WordTrace (prefixWord ++ tailWord_1161110) baseStart_1161110 baseEnd_1161110 := by
    simpa [prefixWord, tailWord_1161110, baseEnd_1161110] using wordTrace_append hprefix tailTrace_1161110
  have hstable : (prefixWord ++ tailWord_1161110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161110).length < 2 ^ (prefixWord ++ tailWord_1161110).sum := by decide
  have hdescent : baseEnd_1161110 < baseStart_1161110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161116 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1161116 : Nat := 118140960795 + 1161116 * 2 ^ 59
def prefixEnd_1161116 : Nat := 4983230072969 + 3 ^ 40 * 1161116 * 2
def baseEnd_1161116 : Nat := 596210603625984362010131

theorem tailTrace_1161116 : CollatzResearch.WordTrace tailWord_1161116 prefixEnd_1161116 596210603625984362010131 := by
  unfold tailWord_1161116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21174689830741254835107601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28232919774321673113476801 21174689830741254835107601)
  ·
    refine ⟨15881017373055941126330701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21174689830741254835107601 15881017373055941126330701)
    ·
      refine ⟨5955381514895977922374013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15881017373055941126330701 5955381514895977922374013)
      ·
        refine ⟨2233268068085991720890255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5955381514895977922374013 2233268068085991720890255)
        ·
          refine ⟨3349902102128987581335383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233268068085991720890255 3349902102128987581335383)
          ·
            refine ⟨5024853153193481372003075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349902102128987581335383 5024853153193481372003075)
            ·
              refine ⟨7537279729790222058004613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024853153193481372003075 7537279729790222058004613)
              ·
                refine ⟨1413239949335666635875865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7537279729790222058004613 1413239949335666635875865)
                ·
                  refine ⟨1059929962001749976906899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413239949335666635875865 1059929962001749976906899)
                  ·
                    refine ⟨1589894943002624965360349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1059929962001749976906899 1589894943002624965360349)
                    ·
                      refine ⟨596210603625984362010131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589894943002624965360349 596210603625984362010131)
                      ·
                        rfl

theorem cell23_1161116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1161116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161116 prefixEnd_1161116 := by exact prefixLift 1161116
  have htrace : WordTrace (prefixWord ++ tailWord_1161116) baseStart_1161116 baseEnd_1161116 := by
    simpa [prefixWord, tailWord_1161116, baseEnd_1161116] using wordTrace_append hprefix tailTrace_1161116
  have hstable : (prefixWord ++ tailWord_1161116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161116).length < 2 ^ (prefixWord ++ tailWord_1161116).sum := by decide
  have hdescent : baseEnd_1161116 < baseStart_1161116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161125 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_1161125 : Nat := 118140960795 + 1161125 * 2 ^ 59
def prefixEnd_1161125 : Nat := 4983230072969 + 3 ^ 40 * 1161125 * 2
def baseEnd_1161125 : Nat := 596215224951874826797589

theorem tailTrace_1161125 : CollatzResearch.WordTrace tailWord_1161125 prefixEnd_1161125 596215224951874826797589 := by
  unfold tailWord_1161125
  simp only [CollatzResearch.WordTrace]
  refine ⟨42349707918449904207292829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28233138612299936138195219 42349707918449904207292829)
  ·
    refine ⟨15881140469418714077734811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42349707918449904207292829 15881140469418714077734811)
    ·
      refine ⟨23821710704128071116602217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15881140469418714077734811 23821710704128071116602217)
      ·
        refine ⟨17866283028096053337451663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23821710704128071116602217 17866283028096053337451663)
        ·
          refine ⟨26799424542144080006177495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17866283028096053337451663 26799424542144080006177495)
          ·
            refine ⟨40199136813216120009266243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26799424542144080006177495 40199136813216120009266243)
            ·
              refine ⟨60298705219824180013899365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40199136813216120009266243 60298705219824180013899365)
              ·
                refine ⟨11306007228717033752606131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60298705219824180013899365 11306007228717033752606131)
                ·
                  refine ⟨16959010843075550628909197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11306007228717033752606131 16959010843075550628909197)
                  ·
                    refine ⟨6359629066153331485840949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16959010843075550628909197 6359629066153331485840949)
                    ·
                      refine ⟨596215224951874826797589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6359629066153331485840949 596215224951874826797589)
                      ·
                        rfl

theorem cell23_1161125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_1161125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161125 prefixEnd_1161125 := by exact prefixLift 1161125
  have htrace : WordTrace (prefixWord ++ tailWord_1161125) baseStart_1161125 baseEnd_1161125 := by
    simpa [prefixWord, tailWord_1161125, baseEnd_1161125] using wordTrace_append hprefix tailTrace_1161125
  have hstable : (prefixWord ++ tailWord_1161125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161125).length < 2 ^ (prefixWord ++ tailWord_1161125).sum := by decide
  have hdescent : baseEnd_1161125 < baseStart_1161125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161139 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 1, 4, 2]
def baseStart_1161139 : Nat := 118140960795 + 1161139 * 2 ^ 59
def prefixEnd_1161139 : Nat := 4983230072969 + 3 ^ 40 * 1161139 * 2
def baseEnd_1161139 : Nat := 596222413681037772022525

theorem tailTrace_1161139 : CollatzResearch.WordTrace tailWord_1161139 prefixEnd_1161139 596222413681037772022525 := by
  unfold tailWord_1161139
  simp only [CollatzResearch.WordTrace]
  refine ⟨42350218540399184598302471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28233479026932789732201647 42350218540399184598302471)
  ·
    refine ⟨63525327810598776897453707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42350218540399184598302471 63525327810598776897453707)
    ·
      refine ⟨95287991715898165346180561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63525327810598776897453707 95287991715898165346180561)
      ·
        refine ⟨71465993786923624009635421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95287991715898165346180561 71465993786923624009635421)
        ·
          refine ⟨26799747670096359003613283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71465993786923624009635421 26799747670096359003613283)
          ·
            refine ⟨40199621505144538505419925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26799747670096359003613283 40199621505144538505419925)
            ·
              refine ⟨1884357258053650242441559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40199621505144538505419925 1884357258053650242441559)
              ·
                refine ⟨2826535887080475363662339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884357258053650242441559 2826535887080475363662339)
                ·
                  refine ⟨4239803830620713045493509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826535887080475363662339 4239803830620713045493509)
                  ·
                    refine ⟨794963218241383696030033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239803830620713045493509 794963218241383696030033)
                    ·
                      refine ⟨596222413681037772022525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794963218241383696030033 596222413681037772022525)
                      ·
                        rfl

theorem cell23_1161139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 4, 2].length) (baseStart_1161139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161139 prefixEnd_1161139 := by exact prefixLift 1161139
  have htrace : WordTrace (prefixWord ++ tailWord_1161139) baseStart_1161139 baseEnd_1161139 := by
    simpa [prefixWord, tailWord_1161139, baseEnd_1161139] using wordTrace_append hprefix tailTrace_1161139
  have hstable : (prefixWord ++ tailWord_1161139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161139).length < 2 ^ (prefixWord ++ tailWord_1161139).sum := by decide
  have hdescent : baseEnd_1161139 < baseStart_1161139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161173 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1161173 : Nat := 118140960795 + 1161173 * 2 ^ 59
def prefixEnd_1161173 : Nat := 4983230072969 + 3 ^ 40 * 1161173 * 2
def baseEnd_1161173 : Nat := 596239872023290638997369

theorem tailTrace_1161173 : CollatzResearch.WordTrace tailWord_1161173 prefixEnd_1161173 596239872023290638997369 := by
  unfold tailWord_1161173
  simp only [CollatzResearch.WordTrace]
  refine ⟨42351458622276008405040173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28234305748184005603360115 42351458622276008405040173)
  ·
    refine ⟨15881796983353503151890065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42351458622276008405040173 15881796983353503151890065)
    ·
      refine ⟨11911347737515127363917549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15881796983353503151890065 11911347737515127363917549)
      ·
        refine ⟨4466755401568172761469081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11911347737515127363917549 4466755401568172761469081)
        ·
          refine ⟨3350066551176129571101811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4466755401568172761469081 3350066551176129571101811)
          ·
            refine ⟨5025099826764194356652717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350066551176129571101811 5025099826764194356652717)
            ·
              refine ⟨1884412435036572883744769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5025099826764194356652717 1884412435036572883744769)
              ·
                refine ⟨1413309326277429662808577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884412435036572883744769 1413309326277429662808577)
                ·
                  refine ⟨1059981994708072247106433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413309326277429662808577 1059981994708072247106433)
                  ·
                    refine ⟨794986496031054185329825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1059981994708072247106433 794986496031054185329825)
                    ·
                      refine ⟨596239872023290638997369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794986496031054185329825 596239872023290638997369)
                      ·
                        rfl

theorem cell23_1161173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1161173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161173 prefixEnd_1161173 := by exact prefixLift 1161173
  have htrace : WordTrace (prefixWord ++ tailWord_1161173) baseStart_1161173 baseEnd_1161173 := by
    simpa [prefixWord, tailWord_1161173, baseEnd_1161173] using wordTrace_append hprefix tailTrace_1161173
  have hstable : (prefixWord ++ tailWord_1161173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161173).length < 2 ^ (prefixWord ++ tailWord_1161173).sum := by decide
  have hdescent : baseEnd_1161173 < baseStart_1161173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161212 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_1161212 : Nat := 118140960795 + 1161212 * 2 ^ 59
def prefixEnd_1161212 : Nat := 4983230072969 + 3 ^ 40 * 1161212 * 2
def baseEnd_1161212 : Nat := 596259897768815986409689

theorem tailTrace_1161212 : CollatzResearch.WordTrace tailWord_1161212 prefixEnd_1161212 596259897768815986409689 := by
  unfold tailWord_1161212
  simp only [CollatzResearch.WordTrace]
  refine ⟨21176440534567359032854945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28235254046089812043806593 21176440534567359032854945)
  ·
    refine ⟨15882330400925519274641209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21176440534567359032854945 15882330400925519274641209)
    ·
      refine ⟨11911747800694139455980907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15882330400925519274641209 11911747800694139455980907)
      ·
        refine ⟨17867621701041209183971361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11911747800694139455980907 17867621701041209183971361)
        ·
          refine ⟨13400716275780906887978521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17867621701041209183971361 13400716275780906887978521)
          ·
            refine ⟨10050537206835680165983891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13400716275780906887978521 10050537206835680165983891)
            ·
              refine ⟨15075805810253520248975837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10050537206835680165983891 15075805810253520248975837)
              ·
                refine ⟨5653427178845070093365939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15075805810253520248975837 5653427178845070093365939)
                ·
                  refine ⟨8480140768267605140048909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5653427178845070093365939 8480140768267605140048909)
                  ·
                    refine ⟨3180052788100351927518341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8480140768267605140048909 3180052788100351927518341)
                    ·
                      refine ⟨596259897768815986409689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3180052788100351927518341 596259897768815986409689)
                      ·
                        rfl

theorem cell23_1161212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_1161212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161212 prefixEnd_1161212 := by exact prefixLift 1161212
  have htrace : WordTrace (prefixWord ++ tailWord_1161212) baseStart_1161212 baseEnd_1161212 := by
    simpa [prefixWord, tailWord_1161212, baseEnd_1161212] using wordTrace_append hprefix tailTrace_1161212
  have hstable : (prefixWord ++ tailWord_1161212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161212).length < 2 ^ (prefixWord ++ tailWord_1161212).sum := by decide
  have hdescent : baseEnd_1161212 < baseStart_1161212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161266 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1161266 : Nat := 118140960795 + 1161266 * 2 ^ 59
def prefixEnd_1161266 : Nat := 4983230072969 + 3 ^ 40 * 1161266 * 2
def baseEnd_1161266 : Nat := 596287625724158775134441

theorem tailTrace_1161266 : CollatzResearch.WordTrace tailWord_1161266 prefixEnd_1161266 596287625724158775134441 := by
  unfold tailWord_1161266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10588712652734771322043913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28236567073959390192117101 10588712652734771322043913)
  ·
    refine ⟨7941534489551078491532935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10588712652734771322043913 7941534489551078491532935)
    ·
      refine ⟨11912301734326617737299403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7941534489551078491532935 11912301734326617737299403)
      ·
        refine ⟨17868452601489926605949105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11912301734326617737299403 17868452601489926605949105)
        ·
          refine ⟨13401339451117444954461829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17868452601489926605949105 13401339451117444954461829)
          ·
            refine ⟨2512751147084520928961593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13401339451117444954461829 2512751147084520928961593)
            ·
              refine ⟨1884563360313390696721195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512751147084520928961593 1884563360313390696721195)
              ·
                refine ⟨2826845040470086045081793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884563360313390696721195 2826845040470086045081793)
                ·
                  refine ⟨2120133780352564533811345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826845040470086045081793 2120133780352564533811345)
                  ·
                    refine ⟨1590100335264423400358509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120133780352564533811345 1590100335264423400358509)
                    ·
                      refine ⟨596287625724158775134441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590100335264423400358509 596287625724158775134441)
                      ·
                        rfl

theorem cell23_1161266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1161266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161266 prefixEnd_1161266 := by exact prefixLift 1161266
  have htrace : WordTrace (prefixWord ++ tailWord_1161266) baseStart_1161266 baseEnd_1161266 := by
    simpa [prefixWord, tailWord_1161266, baseEnd_1161266] using wordTrace_append hprefix tailTrace_1161266
  have hstable : (prefixWord ++ tailWord_1161266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161266).length < 2 ^ (prefixWord ++ tailWord_1161266).sum := by decide
  have hdescent : baseEnd_1161266 < baseStart_1161266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161319 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1161319 : Nat := 118140960795 + 1161319 * 2 ^ 59
def prefixEnd_1161319 : Nat := 4983230072969 + 3 ^ 40 * 1161319 * 2
def baseEnd_1161319 : Nat := 596314840198847067771697

theorem tailTrace_1161319 : CollatzResearch.WordTrace tailWord_1161319 prefixEnd_1161319 596314840198847067771697 := by
  unfold tailWord_1161319
  simp only [CollatzResearch.WordTrace]
  refine ⟨42356783679747075339855011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28237855786498050226570007 42356783679747075339855011)
  ·
    refine ⟨63535175519620613009782517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42356783679747075339855011 63535175519620613009782517)
    ·
      refine ⟨5956422704964432469667111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63535175519620613009782517 5956422704964432469667111)
      ·
        refine ⟨8934634057446648704500667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956422704964432469667111 8934634057446648704500667)
        ·
          refine ⟨13401951086169973056751001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8934634057446648704500667 13401951086169973056751001)
          ·
            refine ⟨10051463314627479792563251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13401951086169973056751001 10051463314627479792563251)
            ·
              refine ⟨15077194971941219688844877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10051463314627479792563251 15077194971941219688844877)
              ·
                refine ⟨5653948114477957383316829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15077194971941219688844877 5653948114477957383316829)
                ·
                  refine ⟨2120230542929234018743811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5653948114477957383316829 2120230542929234018743811)
                  ·
                    refine ⟨3180345814393851028115717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120230542929234018743811 3180345814393851028115717)
                    ·
                      refine ⟨596314840198847067771697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3180345814393851028115717 596314840198847067771697)
                      ·
                        rfl

theorem cell23_1161319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1161319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161319 prefixEnd_1161319 := by exact prefixLift 1161319
  have htrace : WordTrace (prefixWord ++ tailWord_1161319) baseStart_1161319 baseEnd_1161319 := by
    simpa [prefixWord, tailWord_1161319, baseEnd_1161319] using wordTrace_append hprefix tailTrace_1161319
  have hstable : (prefixWord ++ tailWord_1161319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161319).length < 2 ^ (prefixWord ++ tailWord_1161319).sum := by decide
  have hdescent : baseEnd_1161319 < baseStart_1161319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161329 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_1161329 : Nat := 118140960795 + 1161329 * 2 ^ 59
def prefixEnd_1161329 : Nat := 4983230072969 + 3 ^ 40 * 1161329 * 2
def baseEnd_1161329 : Nat := 198773325001797342882217

theorem tailTrace_1161329 : CollatzResearch.WordTrace tailWord_1161329 prefixEnd_1161329 198773325001797342882217 := by
  unfold tailWord_1161329
  simp only [CollatzResearch.WordTrace]
  refine ⟨42357148409710847047719041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28238098939807231365146027 42357148409710847047719041)
  ·
    refine ⟨31767861307283135285789281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42357148409710847047719041 31767861307283135285789281)
    ·
      refine ⟨23825895980462351464341961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31767861307283135285789281 23825895980462351464341961)
      ·
        refine ⟨17869421985346763598256471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23825895980462351464341961 17869421985346763598256471)
        ·
          refine ⟨26804132978020145397384707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17869421985346763598256471 26804132978020145397384707)
          ·
            refine ⟨40206199467030218096077061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26804132978020145397384707 40206199467030218096077061)
            ·
              refine ⟨7538662400068165893014449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40206199467030218096077061 7538662400068165893014449)
              ·
                refine ⟨5653996800051124419760837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7538662400068165893014449 5653996800051124419760837)
                ·
                  refine ⟨1060124400009585828705157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5653996800051124419760837 1060124400009585828705157)
                  ·
                    refine ⟨198773325001797342882217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1060124400009585828705157 198773325001797342882217)
                    ·
                      rfl

theorem cell23_1161329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_1161329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161329 prefixEnd_1161329 := by exact prefixLift 1161329
  have htrace : WordTrace (prefixWord ++ tailWord_1161329) baseStart_1161329 baseEnd_1161329 := by
    simpa [prefixWord, tailWord_1161329, baseEnd_1161329] using wordTrace_append hprefix tailTrace_1161329
  have hstable : (prefixWord ++ tailWord_1161329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161329).length < 2 ^ (prefixWord ++ tailWord_1161329).sum := by decide
  have hdescent : baseEnd_1161329 < baseStart_1161329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161330 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1161330 : Nat := 118140960795 + 1161330 * 2 ^ 59
def prefixEnd_1161330 : Nat := 4983230072969 + 3 ^ 40 * 1161330 * 2
def baseEnd_1161330 : Nat := 596320488486046524734147

theorem tailTrace_1161330 : CollatzResearch.WordTrace tailWord_1161330 prefixEnd_1161330 596320488486046524734147 := by
  unfold tailWord_1161330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589296220676806054626361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28238123255138149479003629 10589296220676806054626361)
  ·
    refine ⟨7941972165507604540969771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10589296220676806054626361 7941972165507604540969771)
    ·
      refine ⟨11912958248261406811454657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7941972165507604540969771 11912958248261406811454657)
      ·
        refine ⟨8934718686196055108590993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11912958248261406811454657 8934718686196055108590993)
        ·
          refine ⟨6701039014647041331443245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8934718686196055108590993 6701039014647041331443245)
          ·
            refine ⟨2512889630492640499291217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6701039014647041331443245 2512889630492640499291217)
            ·
              refine ⟨1884667222869480374468413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512889630492640499291217 1884667222869480374468413)
              ·
                refine ⟨706750208576055140425655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1884667222869480374468413 706750208576055140425655)
                ·
                  refine ⟨1060125312864082710638483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706750208576055140425655 1060125312864082710638483)
                  ·
                    refine ⟨1590187969296124065957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1060125312864082710638483 1590187969296124065957725)
                    ·
                      refine ⟨596320488486046524734147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590187969296124065957725 596320488486046524734147)
                      ·
                        rfl

theorem cell23_1161330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1161330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161330 prefixEnd_1161330 := by exact prefixLift 1161330
  have htrace : WordTrace (prefixWord ++ tailWord_1161330) baseStart_1161330 baseEnd_1161330 := by
    simpa [prefixWord, tailWord_1161330, baseEnd_1161330] using wordTrace_append hprefix tailTrace_1161330
  have hstable : (prefixWord ++ tailWord_1161330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161330).length < 2 ^ (prefixWord ++ tailWord_1161330).sum := by decide
  have hdescent : baseEnd_1161330 < baseStart_1161330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161336 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_1161336 : Nat := 118140960795 + 1161336 * 2 ^ 59
def prefixEnd_1161336 : Nat := 4983230072969 + 3 ^ 40 * 1161336 * 2
def baseEnd_1161336 : Nat := 596323569369973501259119

theorem tailTrace_1161336 : CollatzResearch.WordTrace tailWord_1161336 prefixEnd_1161336 596323569369973501259119 := by
  unfold tailWord_1161336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21178701860342743621611931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28238269147123658162149241 21178701860342743621611931)
  ·
    refine ⟨31768052790514115432417897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21178701860342743621611931 31768052790514115432417897)
    ·
      refine ⟨23826039592885586574313423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31768052790514115432417897 23826039592885586574313423)
      ·
        refine ⟨35739059389328379861470135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23826039592885586574313423 35739059389328379861470135)
        ·
          refine ⟨53608589083992569792205203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35739059389328379861470135 53608589083992569792205203)
          ·
            refine ⟨80412883625988854688307805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53608589083992569792205203 80412883625988854688307805)
            ·
              refine ⟨30154831359745820508115427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80412883625988854688307805 30154831359745820508115427)
              ·
                refine ⟨45232247039618730762173141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30154831359745820508115427 45232247039618730762173141)
                ·
                  refine ⟨1060130789991064002238433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 45232247039618730762173141 1060130789991064002238433)
                  ·
                    refine ⟨795098092493298001678825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060130789991064002238433 795098092493298001678825)
                    ·
                      refine ⟨596323569369973501259119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795098092493298001678825 596323569369973501259119)
                      ·
                        rfl

theorem cell23_1161336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_1161336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161336 prefixEnd_1161336 := by exact prefixLift 1161336
  have htrace : WordTrace (prefixWord ++ tailWord_1161336) baseStart_1161336 baseEnd_1161336 := by
    simpa [prefixWord, tailWord_1161336, baseEnd_1161336] using wordTrace_append hprefix tailTrace_1161336
  have hstable : (prefixWord ++ tailWord_1161336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161336).length < 2 ^ (prefixWord ++ tailWord_1161336).sum := by decide
  have hdescent : baseEnd_1161336 < baseStart_1161336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161353 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 3, 2, 2]
def baseStart_1161353 : Nat := 118140960795 + 1161353 * 2 ^ 59
def prefixEnd_1161353 : Nat := 4983230072969 + 3 ^ 40 * 1161353 * 2
def baseEnd_1161353 : Nat := 596332298541099934746541

theorem tailTrace_1161353 : CollatzResearch.WordTrace tailWord_1161353 prefixEnd_1161353 596332298541099934746541 := by
  unfold tailWord_1161353
  simp only [CollatzResearch.WordTrace]
  refine ⟨42358023761623899146592713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28238682507749266097728475 42358023761623899146592713)
  ·
    refine ⟨31768517821217924359944535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42358023761623899146592713 31768517821217924359944535)
    ·
      refine ⟨47652776731826886539916803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31768517821217924359944535 47652776731826886539916803)
      ·
        refine ⟨71479165097740329809875205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47652776731826886539916803 71479165097740329809875205)
        ·
          refine ⟨13402343455826311839351601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71479165097740329809875205 13402343455826311839351601)
          ·
            refine ⟨10051757591869733879513701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13402343455826311839351601 10051757591869733879513701)
            ·
              refine ⟨1884704548475575102408819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10051757591869733879513701 1884704548475575102408819)
              ·
                refine ⟨2827056822713362653613229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884704548475575102408819 2827056822713362653613229)
                ·
                  refine ⟨1060146308517510995104961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2827056822713362653613229 1060146308517510995104961)
                  ·
                    refine ⟨795109731388133246328721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060146308517510995104961 795109731388133246328721)
                    ·
                      refine ⟨596332298541099934746541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795109731388133246328721 596332298541099934746541)
                      ·
                        rfl

theorem cell23_1161353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 2, 2].length) (baseStart_1161353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161353 prefixEnd_1161353 := by exact prefixLift 1161353
  have htrace : WordTrace (prefixWord ++ tailWord_1161353) baseStart_1161353 baseEnd_1161353 := by
    simpa [prefixWord, tailWord_1161353, baseEnd_1161353] using wordTrace_append hprefix tailTrace_1161353
  have hstable : (prefixWord ++ tailWord_1161353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161353).length < 2 ^ (prefixWord ++ tailWord_1161353).sum := by decide
  have hdescent : baseEnd_1161353 < baseStart_1161353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161373 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1161373 : Nat := 118140960795 + 1161373 * 2 ^ 59
def prefixEnd_1161373 : Nat := 4983230072969 + 3 ^ 40 * 1161373 * 2
def baseEnd_1161373 : Nat := 596342568154189856496449

theorem tailTrace_1161373 : CollatzResearch.WordTrace tailWord_1161373 prefixEnd_1161373 596342568154189856496449 := by
  unfold tailWord_1161373
  simp only [CollatzResearch.WordTrace]
  refine ⟨42358753221551442562320773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28239168814367628374880515 42358753221551442562320773)
  ·
    refine ⟨7942266229040895480435145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42358753221551442562320773 7942266229040895480435145)
    ·
      refine ⟨5956699671780671610326359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7942266229040895480435145 5956699671780671610326359)
      ·
        refine ⟨8935049507671007415489539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956699671780671610326359 8935049507671007415489539)
        ·
          refine ⟨13402574261506511123234309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935049507671007415489539 13402574261506511123234309)
          ·
            refine ⟨2512982674032470835606433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13402574261506511123234309 2512982674032470835606433)
            ·
              refine ⟨1884737005524353126704825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512982674032470835606433 1884737005524353126704825)
              ·
                refine ⟨1413552754143264845028619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884737005524353126704825 1413552754143264845028619)
                ·
                  refine ⟨2120329131214897267542929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413552754143264845028619 2120329131214897267542929)
                  ·
                    refine ⟨1590246848411172950657197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120329131214897267542929 1590246848411172950657197)
                    ·
                      refine ⟨596342568154189856496449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590246848411172950657197 596342568154189856496449)
                      ·
                        rfl

theorem cell23_1161373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1161373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161373 prefixEnd_1161373 := by exact prefixLift 1161373
  have htrace : WordTrace (prefixWord ++ tailWord_1161373) baseStart_1161373 baseEnd_1161373 := by
    simpa [prefixWord, tailWord_1161373, baseEnd_1161373] using wordTrace_append hprefix tailTrace_1161373
  have hstable : (prefixWord ++ tailWord_1161373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161373).length < 2 ^ (prefixWord ++ tailWord_1161373).sum := by decide
  have hdescent : baseEnd_1161373 < baseStart_1161373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161376 : List Nat := [2, 1, 1, 4, 2, 4, 2, 7]
def baseStart_1161376 : Nat := 118140960795 + 1161376 * 2 ^ 59
def prefixEnd_1161376 : Nat := 4983230072969 + 3 ^ 40 * 1161376 * 2
def baseEnd_1161376 : Nat := 22086818836894568324405

theorem tailTrace_1161376 : CollatzResearch.WordTrace tailWord_1161376 prefixEnd_1161376 22086818836894568324405 := by
  unfold tailWord_1161376
  simp only [CollatzResearch.WordTrace]
  refine ⟨21179431320270287037339991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28239241760360382716453321 21179431320270287037339991)
  ·
    refine ⟨31769146980405430556009987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21179431320270287037339991 31769146980405430556009987)
    ·
      refine ⟨47653720470608145834014981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31769146980405430556009987 47653720470608145834014981)
      ·
        refine ⟨8935072588239027343877809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47653720470608145834014981 8935072588239027343877809)
        ·
          refine ⟨6701304441179270507908357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8935072588239027343877809 6701304441179270507908357)
          ·
            refine ⟨1256494582721113220232817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6701304441179270507908357 1256494582721113220232817)
            ·
              refine ⟨942370937040834915174613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256494582721113220232817 942370937040834915174613)
              ·
                refine ⟨22086818836894568324405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 942370937040834915174613 22086818836894568324405)
                ·
                  rfl

theorem cell23_1161376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 7].length) (baseStart_1161376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161376 prefixEnd_1161376 := by exact prefixLift 1161376
  have htrace : WordTrace (prefixWord ++ tailWord_1161376) baseStart_1161376 baseEnd_1161376 := by
    simpa [prefixWord, tailWord_1161376, baseEnd_1161376] using wordTrace_append hprefix tailTrace_1161376
  have hstable : (prefixWord ++ tailWord_1161376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161376).length < 2 ^ (prefixWord ++ tailWord_1161376).sum := by decide
  have hdescent : baseEnd_1161376 < baseStart_1161376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161390 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1161390 : Nat := 118140960795 + 1161390 * 2 ^ 59
def prefixEnd_1161390 : Nat := 4983230072969 + 3 ^ 40 * 1161390 * 2
def baseEnd_1161390 : Nat := 596351297325316289983871

theorem tailTrace_1161390 : CollatzResearch.WordTrace tailWord_1161390 prefixEnd_1161390 596351297325316289983871 := by
  unfold tailWord_1161390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294921657811231808211203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28239582174993236310459749 5294921657811231808211203)
  ·
    refine ⟨7942382486716847712316805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5294921657811231808211203 7942382486716847712316805)
    ·
      refine ⟨1489196716259408946059401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7942382486716847712316805 1489196716259408946059401)
      ·
        refine ⟨1116897537194556709544551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1489196716259408946059401 1116897537194556709544551)
        ·
          refine ⟨1675346305791835064316827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116897537194556709544551 1675346305791835064316827)
          ·
            refine ⟨2513019458687752596475241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675346305791835064316827 2513019458687752596475241)
            ·
              refine ⟨1884764594015814447356431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513019458687752596475241 1884764594015814447356431)
              ·
                refine ⟨2827146891023721671034647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884764594015814447356431 2827146891023721671034647)
                ·
                  refine ⟨4240720336535582506551971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827146891023721671034647 4240720336535582506551971)
                  ·
                    refine ⟨6361080504803373759827957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240720336535582506551971 6361080504803373759827957)
                    ·
                      refine ⟨596351297325316289983871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6361080504803373759827957 596351297325316289983871)
                      ·
                        rfl

theorem cell23_1161390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1161390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161390 prefixEnd_1161390 := by exact prefixLift 1161390
  have htrace : WordTrace (prefixWord ++ tailWord_1161390) baseStart_1161390 baseEnd_1161390 := by
    simpa [prefixWord, tailWord_1161390, baseEnd_1161390] using wordTrace_append hprefix tailTrace_1161390
  have hstable : (prefixWord ++ tailWord_1161390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161390).length < 2 ^ (prefixWord ++ tailWord_1161390).sum := by decide
  have hdescent : baseEnd_1161390 < baseStart_1161390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161404 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_1161404 : Nat := 118140960795 + 1161404 * 2 ^ 59
def prefixEnd_1161404 : Nat := 4983230072969 + 3 ^ 40 * 1161404 * 2
def baseEnd_1161404 : Nat := 596358486054479235208807

theorem tailTrace_1161404 : CollatzResearch.WordTrace tailWord_1161404 prefixEnd_1161404 596358486054479235208807 := by
  unfold tailWord_1161404
  simp only [CollatzResearch.WordTrace]
  refine ⟨21179941942219567428349633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28239922589626089904466177 21179941942219567428349633)
  ·
    refine ⟨15884956456664675571262225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21179941942219567428349633 15884956456664675571262225)
    ·
      refine ⟨11913717342498506678446669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15884956456664675571262225 11913717342498506678446669)
      ·
        refine ⟨4467644003436940004417501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11913717342498506678446669 4467644003436940004417501)
        ·
          refine ⟨1675366501288852501656563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4467644003436940004417501 1675366501288852501656563)
          ·
            refine ⟨2513049751933278752484845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675366501288852501656563 2513049751933278752484845)
            ·
              refine ⟨942393656974979532181817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513049751933278752484845 942393656974979532181817)
              ·
                refine ⟨706795242731234649136363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942393656974979532181817 706795242731234649136363)
                ·
                  refine ⟨1060192864096851973704545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706795242731234649136363 1060192864096851973704545)
                  ·
                    refine ⟨795144648072638980278409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060192864096851973704545 795144648072638980278409)
                    ·
                      refine ⟨596358486054479235208807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795144648072638980278409 596358486054479235208807)
                      ·
                        rfl

theorem cell23_1161404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_1161404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161404 prefixEnd_1161404 := by exact prefixLift 1161404
  have htrace : WordTrace (prefixWord ++ tailWord_1161404) baseStart_1161404 baseEnd_1161404 := by
    simpa [prefixWord, tailWord_1161404, baseEnd_1161404] using wordTrace_append hprefix tailTrace_1161404
  have hstable : (prefixWord ++ tailWord_1161404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161404).length < 2 ^ (prefixWord ++ tailWord_1161404).sum := by decide
  have hdescent : baseEnd_1161404 < baseStart_1161404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161439 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1161439 : Nat := 118140960795 + 1161439 * 2 ^ 59
def prefixEnd_1161439 : Nat := 4983230072969 + 3 ^ 40 * 1161439 * 2
def baseEnd_1161439 : Nat := 596376457877386598271145

theorem tailTrace_1161439 : CollatzResearch.WordTrace tailWord_1161439 prefixEnd_1161439 596376457877386598271145 := by
  unfold tailWord_1161439
  simp only [CollatzResearch.WordTrace]
  refine ⟨42361160439312335834223371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28240773626208223889482247 42361160439312335834223371)
  ·
    refine ⟨63541740658968503751335057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42361160439312335834223371 63541740658968503751335057)
    ·
      refine ⟨47656305494226377813501293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63541740658968503751335057 47656305494226377813501293)
      ·
        refine ⟨17871114560334891680062985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47656305494226377813501293 17871114560334891680062985)
        ·
          refine ⟨13403335920251168760047239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17871114560334891680062985 13403335920251168760047239)
          ·
            refine ⟨20105003880376753140070859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403335920251168760047239 20105003880376753140070859)
            ·
              refine ⟨30157505820565129710106289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20105003880376753140070859 30157505820565129710106289)
              ·
                refine ⟨22618129365423847282579717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30157505820565129710106289 22618129365423847282579717)
                ·
                  refine ⟨4240899256016971365483697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22618129365423847282579717 4240899256016971365483697)
                  ·
                    refine ⟨3180674442012728524112773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4240899256016971365483697 3180674442012728524112773)
                    ·
                      refine ⟨596376457877386598271145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3180674442012728524112773 596376457877386598271145)
                      ·
                        rfl

theorem cell23_1161439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1161439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161439 prefixEnd_1161439 := by exact prefixLift 1161439
  have htrace : WordTrace (prefixWord ++ tailWord_1161439) baseStart_1161439 baseEnd_1161439 := by
    simpa [prefixWord, tailWord_1161439, baseEnd_1161439] using wordTrace_append hprefix tailTrace_1161439
  have hstable : (prefixWord ++ tailWord_1161439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161439).length < 2 ^ (prefixWord ++ tailWord_1161439).sum := by decide
  have hdescent : baseEnd_1161439 < baseStart_1161439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161447 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1161447 : Nat := 118140960795 + 1161447 * 2 ^ 59
def prefixEnd_1161447 : Nat := 4983230072969 + 3 ^ 40 * 1161447 * 2
def baseEnd_1161447 : Nat := 596380565722622566971109

theorem tailTrace_1161447 : CollatzResearch.WordTrace tailWord_1161447 prefixEnd_1161447 596380565722622566971109 := by
  unfold tailWord_1161447
  simp only [CollatzResearch.WordTrace]
  refine ⟨42361452223283353200514595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28240968148855568800343063 42361452223283353200514595)
  ·
    refine ⟨63542178334925029800771893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42361452223283353200514595 63542178334925029800771893)
    ·
      refine ⟨5957079218899221543822365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63542178334925029800771893 5957079218899221543822365)
      ·
        refine ⟨2233904707087208078933387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5957079218899221543822365 2233904707087208078933387)
        ·
          refine ⟨3350857060630812118400081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233904707087208078933387 3350857060630812118400081)
          ·
            refine ⟨2513142795473109088800061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3350857060630812118400081 2513142795473109088800061)
            ·
              refine ⟨942428548302415908300023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513142795473109088800061 942428548302415908300023)
              ·
                refine ⟨1413642822453623862450035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942428548302415908300023 1413642822453623862450035)
                ·
                  refine ⟨2120464233680435793675053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413642822453623862450035 2120464233680435793675053)
                  ·
                    refine ⟨795174087630163422628145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120464233680435793675053 795174087630163422628145)
                    ·
                      refine ⟨596380565722622566971109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795174087630163422628145 596380565722622566971109)
                      ·
                        rfl

theorem cell23_1161447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1161447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161447 prefixEnd_1161447 := by exact prefixLift 1161447
  have htrace : WordTrace (prefixWord ++ tailWord_1161447) baseStart_1161447 baseEnd_1161447 := by
    simpa [prefixWord, tailWord_1161447, baseEnd_1161447] using wordTrace_append hprefix tailTrace_1161447
  have hstable : (prefixWord ++ tailWord_1161447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161447).length < 2 ^ (prefixWord ++ tailWord_1161447).sum := by decide
  have hdescent : baseEnd_1161447 < baseStart_1161447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161516 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_1161516 : Nat := 118140960795 + 1161516 * 2 ^ 59
def prefixEnd_1161516 : Nat := 4983230072969 + 3 ^ 40 * 1161516 * 2
def baseEnd_1161516 : Nat := 596415995887782797008291

theorem tailTrace_1161516 : CollatzResearch.WordTrace tailWord_1161516 prefixEnd_1161516 596415995887782797008291 := by
  unfold tailWord_1161516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21181984430016688992388201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28242645906688918656517601 21181984430016688992388201)
  ·
    refine ⟨15886488322512516744291151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21181984430016688992388201 15886488322512516744291151)
    ·
      refine ⟨23829732483768775116436727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15886488322512516744291151 23829732483768775116436727)
      ·
        refine ⟨35744598725653162674655091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23829732483768775116436727 35744598725653162674655091)
        ·
          refine ⟨53616898088479744011982637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35744598725653162674655091 53616898088479744011982637)
          ·
            refine ⟨20106336783179904004493489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53616898088479744011982637 20106336783179904004493489)
            ·
              refine ⟨15079752587384928003370117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20106336783179904004493489 15079752587384928003370117)
              ·
                refine ⟨2827453610134674000631897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15079752587384928003370117 2827453610134674000631897)
                ·
                  refine ⟨2120590207601005500473923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827453610134674000631897 2120590207601005500473923)
                  ·
                    refine ⟨3180885311401508250710885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120590207601005500473923 3180885311401508250710885)
                    ·
                      refine ⟨596415995887782797008291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3180885311401508250710885 596415995887782797008291)
                      ·
                        rfl

theorem cell23_1161516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_1161516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161516 prefixEnd_1161516 := by exact prefixLift 1161516
  have htrace : WordTrace (prefixWord ++ tailWord_1161516) baseStart_1161516 baseEnd_1161516 := by
    simpa [prefixWord, tailWord_1161516, baseEnd_1161516] using wordTrace_append hprefix tailTrace_1161516
  have hstable : (prefixWord ++ tailWord_1161516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161516).length < 2 ^ (prefixWord ++ tailWord_1161516).sum := by decide
  have hdescent : baseEnd_1161516 < baseStart_1161516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161519 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_1161519 : Nat := 118140960795 + 1161519 * 2 ^ 59
def prefixEnd_1161519 : Nat := 4983230072969 + 3 ^ 40 * 1161519 * 2
def baseEnd_1161519 : Nat := 596417536329746285270777

theorem tailTrace_1161519 : CollatzResearch.WordTrace tailWord_1161519 prefixEnd_1161519 596417536329746285270777 := by
  unfold tailWord_1161519
  simp only [CollatzResearch.WordTrace]
  refine ⟨42364078279022509497135611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28242718852681672998090407 42364078279022509497135611)
  ·
    refine ⟨63546117418533764245703417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42364078279022509497135611 63546117418533764245703417)
    ·
      refine ⟨47659588063900323184277563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63546117418533764245703417 47659588063900323184277563)
      ·
        refine ⟨71489382095850484776416345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47659588063900323184277563 71489382095850484776416345)
        ·
          refine ⟨53617036571887863582312259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71489382095850484776416345 53617036571887863582312259)
          ·
            refine ⟨80425554857831795373468389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53617036571887863582312259 80425554857831795373468389)
            ·
              refine ⟨15079791535843461632525323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80425554857831795373468389 15079791535843461632525323)
              ·
                refine ⟨22619687303765192448787985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15079791535843461632525323 22619687303765192448787985)
                ·
                  refine ⟨16964765477823894336590989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22619687303765192448787985 16964765477823894336590989)
                  ·
                    refine ⟨6361787054183960376221621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16964765477823894336590989 6361787054183960376221621)
                    ·
                      refine ⟨596417536329746285270777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6361787054183960376221621 596417536329746285270777)
                      ·
                        rfl

theorem cell23_1161519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_1161519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161519 prefixEnd_1161519 := by exact prefixLift 1161519
  have htrace : WordTrace (prefixWord ++ tailWord_1161519) baseStart_1161519 baseEnd_1161519 := by
    simpa [prefixWord, tailWord_1161519, baseEnd_1161519] using wordTrace_append hprefix tailTrace_1161519
  have hstable : (prefixWord ++ tailWord_1161519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161519).length < 2 ^ (prefixWord ++ tailWord_1161519).sum := by decide
  have hdescent : baseEnd_1161519 < baseStart_1161519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161536 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_1161536 : Nat := 118140960795 + 1161536 * 2 ^ 59
def prefixEnd_1161536 : Nat := 4983230072969 + 3 ^ 40 * 1161536 * 2
def baseEnd_1161536 : Nat := 596426265500872718758199

theorem tailTrace_1161536 : CollatzResearch.WordTrace tailWord_1161536 prefixEnd_1161536 596426265500872718758199 := by
  unfold tailWord_1161536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21182349159980460700252231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28243132213307280933669641 21182349159980460700252231)
  ·
    refine ⟨31773523739970691050378347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21182349159980460700252231 31773523739970691050378347)
    ·
      refine ⟨47660285609956036575567521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31773523739970691050378347 47660285609956036575567521)
      ·
        refine ⟨35745214207467027431675641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47660285609956036575567521 35745214207467027431675641)
        ·
          refine ⟨26808910655600270573756731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35745214207467027431675641 26808910655600270573756731)
          ·
            refine ⟨40213365983400405860635097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26808910655600270573756731 40213365983400405860635097)
            ·
              refine ⟨30160024487550304395476323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40213365983400405860635097 30160024487550304395476323)
              ·
                refine ⟨45240036731325456593214485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30160024487550304395476323 45240036731325456593214485)
                ·
                  refine ⟨2120626721780880777806929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45240036731325456593214485 2120626721780880777806929)
                  ·
                    refine ⟨1590470041335660583355197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120626721780880777806929 1590470041335660583355197)
                    ·
                      refine ⟨596426265500872718758199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590470041335660583355197 596426265500872718758199)
                      ·
                        rfl

theorem cell23_1161536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_1161536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161536 prefixEnd_1161536 := by exact prefixLift 1161536
  have htrace : WordTrace (prefixWord ++ tailWord_1161536) baseStart_1161536 baseEnd_1161536 := by
    simpa [prefixWord, tailWord_1161536, baseEnd_1161536] using wordTrace_append hprefix tailTrace_1161536
  have hstable : (prefixWord ++ tailWord_1161536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161536).length < 2 ^ (prefixWord ++ tailWord_1161536).sum := by decide
  have hdescent : baseEnd_1161536 < baseStart_1161536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161556 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1161556 : Nat := 118140960795 + 1161556 * 2 ^ 59
def prefixEnd_1161556 : Nat := 4983230072969 + 3 ^ 40 * 1161556 * 2
def baseEnd_1161556 : Nat := 66270726123773626723123

theorem tailTrace_1161556 : CollatzResearch.WordTrace tailWord_1161556 prefixEnd_1161556 66270726123773626723123 := by
  unfold tailWord_1161556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21182713889944232408116261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28243618519925643210821681 21182713889944232408116261)
  ·
    refine ⟨3971758854364543576521799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21182713889944232408116261 3971758854364543576521799)
    ·
      refine ⟨5957638281546815364782699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3971758854364543576521799 5957638281546815364782699)
      ·
        refine ⟨8936457422320223047174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5957638281546815364782699 8936457422320223047174049)
        ·
          refine ⟨6702343066740167285380537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8936457422320223047174049 6702343066740167285380537)
          ·
            refine ⟨5026757300055125464035403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6702343066740167285380537 5026757300055125464035403)
            ·
              refine ⟨7540135950082688196053105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026757300055125464035403 7540135950082688196053105)
              ·
                refine ⟨5655101962562016147039829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7540135950082688196053105 5655101962562016147039829)
                ·
                  refine ⟨66270726123773626723123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5655101962562016147039829 66270726123773626723123)
                  ·
                    rfl

theorem cell23_1161556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1161556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161556 prefixEnd_1161556 := by exact prefixLift 1161556
  have htrace : WordTrace (prefixWord ++ tailWord_1161556) baseStart_1161556 baseEnd_1161556 := by
    simpa [prefixWord, tailWord_1161556, baseEnd_1161556] using wordTrace_append hprefix tailTrace_1161556
  have hstable : (prefixWord ++ tailWord_1161556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161556).length < 2 ^ (prefixWord ++ tailWord_1161556).sum := by decide
  have hdescent : baseEnd_1161556 < baseStart_1161556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161570 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1161570 : Nat := 118140960795 + 1161570 * 2 ^ 59
def prefixEnd_1161570 : Nat := 4983230072969 + 3 ^ 40 * 1161570 * 2
def baseEnd_1161570 : Nat := 596443723843125585733043

theorem tailTrace_1161570 : CollatzResearch.WordTrace tailWord_1161570 prefixEnd_1161570 596443723843125585733043 := by
  unfold tailWord_1161570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10591484600459436301810541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28243958934558496804828109 10591484600459436301810541)
  ·
    refine ⟨3971806725172288613178953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10591484600459436301810541 3971806725172288613178953)
    ·
      refine ⟨2978855043879216459884215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3971806725172288613178953 2978855043879216459884215)
      ·
        refine ⟨4468282565818824689826323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978855043879216459884215 4468282565818824689826323)
        ·
          refine ⟨6702423848728237034739485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468282565818824689826323 6702423848728237034739485)
          ·
            refine ⟨2513408943273088888027307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6702423848728237034739485 2513408943273088888027307)
            ·
              refine ⟨3770113414909633332040961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513408943273088888027307 3770113414909633332040961)
              ·
                refine ⟨2827585061182224999030721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770113414909633332040961 2827585061182224999030721)
                ·
                  refine ⟨2120688795886668749273041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827585061182224999030721 2120688795886668749273041)
                  ·
                    refine ⟨1590516596915001561954781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120688795886668749273041 1590516596915001561954781)
                    ·
                      refine ⟨596443723843125585733043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590516596915001561954781 596443723843125585733043)
                      ·
                        rfl

theorem cell23_1161570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1161570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161570 prefixEnd_1161570 := by exact prefixLift 1161570
  have htrace : WordTrace (prefixWord ++ tailWord_1161570) baseStart_1161570 baseEnd_1161570 := by
    simpa [prefixWord, tailWord_1161570, baseEnd_1161570] using wordTrace_append hprefix tailTrace_1161570
  have hstable : (prefixWord ++ tailWord_1161570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161570).length < 2 ^ (prefixWord ++ tailWord_1161570).sum := by decide
  have hdescent : baseEnd_1161570 < baseStart_1161570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161583 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 3]
def baseStart_1161583 : Nat := 118140960795 + 1161583 * 2 ^ 59
def prefixEnd_1161583 : Nat := 4983230072969 + 3 ^ 40 * 1161583 * 2
def baseEnd_1161583 : Nat := 596450399091634034870483

theorem tailTrace_1161583 : CollatzResearch.WordTrace tailWord_1161583 prefixEnd_1161583 596450399091634034870483 := by
  unfold tailWord_1161583
  simp only [CollatzResearch.WordTrace]
  refine ⟨42366412550790648427465403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28244275033860432284976935 42366412550790648427465403)
  ·
    refine ⟨63549618826185972641198105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42366412550790648427465403 63549618826185972641198105)
    ·
      refine ⟨47662214119639479480898579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63549618826185972641198105 47662214119639479480898579)
      ·
        refine ⟨71493321179459219221347869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47662214119639479480898579 71493321179459219221347869)
        ·
          refine ⟨26809995442297207208005451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71493321179459219221347869 26809995442297207208005451)
          ·
            refine ⟨40214993163445810812008177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26809995442297207208005451 40214993163445810812008177)
            ·
              refine ⟨30161244872584358109006133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40214993163445810812008177 30161244872584358109006133)
              ·
                refine ⟨2827616706804783572719325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30161244872584358109006133 2827616706804783572719325)
                ·
                  refine ⟨1060356265051793839769747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2827616706804783572719325 1060356265051793839769747)
                  ·
                    refine ⟨1590534397577690759654621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1060356265051793839769747 1590534397577690759654621)
                    ·
                      refine ⟨596450399091634034870483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590534397577690759654621 596450399091634034870483)
                      ·
                        rfl

theorem cell23_1161583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_1161583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161583 prefixEnd_1161583 := by exact prefixLift 1161583
  have htrace : WordTrace (prefixWord ++ tailWord_1161583) baseStart_1161583 baseEnd_1161583 := by
    simpa [prefixWord, tailWord_1161583, baseEnd_1161583] using wordTrace_append hprefix tailTrace_1161583
  have hstable : (prefixWord ++ tailWord_1161583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161583).length < 2 ^ (prefixWord ++ tailWord_1161583).sum := by decide
  have hdescent : baseEnd_1161583 < baseStart_1161583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161593 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 6, 3, 2]
def baseStart_1161593 : Nat := 118140960795 + 1161593 * 2 ^ 59
def prefixEnd_1161593 : Nat := 4983230072969 + 3 ^ 40 * 1161593 * 2
def baseEnd_1161593 : Nat := 596455533898178995745437

theorem tailTrace_1161593 : CollatzResearch.WordTrace tailWord_1161593 prefixEnd_1161593 596455533898178995745437 := by
  unfold tailWord_1161593
  simp only [CollatzResearch.WordTrace]
  refine ⟨42366777280754420135329433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28244518187169613423552955 42366777280754420135329433)
  ·
    refine ⟨31775082960565815101497075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42366777280754420135329433 31775082960565815101497075)
    ·
      refine ⟨47662624440848722652245613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31775082960565815101497075 47662624440848722652245613)
      ·
        refine ⟨17873484165318270994592105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47662624440848722652245613 17873484165318270994592105)
        ·
          refine ⟨13405113123988703245944079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17873484165318270994592105 13405113123988703245944079)
          ·
            refine ⟨20107669685983054868916119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405113123988703245944079 20107669685983054868916119)
            ·
              refine ⟨30161504528974582303374179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20107669685983054868916119 30161504528974582303374179)
              ·
                refine ⟨45242256793461873455061269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30161504528974582303374179 45242256793461873455061269)
                ·
                  refine ⟨2120730787193525318205997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45242256793461873455061269 2120730787193525318205997)
                  ·
                    refine ⟨795274045197571994327249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2120730787193525318205997 795274045197571994327249)
                    ·
                      refine ⟨596455533898178995745437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795274045197571994327249 596455533898178995745437)
                      ·
                        rfl

theorem cell23_1161593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_1161593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161593 prefixEnd_1161593 := by exact prefixLift 1161593
  have htrace : WordTrace (prefixWord ++ tailWord_1161593) baseStart_1161593 baseEnd_1161593 := by
    simpa [prefixWord, tailWord_1161593, baseEnd_1161593] using wordTrace_append hprefix tailTrace_1161593
  have hstable : (prefixWord ++ tailWord_1161593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161593).length < 2 ^ (prefixWord ++ tailWord_1161593).sum := by decide
  have hdescent : baseEnd_1161593 < baseStart_1161593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161603 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 3, 5]
def baseStart_1161603 : Nat := 118140960795 + 1161603 * 2 ^ 59
def prefixEnd_1161603 : Nat := 4983230072969 + 3 ^ 40 * 1161603 * 2
def baseEnd_1161603 : Nat := 198820222901574652206797

theorem tailTrace_1161603 : CollatzResearch.WordTrace tailWord_1161603 prefixEnd_1161603 198820222901574652206797 := by
  unfold tailWord_1161603
  simp only [CollatzResearch.WordTrace]
  refine ⟨42367142010718191843193463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28244761340478794562128975 42367142010718191843193463)
  ·
    refine ⟨63550713016077287764790195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42367142010718191843193463 63550713016077287764790195)
    ·
      refine ⟨95326069524115931647185293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63550713016077287764790195 95326069524115931647185293)
      ·
        refine ⟨35747276071543474367694485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95326069524115931647185293 35747276071543474367694485)
        ·
          refine ⟨1675653565853600360985679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35747276071543474367694485 1675653565853600360985679)
          ·
            refine ⟨2513480348780400541478519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675653565853600360985679 2513480348780400541478519)
            ·
              refine ⟨3770220523170600812217779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513480348780400541478519 3770220523170600812217779)
              ·
                refine ⟨5655330784755901218326669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770220523170600812217779 5655330784755901218326669)
                ·
                  refine ⟨2120749044283462956872501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5655330784755901218326669 2120749044283462956872501)
                  ·
                    refine ⟨198820222901574652206797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2120749044283462956872501 198820222901574652206797)
                    ·
                      rfl

theorem cell23_1161603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 5].length) (baseStart_1161603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161603 prefixEnd_1161603 := by exact prefixLift 1161603
  have htrace : WordTrace (prefixWord ++ tailWord_1161603) baseStart_1161603 baseEnd_1161603 := by
    simpa [prefixWord, tailWord_1161603, baseEnd_1161603] using wordTrace_append hprefix tailTrace_1161603
  have hstable : (prefixWord ++ tailWord_1161603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161603).length < 2 ^ (prefixWord ++ tailWord_1161603).sum := by decide
  have hdescent : baseEnd_1161603 < baseStart_1161603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161623 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_1161623 : Nat := 118140960795 + 1161623 * 2 ^ 59
def prefixEnd_1161623 : Nat := 4983230072969 + 3 ^ 40 * 1161623 * 2
def baseEnd_1161623 : Nat := 596470938317813878370299

theorem tailTrace_1161623 : CollatzResearch.WordTrace tailWord_1161623 prefixEnd_1161623 596470938317813878370299 := by
  unfold tailWord_1161623
  simp only [CollatzResearch.WordTrace]
  refine ⟨42367871470645735258921523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28245247647097156839281015 42367871470645735258921523)
  ·
    refine ⟨63551807205968602888382285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42367871470645735258921523 63551807205968602888382285)
    ·
      refine ⟨23831927702238226083143357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63551807205968602888382285 23831927702238226083143357)
      ·
        refine ⟨8936972888339334781178759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23831927702238226083143357 8936972888339334781178759)
        ·
          refine ⟨13405459332509002171768139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8936972888339334781178759 13405459332509002171768139)
          ·
            refine ⟨20108188998763503257652209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405459332509002171768139 20108188998763503257652209)
            ·
              refine ⟨15081141749072627443239157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20108188998763503257652209 15081141749072627443239157)
              ·
                refine ⟨1413857038975558822803671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15081141749072627443239157 1413857038975558822803671)
                ·
                  refine ⟨2120785558463338234205507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413857038975558822803671 2120785558463338234205507)
                  ·
                    refine ⟨3181178337695007351308261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120785558463338234205507 3181178337695007351308261)
                    ·
                      refine ⟨596470938317813878370299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3181178337695007351308261 596470938317813878370299)
                      ·
                        rfl

theorem cell23_1161623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_1161623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161623 prefixEnd_1161623 := by exact prefixLift 1161623
  have htrace : WordTrace (prefixWord ++ tailWord_1161623) baseStart_1161623 baseEnd_1161623 := by
    simpa [prefixWord, tailWord_1161623, baseEnd_1161623] using wordTrace_append hprefix tailTrace_1161623
  have hstable : (prefixWord ++ tailWord_1161623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161623).length < 2 ^ (prefixWord ++ tailWord_1161623).sum := by decide
  have hdescent : baseEnd_1161623 < baseStart_1161623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161636 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1161636 : Nat := 118140960795 + 1161636 * 2 ^ 59
def prefixEnd_1161636 : Nat := 4983230072969 + 3 ^ 40 * 1161636 * 2
def baseEnd_1161636 : Nat := 596477613566322327507739

theorem tailTrace_1161636 : CollatzResearch.WordTrace tailWord_1161636 prefixEnd_1161636 596477613566322327507739 := by
  unfold tailWord_1161636
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184172809799319239572381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28245563746399092319429841 21184172809799319239572381)
  ·
    refine ⟨7944064803674744714839643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21184172809799319239572381 7944064803674744714839643)
    ·
      refine ⟨11916097205512117072259465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7944064803674744714839643 11916097205512117072259465)
      ·
        refine ⟨8937072904134087804194599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11916097205512117072259465 8937072904134087804194599)
        ·
          refine ⟨13405609356201131706291899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8937072904134087804194599 13405609356201131706291899)
          ·
            refine ⟨20108414034301697559437849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405609356201131706291899 20108414034301697559437849)
            ·
              refine ⟨15081310525726273169578387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20108414034301697559437849 15081310525726273169578387)
              ·
                refine ⟨22621965788589409754367581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15081310525726273169578387 22621965788589409754367581)
                ·
                  refine ⟨8483237170721028657887843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22621965788589409754367581 8483237170721028657887843)
                  ·
                    refine ⟨12724855756081542986831765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8483237170721028657887843 12724855756081542986831765)
                    ·
                      refine ⟨596477613566322327507739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12724855756081542986831765 596477613566322327507739)
                      ·
                        rfl

theorem cell23_1161636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1161636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161636 prefixEnd_1161636 := by exact prefixLift 1161636
  have htrace : WordTrace (prefixWord ++ tailWord_1161636) baseStart_1161636 baseEnd_1161636 := by
    simpa [prefixWord, tailWord_1161636, baseEnd_1161636] using wordTrace_append hprefix tailTrace_1161636
  have hstable : (prefixWord ++ tailWord_1161636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161636).length < 2 ^ (prefixWord ++ tailWord_1161636).sum := by decide
  have hdescent : baseEnd_1161636 < baseStart_1161636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161640 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1161640 : Nat := 118140960795 + 1161640 * 2 ^ 59
def prefixEnd_1161640 : Nat := 4983230072969 + 3 ^ 40 * 1161640 * 2
def baseEnd_1161640 : Nat := 596479667488940311857721

theorem tailTrace_1161640 : CollatzResearch.WordTrace tailWord_1161640 prefixEnd_1161640 596479667488940311857721 := by
  unfold tailWord_1161640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184245755792073581145187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28245661007722764774860249 21184245755792073581145187)
  ·
    refine ⟨31776368633688110371717781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21184245755792073581145187 31776368633688110371717781)
    ·
      refine ⟨1489517279704130173674271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31776368633688110371717781 1489517279704130173674271)
      ·
        refine ⟨2234275919556195260511407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489517279704130173674271 2234275919556195260511407)
        ·
          refine ⟨3351413879334292890767111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234275919556195260511407 3351413879334292890767111)
          ·
            refine ⟨5027120819001439336150667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351413879334292890767111 5027120819001439336150667)
            ·
              refine ⟨7540681228502159004226001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027120819001439336150667 7540681228502159004226001)
              ·
                refine ⟨5655510921376619253169501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7540681228502159004226001 5655510921376619253169501)
                ·
                  refine ⟨2120816595516232219938563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5655510921376619253169501 2120816595516232219938563)
                  ·
                    refine ⟨3181224893274348329907845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120816595516232219938563 3181224893274348329907845)
                    ·
                      refine ⟨596479667488940311857721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3181224893274348329907845 596479667488940311857721)
                      ·
                        rfl

theorem cell23_1161640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1161640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161640 prefixEnd_1161640 := by exact prefixLift 1161640
  have htrace : WordTrace (prefixWord ++ tailWord_1161640) baseStart_1161640 baseEnd_1161640 := by
    simpa [prefixWord, tailWord_1161640, baseEnd_1161640] using wordTrace_append hprefix tailTrace_1161640
  have hstable : (prefixWord ++ tailWord_1161640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161640).length < 2 ^ (prefixWord ++ tailWord_1161640).sum := by decide
  have hdescent : baseEnd_1161640 < baseStart_1161640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161657 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1161657 : Nat := 118140960795 + 1161657 * 2 ^ 59
def prefixEnd_1161657 : Nat := 4983230072969 + 3 ^ 40 * 1161657 * 2
def baseEnd_1161657 : Nat := 596488396660066745345143

theorem tailTrace_1161657 : CollatzResearch.WordTrace tailWord_1161657 prefixEnd_1161657 596488396660066745345143 := by
  unfold tailWord_1161657
  simp only [CollatzResearch.WordTrace]
  refine ⟨42369111552522559065659225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28246074368348372710439483 42369111552522559065659225)
  ·
    refine ⟨31776833664391919299244419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42369111552522559065659225 31776833664391919299244419)
    ·
      refine ⟨47665250496587878948866629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31776833664391919299244419 47665250496587878948866629)
      ·
        refine ⟨8937234468110227302912493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47665250496587878948866629 8937234468110227302912493)
        ·
          refine ⟨3351462925541335238592185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8937234468110227302912493 3351462925541335238592185)
          ·
            refine ⟨2513597194156001428944139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3351462925541335238592185 2513597194156001428944139)
            ·
              refine ⟨3770395791234002143416209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513597194156001428944139 3770395791234002143416209)
              ·
                refine ⟨2827796843425501607562157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770395791234002143416209 2827796843425501607562157)
                ·
                  refine ⟨1060423816284563102835809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2827796843425501607562157 1060423816284563102835809)
                  ·
                    refine ⟨795317862213422327126857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060423816284563102835809 795317862213422327126857)
                    ·
                      refine ⟨596488396660066745345143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795317862213422327126857 596488396660066745345143)
                      ·
                        rfl

theorem cell23_1161657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1161657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161657 prefixEnd_1161657 := by exact prefixLift 1161657
  have htrace : WordTrace (prefixWord ++ tailWord_1161657) baseStart_1161657 baseEnd_1161657 := by
    simpa [prefixWord, tailWord_1161657, baseEnd_1161657] using wordTrace_append hprefix tailTrace_1161657
  have hstable : (prefixWord ++ tailWord_1161657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161657).length < 2 ^ (prefixWord ++ tailWord_1161657).sum := by decide
  have hdescent : baseEnd_1161657 < baseStart_1161657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161660 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1161660 : Nat := 118140960795 + 1161660 * 2 ^ 59
def prefixEnd_1161660 : Nat := 4983230072969 + 3 ^ 40 * 1161660 * 2
def baseEnd_1161660 : Nat := 596489937102030233607629

theorem tailTrace_1161660 : CollatzResearch.WordTrace tailWord_1161660 prefixEnd_1161660 596489937102030233607629 := by
  unfold tailWord_1161660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184610485755845289009217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28246147314341127052012289 21184610485755845289009217)
  ·
    refine ⟨15888457864316883966756913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21184610485755845289009217 15888457864316883966756913)
    ·
      refine ⟨11916343398237662975067685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15888457864316883966756913 11916343398237662975067685)
      ·
        refine ⟨2234314387169561807825191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11916343398237662975067685 2234314387169561807825191)
        ·
          refine ⟨3351471580754342711737787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234314387169561807825191 3351471580754342711737787)
          ·
            refine ⟨5027207371131514067606681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351471580754342711737787 5027207371131514067606681)
            ·
              refine ⟨3770405528348635550705011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027207371131514067606681 3770405528348635550705011)
              ·
                refine ⟨5655608292522953326057517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770405528348635550705011 5655608292522953326057517)
                ·
                  refine ⟨2120853109696107497271569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5655608292522953326057517 2120853109696107497271569)
                  ·
                    refine ⟨1590639832272080622953677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120853109696107497271569 1590639832272080622953677)
                    ·
                      refine ⟨596489937102030233607629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590639832272080622953677 596489937102030233607629)
                      ·
                        rfl

theorem cell23_1161660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1161660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161660 prefixEnd_1161660 := by exact prefixLift 1161660
  have htrace : WordTrace (prefixWord ++ tailWord_1161660) baseStart_1161660 baseEnd_1161660 := by
    simpa [prefixWord, tailWord_1161660, baseEnd_1161660] using wordTrace_append hprefix tailTrace_1161660
  have hstable : (prefixWord ++ tailWord_1161660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161660).length < 2 ^ (prefixWord ++ tailWord_1161660).sum := by decide
  have hdescent : baseEnd_1161660 < baseStart_1161660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161673 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_1161673 : Nat := 118140960795 + 1161673 * 2 ^ 59
def prefixEnd_1161673 : Nat := 4983230072969 + 3 ^ 40 * 1161673 * 2
def baseEnd_1161673 : Nat := 596496612350538682745069

theorem tailTrace_1161673 : CollatzResearch.WordTrace tailWord_1161673 prefixEnd_1161673 596496612350538682745069 := by
  unfold tailWord_1161673
  simp only [CollatzResearch.WordTrace]
  refine ⟨42369695120464593798241673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28246463413643062532161115 42369695120464593798241673)
  ·
    refine ⟨31777271340348445348681255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42369695120464593798241673 31777271340348445348681255)
    ·
      refine ⟨47665907010522668023021883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31777271340348445348681255 47665907010522668023021883)
      ·
        refine ⟨71498860515784002034532825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47665907010522668023021883 71498860515784002034532825)
        ·
          refine ⟨53624145386838001525899619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71498860515784002034532825 53624145386838001525899619)
          ·
            refine ⟨80436218080257002288849429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53624145386838001525899619 80436218080257002288849429)
            ·
              refine ⟨3770447722512046982289817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80436218080257002288849429 3770447722512046982289817)
              ·
                refine ⟨2827835791884035236717363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770447722512046982289817 2827835791884035236717363)
                ·
                  refine ⟨4241753687826052855076045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827835791884035236717363 4241753687826052855076045)
                  ·
                    refine ⟨1590657632934769820653517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4241753687826052855076045 1590657632934769820653517)
                    ·
                      refine ⟨596496612350538682745069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590657632934769820653517 596496612350538682745069)
                      ·
                        rfl

theorem cell23_1161673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_1161673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161673 prefixEnd_1161673 := by exact prefixLift 1161673
  have htrace : WordTrace (prefixWord ++ tailWord_1161673) baseStart_1161673 baseEnd_1161673 := by
    simpa [prefixWord, tailWord_1161673, baseEnd_1161673] using wordTrace_append hprefix tailTrace_1161673
  have hstable : (prefixWord ++ tailWord_1161673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161673).length < 2 ^ (prefixWord ++ tailWord_1161673).sum := by decide
  have hdescent : baseEnd_1161673 < baseStart_1161673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161674 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_1161674 : Nat := 118140960795 + 1161674 * 2 ^ 59
def prefixEnd_1161674 : Nat := 4983230072969 + 3 ^ 40 * 1161674 * 2
def baseEnd_1161674 : Nat := 596497125831193178832565

theorem tailTrace_1161674 : CollatzResearch.WordTrace tailWord_1161674 prefixEnd_1161674 596497125831193178832565 := by
  unfold tailWord_1161674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592432898365242742257019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28246487728973980646018717 10592432898365242742257019)
  ·
    refine ⟨15888649347547864113385529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10592432898365242742257019 15888649347547864113385529)
    ·
      refine ⟨11916487010660898085039147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15888649347547864113385529 11916487010660898085039147)
      ·
        refine ⟨17874730515991347127558721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916487010660898085039147 17874730515991347127558721)
        ·
          refine ⟨13406047886993510345669041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17874730515991347127558721 13406047886993510345669041)
          ·
            refine ⟨10054535915245132759251781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13406047886993510345669041 10054535915245132759251781)
            ·
              refine ⟨1885225484108462392359709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10054535915245132759251781 1885225484108462392359709)
              ·
                refine ⟨706959556540673397134891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1885225484108462392359709 706959556540673397134891)
                ·
                  refine ⟨1060439334811010095702337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706959556540673397134891 1060439334811010095702337)
                  ·
                    refine ⟨795329501108257571776753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060439334811010095702337 795329501108257571776753)
                    ·
                      refine ⟨596497125831193178832565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795329501108257571776753 596497125831193178832565)
                      ·
                        rfl

theorem cell23_1161674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_1161674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161674 prefixEnd_1161674 := by exact prefixLift 1161674
  have htrace : WordTrace (prefixWord ++ tailWord_1161674) baseStart_1161674 baseEnd_1161674 := by
    simpa [prefixWord, tailWord_1161674, baseEnd_1161674] using wordTrace_append hprefix tailTrace_1161674
  have hstable : (prefixWord ++ tailWord_1161674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161674).length < 2 ^ (prefixWord ++ tailWord_1161674).sum := by decide
  have hdescent : baseEnd_1161674 < baseStart_1161674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161690 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_1161690 : Nat := 118140960795 + 1161690 * 2 ^ 59
def prefixEnd_1161690 : Nat := 4983230072969 + 3 ^ 40 * 1161690 * 2
def baseEnd_1161690 : Nat := 596505341521665116232491

theorem tailTrace_1161690 : CollatzResearch.WordTrace tailWord_1161690 prefixEnd_1161690 596505341521665116232491 := by
  unfold tailWord_1161690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592578790350751425402631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28246876774268670467740349 10592578790350751425402631)
  ·
    refine ⟨15888868185526127138103947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10592578790350751425402631 15888868185526127138103947)
    ·
      refine ⟨23833302278289190707155921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15888868185526127138103947 23833302278289190707155921)
      ·
        refine ⟨17874976708716893030366941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23833302278289190707155921 17874976708716893030366941)
        ·
          refine ⟨6703116265768834886387603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17874976708716893030366941 6703116265768834886387603)
          ·
            refine ⟨10054674398653252329581405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703116265768834886387603 10054674398653252329581405)
            ·
              refine ⟨3770502899494969623593027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10054674398653252329581405 3770502899494969623593027)
              ·
                refine ⟨5655754349242454435389541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770502899494969623593027 5655754349242454435389541)
                ·
                  refine ⟨1060453940482960206635539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5655754349242454435389541 1060453940482960206635539)
                  ·
                    refine ⟨1590680910724440309953309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1060453940482960206635539 1590680910724440309953309)
                    ·
                      refine ⟨596505341521665116232491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590680910724440309953309 596505341521665116232491)
                      ·
                        rfl

theorem cell23_1161690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_1161690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161690 prefixEnd_1161690 := by exact prefixLift 1161690
  have htrace : WordTrace (prefixWord ++ tailWord_1161690) baseStart_1161690 baseEnd_1161690 := by
    simpa [prefixWord, tailWord_1161690, baseEnd_1161690] using wordTrace_append hprefix tailTrace_1161690
  have hstable : (prefixWord ++ tailWord_1161690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161690).length < 2 ^ (prefixWord ++ tailWord_1161690).sum := by decide
  have hdescent : baseEnd_1161690 < baseStart_1161690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161707 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 2, 1, 3]
def baseStart_1161707 : Nat := 118140960795 + 1161707 * 2 ^ 59
def prefixEnd_1161707 : Nat := 4983230072969 + 3 ^ 40 * 1161707 * 2
def baseEnd_1161707 : Nat := 596514070692791549719913

theorem tailTrace_1161707 : CollatzResearch.WordTrace tailWord_1161707 prefixEnd_1161707 596514070692791549719913 := by
  unfold tailWord_1161707
  simp only [CollatzResearch.WordTrace]
  refine ⟨42370935202341417604979375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28247290134894278403319583 42370935202341417604979375)
  ·
    refine ⟨63556402803512126407469063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42370935202341417604979375 63556402803512126407469063)
    ·
      refine ⟨95334604205268189611203595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63556402803512126407469063 95334604205268189611203595)
      ·
        refine ⟨143001906307902284416805393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95334604205268189611203595 143001906307902284416805393)
        ·
          refine ⟨107251429730926713312604045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143001906307902284416805393 107251429730926713312604045)
          ·
            refine ⟨40219286149097517492226517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107251429730926713312604045 40219286149097517492226517)
            ·
              refine ⟨942639519119473066224059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40219286149097517492226517 942639519119473066224059)
              ·
                refine ⟨1413959278679209599336089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942639519119473066224059 1413959278679209599336089)
                ·
                  refine ⟨1060469459009407199502067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413959278679209599336089 1060469459009407199502067)
                  ·
                    refine ⟨1590704188514110799253101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1060469459009407199502067 1590704188514110799253101)
                    ·
                      refine ⟨596514070692791549719913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1590704188514110799253101 596514070692791549719913)
                      ·
                        rfl

theorem cell23_1161707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 1, 3].length) (baseStart_1161707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161707 prefixEnd_1161707 := by exact prefixLift 1161707
  have htrace : WordTrace (prefixWord ++ tailWord_1161707) baseStart_1161707 baseEnd_1161707 := by
    simpa [prefixWord, tailWord_1161707, baseEnd_1161707] using wordTrace_append hprefix tailTrace_1161707
  have hstable : (prefixWord ++ tailWord_1161707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161707).length < 2 ^ (prefixWord ++ tailWord_1161707).sum := by decide
  have hdescent : baseEnd_1161707 < baseStart_1161707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161747 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 2, 2, 2]
def baseStart_1161747 : Nat := 118140960795 + 1161747 * 2 ^ 59
def prefixEnd_1161747 : Nat := 4983230072969 + 3 ^ 40 * 1161747 * 2
def baseEnd_1161747 : Nat := 596534609918971393219729

theorem tailTrace_1161747 : CollatzResearch.WordTrace tailWord_1161747 prefixEnd_1161747 596534609918971393219729 := by
  unfold tailWord_1161747
  simp only [CollatzResearch.WordTrace]
  refine ⟨42372394122196504436435495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28248262748131002957623663 42372394122196504436435495)
  ·
    refine ⟨63558591183294756654653243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42372394122196504436435495 63558591183294756654653243)
    ·
      refine ⟨95337886774942134981979865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63558591183294756654653243 95337886774942134981979865)
      ·
        refine ⟨71503415081206601236484899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95337886774942134981979865 71503415081206601236484899)
        ·
          refine ⟨107255122621809901854727349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71503415081206601236484899 107255122621809901854727349)
          ·
            refine ⟨10055167745794678298880689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107255122621809901854727349 10055167745794678298880689)
            ·
              refine ⟨7541375809346008724160517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10055167745794678298880689 7541375809346008724160517)
              ·
                refine ⟨1414007964252376635780097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7541375809346008724160517 1414007964252376635780097)
                ·
                  refine ⟨1060505973189282476835073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414007964252376635780097 1060505973189282476835073)
                  ·
                    refine ⟨795379479891961857626305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060505973189282476835073 795379479891961857626305)
                    ·
                      refine ⟨596534609918971393219729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795379479891961857626305 596534609918971393219729)
                      ·
                        rfl

theorem cell23_1161747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2, 2].length) (baseStart_1161747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161747 prefixEnd_1161747 := by exact prefixLift 1161747
  have htrace : WordTrace (prefixWord ++ tailWord_1161747) baseStart_1161747 baseEnd_1161747 := by
    simpa [prefixWord, tailWord_1161747, baseEnd_1161747] using wordTrace_append hprefix tailTrace_1161747
  have hstable : (prefixWord ++ tailWord_1161747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161747).length < 2 ^ (prefixWord ++ tailWord_1161747).sum := by decide
  have hdescent : baseEnd_1161747 < baseStart_1161747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161798 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1161798 : Nat := 118140960795 + 1161798 * 2 ^ 59
def prefixEnd_1161798 : Nat := 4983230072969 + 3 ^ 40 * 1161798 * 2
def baseEnd_1161798 : Nat := 596560797432350693681995

theorem tailTrace_1161798 : CollatzResearch.WordTrace tailWord_1161798 prefixEnd_1161798 596560797432350693681995 := by
  unfold tailWord_1161798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324195445156616879579439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28249502830007826764361365 1324195445156616879579439)
  ·
    refine ⟨1986293167734925319369159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1324195445156616879579439 1986293167734925319369159)
    ·
      refine ⟨2979439751602387979053739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986293167734925319369159 2979439751602387979053739)
      ·
        refine ⟨4469159627403581968580609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979439751602387979053739 4469159627403581968580609)
        ·
          refine ⟨3351869720552686476435457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469159627403581968580609 3351869720552686476435457)
          ·
            refine ⟨2513902290414514857326593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3351869720552686476435457 2513902290414514857326593)
            ·
              refine ⟨1885426717810886142994945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513902290414514857326593 1885426717810886142994945)
              ·
                refine ⟨1414070038358164607246209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885426717810886142994945 1414070038358164607246209)
                ·
                  refine ⟨1060552528768623455434657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414070038358164607246209 1060552528768623455434657)
                  ·
                    refine ⟨795414396576467591575993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060552528768623455434657 795414396576467591575993)
                    ·
                      refine ⟨596560797432350693681995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795414396576467591575993 596560797432350693681995)
                      ·
                        rfl

theorem cell23_1161798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1161798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161798 prefixEnd_1161798 := by exact prefixLift 1161798
  have htrace : WordTrace (prefixWord ++ tailWord_1161798) baseStart_1161798 baseEnd_1161798 := by
    simpa [prefixWord, tailWord_1161798, baseEnd_1161798] using wordTrace_append hprefix tailTrace_1161798
  have hstable : (prefixWord ++ tailWord_1161798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161798).length < 2 ^ (prefixWord ++ tailWord_1161798).sum := by decide
  have hdescent : baseEnd_1161798 < baseStart_1161798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161837 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1161837 : Nat := 118140960795 + 1161837 * 2 ^ 59
def prefixEnd_1161837 : Nat := 4983230072969 + 3 ^ 40 * 1161837 * 2
def baseEnd_1161837 : Nat := 596580823177876041094315

theorem tailTrace_1161837 : CollatzResearch.WordTrace tailWord_1161837 prefixEnd_1161837 596580823177876041094315 := by
  unfold tailWord_1161837
  simp only [CollatzResearch.WordTrace]
  refine ⟨42375676691870449807211765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28250451127913633204807843 42375676691870449807211765)
  ·
    refine ⟨3972719689862854669426103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42375676691870449807211765 3972719689862854669426103)
    ·
      refine ⟨5959079534794282004139155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3972719689862854669426103 5959079534794282004139155)
      ·
        refine ⟨8938619302191423006208733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959079534794282004139155 8938619302191423006208733)
        ·
          refine ⟨3351982238321783627328275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8938619302191423006208733 3351982238321783627328275)
          ·
            refine ⟨5027973357482675440992413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351982238321783627328275 5027973357482675440992413)
            ·
              refine ⟨1885490009056003290372155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5027973357482675440992413 1885490009056003290372155)
              ·
                refine ⟨2828235013584004935558233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885490009056003290372155 2828235013584004935558233)
                ·
                  refine ⟨2121176260188003701668675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828235013584004935558233 2121176260188003701668675)
                  ·
                    refine ⟨3181764390282005552503013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121176260188003701668675 3181764390282005552503013)
                    ·
                      refine ⟨596580823177876041094315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3181764390282005552503013 596580823177876041094315)
                      ·
                        rfl

theorem cell23_1161837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1161837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161837 prefixEnd_1161837 := by exact prefixLift 1161837
  have htrace : WordTrace (prefixWord ++ tailWord_1161837) baseStart_1161837 baseEnd_1161837 := by
    simpa [prefixWord, tailWord_1161837, baseEnd_1161837] using wordTrace_append hprefix tailTrace_1161837
  have hstable : (prefixWord ++ tailWord_1161837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161837).length < 2 ^ (prefixWord ++ tailWord_1161837).sum := by decide
  have hdescent : baseEnd_1161837 < baseStart_1161837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161847 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 1, 4]
def baseStart_1161847 : Nat := 118140960795 + 1161847 * 2 ^ 59
def prefixEnd_1161847 : Nat := 4983230072969 + 3 ^ 40 * 1161847 * 2
def baseEnd_1161847 : Nat := 198861985994807000656423

theorem tailTrace_1161847 : CollatzResearch.WordTrace tailWord_1161847 prefixEnd_1161847 198861985994807000656423 := by
  unfold tailWord_1161847
  simp only [CollatzResearch.WordTrace]
  refine ⟨42376041421834221515075795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28250694281222814343383863 42376041421834221515075795)
  ·
    refine ⟨63564062132751332272613693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42376041421834221515075795 63564062132751332272613693)
    ·
      refine ⟨23836523299781749602230135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63564062132751332272613693 23836523299781749602230135)
      ·
        refine ⟨35754784949672624403345203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23836523299781749602230135 35754784949672624403345203)
        ·
          refine ⟨53632177424508936605017805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35754784949672624403345203 53632177424508936605017805)
          ·
            refine ⟨20112066534190851226881677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53632177424508936605017805 20112066534190851226881677)
            ·
              refine ⟨7542024950321569210080629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20112066534190851226881677 7542024950321569210080629)
              ·
                refine ⟨707064839092647113445059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7542024950321569210080629 707064839092647113445059)
                ·
                  refine ⟨1060597258638970670167589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707064839092647113445059 1060597258638970670167589)
                  ·
                    refine ⟨198861985994807000656423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1060597258638970670167589 198861985994807000656423)
                    ·
                      rfl

theorem cell23_1161847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_1161847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161847 prefixEnd_1161847 := by exact prefixLift 1161847
  have htrace : WordTrace (prefixWord ++ tailWord_1161847) baseStart_1161847 baseEnd_1161847 := by
    simpa [prefixWord, tailWord_1161847, baseEnd_1161847] using wordTrace_append hprefix tailTrace_1161847
  have hstable : (prefixWord ++ tailWord_1161847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161847).length < 2 ^ (prefixWord ++ tailWord_1161847).sum := by decide
  have hdescent : baseEnd_1161847 < baseStart_1161847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161860 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1161860 : Nat := 118140960795 + 1161860 * 2 ^ 59
def prefixEnd_1161860 : Nat := 4983230072969 + 3 ^ 40 * 1161860 * 2
def baseEnd_1161860 : Nat := 66288070359214383456301

theorem tailTrace_1161860 : CollatzResearch.WordTrace tailWord_1161860 prefixEnd_1161860 66288070359214383456301 := by
  unfold tailWord_1161860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21188257785393562367649517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28251010380524749823532689 21188257785393562367649517)
  ·
    refine ⟨7945596669522585887868569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21188257785393562367649517 7945596669522585887868569)
    ·
      refine ⟨5959197502141939415901427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7945596669522585887868569 5959197502141939415901427)
      ·
        refine ⟨8938796253212909123852141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959197502141939415901427 8938796253212909123852141)
        ·
          refine ⟨3352048594954840921444553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8938796253212909123852141 3352048594954840921444553)
          ·
            refine ⟨2514036446216130691083415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3352048594954840921444553 2514036446216130691083415)
            ·
              refine ⟨3771054669324196036625123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514036446216130691083415 3771054669324196036625123)
              ·
                refine ⟨5656582003986294054937685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771054669324196036625123 5656582003986294054937685)
                ·
                  refine ⟨66288070359214383456301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5656582003986294054937685 66288070359214383456301)
                  ·
                    rfl

theorem cell23_1161860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1161860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161860 prefixEnd_1161860 := by exact prefixLift 1161860
  have htrace : WordTrace (prefixWord ++ tailWord_1161860) baseStart_1161860 baseEnd_1161860 := by
    simpa [prefixWord, tailWord_1161860, baseEnd_1161860] using wordTrace_append hprefix tailTrace_1161860
  have hstable : (prefixWord ++ tailWord_1161860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161860).length < 2 ^ (prefixWord ++ tailWord_1161860).sum := by decide
  have hdescent : baseEnd_1161860 < baseStart_1161860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161863 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1161863 : Nat := 118140960795 + 1161863 * 2 ^ 59
def prefixEnd_1161863 : Nat := 4983230072969 + 3 ^ 40 * 1161863 * 2
def baseEnd_1161863 : Nat := 596594173674892939369195

theorem tailTrace_1161863 : CollatzResearch.WordTrace tailWord_1161863 prefixEnd_1161863 596594173674892939369195 := by
  unfold tailWord_1161863
  simp only [CollatzResearch.WordTrace]
  refine ⟨42376624989776256247658243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28251083326517504165105495 42376624989776256247658243)
  ·
    refine ⟨63564937484664384371487365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42376624989776256247658243 63564937484664384371487365)
    ·
      refine ⟨11918425778374572069653881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63564937484664384371487365 11918425778374572069653881)
      ·
        refine ⟨8938819333780929052240411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11918425778374572069653881 8938819333780929052240411)
        ·
          refine ⟨13408229000671393578360617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8938819333780929052240411 13408229000671393578360617)
          ·
            refine ⟨10056171750503545183770463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13408229000671393578360617 10056171750503545183770463)
            ·
              refine ⟨15084257625755317775655695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10056171750503545183770463 15084257625755317775655695)
              ·
                refine ⟨22626386438632976663483543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15084257625755317775655695 22626386438632976663483543)
                ·
                  refine ⟨33939579657949464995225315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22626386438632976663483543 33939579657949464995225315)
                  ·
                    refine ⟨50909369486924197492837973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33939579657949464995225315 50909369486924197492837973)
                    ·
                      refine ⟨596594173674892939369195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 50909369486924197492837973 596594173674892939369195)
                      ·
                        rfl

theorem cell23_1161863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1161863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161863 prefixEnd_1161863 := by exact prefixLift 1161863
  have htrace : WordTrace (prefixWord ++ tailWord_1161863) baseStart_1161863 baseEnd_1161863 := by
    simpa [prefixWord, tailWord_1161863, baseEnd_1161863] using wordTrace_append hprefix tailTrace_1161863
  have hstable : (prefixWord ++ tailWord_1161863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161863).length < 2 ^ (prefixWord ++ tailWord_1161863).sum := by decide
  have hdescent : baseEnd_1161863 < baseStart_1161863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161937 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_1161937 : Nat := 118140960795 + 1161937 * 2 ^ 59
def prefixEnd_1161937 : Nat := 4983230072969 + 3 ^ 40 * 1161937 * 2
def baseEnd_1161937 : Nat := 198877390414441883281285

theorem tailTrace_1161937 : CollatzResearch.WordTrace tailWord_1161937 prefixEnd_1161937 198877390414441883281285 := by
  unfold tailWord_1161937
  simp only [CollatzResearch.WordTrace]
  refine ⟨42379323991508166885852065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28252882661005444590568043 42379323991508166885852065)
  ·
    refine ⟨31784492993631125164389049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42379323991508166885852065 31784492993631125164389049)
    ·
      refine ⟨23838369745223343873291787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31784492993631125164389049 23838369745223343873291787)
      ·
        refine ⟨35757554617835015809937681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23838369745223343873291787 35757554617835015809937681)
        ·
          refine ⟨26818165963376261857453261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35757554617835015809937681 26818165963376261857453261)
          ·
            refine ⟨10056812236266098196544973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26818165963376261857453261 10056812236266098196544973)
            ·
              refine ⟨3771304588599786823704365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10056812236266098196544973 3771304588599786823704365)
              ·
                refine ⟨1414239220724920058889137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3771304588599786823704365 1414239220724920058889137)
                ·
                  refine ⟨1060679415543690044166853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414239220724920058889137 1060679415543690044166853)
                  ·
                    refine ⟨198877390414441883281285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1060679415543690044166853 198877390414441883281285)
                    ·
                      rfl

theorem cell23_1161937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_1161937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161937 prefixEnd_1161937 := by exact prefixLift 1161937
  have htrace : WordTrace (prefixWord ++ tailWord_1161937) baseStart_1161937 baseEnd_1161937 := by
    simpa [prefixWord, tailWord_1161937, baseEnd_1161937] using wordTrace_append hprefix tailTrace_1161937
  have hstable : (prefixWord ++ tailWord_1161937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161937).length < 2 ^ (prefixWord ++ tailWord_1161937).sum := by decide
  have hdescent : baseEnd_1161937 < baseStart_1161937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161941 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1161941 : Nat := 118140960795 + 1161941 * 2 ^ 59
def prefixEnd_1161941 : Nat := 4983230072969 + 3 ^ 40 * 1161941 * 2
def baseEnd_1161941 : Nat := 198878075055314544731279

theorem tailTrace_1161941 : CollatzResearch.WordTrace tailWord_1161941 prefixEnd_1161941 198878075055314544731279 := by
  unfold tailWord_1161941
  simp only [CollatzResearch.WordTrace]
  refine ⟨42379469883493675568997677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28252979922329117045998451 42379469883493675568997677)
  ·
    refine ⟨15892301206310128338374129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42379469883493675568997677 15892301206310128338374129)
    ·
      refine ⟨11919225904732596253780597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15892301206310128338374129 11919225904732596253780597)
      ·
        refine ⟨1117427428568680898791931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11919225904732596253780597 1117427428568680898791931)
        ·
          refine ⟨1676141142853021348187897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117427428568680898791931 1676141142853021348187897)
          ·
            refine ⟨1257105857139766011140923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676141142853021348187897 1257105857139766011140923)
            ·
              refine ⟨1885658785709649016711385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257105857139766011140923 1885658785709649016711385)
              ·
                refine ⟨1414244089282236762533539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885658785709649016711385 1414244089282236762533539)
                ·
                  refine ⟨2121366133923355143800309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414244089282236762533539 2121366133923355143800309)
                  ·
                    refine ⟨198878075055314544731279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2121366133923355143800309 198878075055314544731279)
                    ·
                      rfl

theorem cell23_1161941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1161941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161941 prefixEnd_1161941 := by exact prefixLift 1161941
  have htrace : WordTrace (prefixWord ++ tailWord_1161941) baseStart_1161941 baseEnd_1161941 := by
    simpa [prefixWord, tailWord_1161941, baseEnd_1161941] using wordTrace_append hprefix tailTrace_1161941
  have hstable : (prefixWord ++ tailWord_1161941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161941).length < 2 ^ (prefixWord ++ tailWord_1161941).sum := by decide
  have hdescent : baseEnd_1161941 < baseStart_1161941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161944 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1161944 : Nat := 118140960795 + 1161944 * 2 ^ 59
def prefixEnd_1161944 : Nat := 4983230072969 + 3 ^ 40 * 1161944 * 2
def baseEnd_1161944 : Nat := 596635765607907122456323

theorem tailTrace_1161944 : CollatzResearch.WordTrace tailWord_1161944 prefixEnd_1161944 596635765607907122456323 := by
  unfold tailWord_1161944
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189789651241403540678443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28253052868321871387571257 21189789651241403540678443)
  ·
    refine ⟨31784684476862105311017665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21189789651241403540678443 31784684476862105311017665)
    ·
      refine ⟨23838513357646578983263249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31784684476862105311017665 23838513357646578983263249)
      ·
        refine ⟨17878885018234934237447437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23838513357646578983263249 17878885018234934237447437)
        ·
          refine ⟨6704581881838100339042789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17878885018234934237447437 6704581881838100339042789)
          ·
            refine ⟨1257109102844643813570523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6704581881838100339042789 1257109102844643813570523)
            ·
              refine ⟨1885663654266965720355785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257109102844643813570523 1885663654266965720355785)
              ·
                refine ⟨1414247740700224290266839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885663654266965720355785 1414247740700224290266839)
                ·
                  refine ⟨2121371611050336435400259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414247740700224290266839 2121371611050336435400259)
                  ·
                    refine ⟨3182057416575504653100389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121371611050336435400259 3182057416575504653100389)
                    ·
                      refine ⟨596635765607907122456323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3182057416575504653100389 596635765607907122456323)
                      ·
                        rfl

theorem cell23_1161944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1161944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161944 prefixEnd_1161944 := by exact prefixLift 1161944
  have htrace : WordTrace (prefixWord ++ tailWord_1161944) baseStart_1161944 baseEnd_1161944 := by
    simpa [prefixWord, tailWord_1161944, baseEnd_1161944] using wordTrace_append hprefix tailTrace_1161944
  have hstable : (prefixWord ++ tailWord_1161944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161944).length < 2 ^ (prefixWord ++ tailWord_1161944).sum := by decide
  have hdescent : baseEnd_1161944 < baseStart_1161944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161957 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1161957 : Nat := 118140960795 + 1161957 * 2 ^ 59
def prefixEnd_1161957 : Nat := 4983230072969 + 3 ^ 40 * 1161957 * 2
def baseEnd_1161957 : Nat := 596642440856415571593763

theorem tailTrace_1161957 : CollatzResearch.WordTrace tailWord_1161957 prefixEnd_1161957 596642440856415571593763 := by
  unfold tailWord_1161957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42380053451435710301580125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28253368967623806867720083 42380053451435710301580125)
  ·
    refine ⟨15892520044288391363092547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42380053451435710301580125 15892520044288391363092547)
    ·
      refine ⟨23838780066432587044638821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15892520044288391363092547 23838780066432587044638821)
      ·
        refine ⟨4469771262456110070869779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23838780066432587044638821 4469771262456110070869779)
        ·
          refine ⟨6704656893684165106304669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469771262456110070869779 6704656893684165106304669)
          ·
            refine ⟨2514246335131561914864251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6704656893684165106304669 2514246335131561914864251)
            ·
              refine ⟨3771369502697342872296377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514246335131561914864251 3771369502697342872296377)
              ·
                refine ⟨2828527127023007154222283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771369502697342872296377 2828527127023007154222283)
                ·
                  refine ⟨4242790690534510731333425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828527127023007154222283 4242790690534510731333425)
                  ·
                    refine ⟨3182093017900883048500069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4242790690534510731333425 3182093017900883048500069)
                    ·
                      refine ⟨596642440856415571593763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3182093017900883048500069 596642440856415571593763)
                      ·
                        rfl

theorem cell23_1161957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1161957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161957 prefixEnd_1161957 := by exact prefixLift 1161957
  have htrace : WordTrace (prefixWord ++ tailWord_1161957) baseStart_1161957 baseEnd_1161957 := by
    simpa [prefixWord, tailWord_1161957, baseEnd_1161957] using wordTrace_append hprefix tailTrace_1161957
  have hstable : (prefixWord ++ tailWord_1161957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161957).length < 2 ^ (prefixWord ++ tailWord_1161957).sum := by decide
  have hdescent : baseEnd_1161957 < baseStart_1161957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161977 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 3]
def baseStart_1161977 : Nat := 118140960795 + 1161977 * 2 ^ 59
def prefixEnd_1161977 : Nat := 4983230072969 + 3 ^ 40 * 1161977 * 2
def baseEnd_1161977 : Nat := 596652710469505493343671

theorem tailTrace_1161977 : CollatzResearch.WordTrace tailWord_1161977 prefixEnd_1161977 596652710469505493343671 := by
  unfold tailWord_1161977
  simp only [CollatzResearch.WordTrace]
  refine ⟨42380782911363253717308185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28253855274242169144872123 42380782911363253717308185)
  ·
    refine ⟨31785587183522440287981139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42380782911363253717308185 31785587183522440287981139)
    ·
      refine ⟨47678380775283660431971709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31785587183522440287981139 47678380775283660431971709)
      ·
        refine ⟨17879392790731372661989391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47678380775283660431971709 17879392790731372661989391)
        ·
          refine ⟨26819089186097058992984087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17879392790731372661989391 26819089186097058992984087)
          ·
            refine ⟨40228633779145588489476131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26819089186097058992984087 40228633779145588489476131)
            ·
              refine ⟨60342950668718382734214197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40228633779145588489476131 60342950668718382734214197)
              ·
                refine ⟨5657151625192348381332581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60342950668718382734214197 5657151625192348381332581)
                ·
                  refine ⟨1060715929723565321499859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5657151625192348381332581 1060715929723565321499859)
                  ·
                    refine ⟨1591073894585347982249789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1060715929723565321499859 1591073894585347982249789)
                    ·
                      refine ⟨596652710469505493343671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591073894585347982249789 596652710469505493343671)
                      ·
                        rfl

theorem cell23_1161977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_1161977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161977 prefixEnd_1161977 := by exact prefixLift 1161977
  have htrace : WordTrace (prefixWord ++ tailWord_1161977) baseStart_1161977 baseEnd_1161977 := by
    simpa [prefixWord, tailWord_1161977, baseEnd_1161977] using wordTrace_append hprefix tailTrace_1161977
  have hstable : (prefixWord ++ tailWord_1161977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161977).length < 2 ^ (prefixWord ++ tailWord_1161977).sum := by decide
  have hdescent : baseEnd_1161977 < baseStart_1161977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161978 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2]
def baseStart_1161978 : Nat := 118140960795 + 1161978 * 2 ^ 59
def prefixEnd_1161978 : Nat := 4983230072969 + 3 ^ 40 * 1161978 * 2
def baseEnd_1161978 : Nat := 596653223950159989431167

theorem tailTrace_1161978 : CollatzResearch.WordTrace tailWord_1161978 prefixEnd_1161978 596653223950159989431167 := by
  unfold tailWord_1161978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595204846089907722023647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28253879589573087258729725 10595204846089907722023647)
  ·
    refine ⟨15892807269134861583035471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595204846089907722023647 15892807269134861583035471)
    ·
      refine ⟨23839210903702292374553207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15892807269134861583035471 23839210903702292374553207)
      ·
        refine ⟨35758816355553438561829811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23839210903702292374553207 35758816355553438561829811)
        ·
          refine ⟨53638224533330157842744717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35758816355553438561829811 53638224533330157842744717)
          ·
            refine ⟨20114334199998809191029269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53638224533330157842744717 20114334199998809191029269)
            ·
              refine ⟨942859415624944180829497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20114334199998809191029269 942859415624944180829497)
              ·
                refine ⟨707144561718708135622123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942859415624944180829497 707144561718708135622123)
                ·
                  refine ⟨1060716842578062203433185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707144561718708135622123 1060716842578062203433185)
                  ·
                    refine ⟨795537631933546652574889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060716842578062203433185 795537631933546652574889)
                    ·
                      refine ⟨596653223950159989431167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795537631933546652574889 596653223950159989431167)
                      ·
                        rfl

theorem cell23_1161978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_1161978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161978 prefixEnd_1161978 := by exact prefixLift 1161978
  have htrace : WordTrace (prefixWord ++ tailWord_1161978) baseStart_1161978 baseEnd_1161978 := by
    simpa [prefixWord, tailWord_1161978, baseEnd_1161978] using wordTrace_append hprefix tailTrace_1161978
  have hstable : (prefixWord ++ tailWord_1161978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161978).length < 2 ^ (prefixWord ++ tailWord_1161978).sum := by decide
  have hdescent : baseEnd_1161978 < baseStart_1161978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161980 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1161980 : Nat := 118140960795 + 1161980 * 2 ^ 59
def prefixEnd_1161980 : Nat := 4983230072969 + 3 ^ 40 * 1161980 * 2
def baseEnd_1161980 : Nat := 198884750303822993868719

theorem tailTrace_1161980 : CollatzResearch.WordTrace tailWord_1161980 prefixEnd_1161980 198884750303822993868719 := by
  unfold tailWord_1161980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21190446165176192614833697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28253928220234923486444929 21190446165176192614833697)
  ·
    refine ⟨15892834623882144461125273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21190446165176192614833697 15892834623882144461125273)
    ·
      refine ⟨11919625967911608345843955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15892834623882144461125273 11919625967911608345843955)
      ·
        refine ⟨17879438951867412518765933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11919625967911608345843955 17879438951867412518765933)
        ·
          refine ⟨6704789606950279694537225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17879438951867412518765933 6704789606950279694537225)
          ·
            refine ⟨5028592205212709770902919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6704789606950279694537225 5028592205212709770902919)
            ·
              refine ⟨7542888307819064656354379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028592205212709770902919 7542888307819064656354379)
              ·
                refine ⟨11314332461728596984531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542888307819064656354379 11314332461728596984531569)
                ·
                  refine ⟨8485749346296447738398677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11314332461728596984531569 8485749346296447738398677)
                  ·
                    refine ⟨198884750303822993868719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8485749346296447738398677 198884750303822993868719)
                    ·
                      rfl

theorem cell23_1161980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1161980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161980 prefixEnd_1161980 := by exact prefixLift 1161980
  have htrace : WordTrace (prefixWord ++ tailWord_1161980) baseStart_1161980 baseEnd_1161980 := by
    simpa [prefixWord, tailWord_1161980, baseEnd_1161980] using wordTrace_append hprefix tailTrace_1161980
  have hstable : (prefixWord ++ tailWord_1161980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161980).length < 2 ^ (prefixWord ++ tailWord_1161980).sum := by decide
  have hdescent : baseEnd_1161980 < baseStart_1161980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161994 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1161994 : Nat := 118140960795 + 1161994 * 2 ^ 59
def prefixEnd_1161994 : Nat := 4983230072969 + 3 ^ 40 * 1161994 * 2
def baseEnd_1161994 : Nat := 596661439640631926831093

theorem tailTrace_1161994 : CollatzResearch.WordTrace tailWord_1161994 prefixEnd_1161994 596661439640631926831093 := by
  unfold tailWord_1161994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595350738075416405169259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28254268634867777080451357 10595350738075416405169259)
  ·
    refine ⟨15893026107113124607753889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595350738075416405169259 15893026107113124607753889)
    ·
      refine ⟨11919769580334843455815417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15893026107113124607753889 11919769580334843455815417)
      ·
        refine ⟨8939827185251132591861563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11919769580334843455815417 8939827185251132591861563)
        ·
          refine ⟨13409740777876698887792345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939827185251132591861563 13409740777876698887792345)
          ·
            refine ⟨10057305583407524165844259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13409740777876698887792345 10057305583407524165844259)
            ·
              refine ⟨15085958375111286248766389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10057305583407524165844259 15085958375111286248766389)
              ·
                refine ⟨1414308597666683085821849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15085958375111286248766389 1414308597666683085821849)
                ·
                  refine ⟨1060731448250012314366387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414308597666683085821849 1060731448250012314366387)
                  ·
                    refine ⟨1591097172375018471549581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1060731448250012314366387 1591097172375018471549581)
                    ·
                      refine ⟨596661439640631926831093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591097172375018471549581 596661439640631926831093)
                      ·
                        rfl

theorem cell23_1161994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1161994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1161994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1161994 prefixEnd_1161994 := by exact prefixLift 1161994
  have htrace : WordTrace (prefixWord ++ tailWord_1161994) baseStart_1161994 baseEnd_1161994 := by
    simpa [prefixWord, tailWord_1161994, baseEnd_1161994] using wordTrace_append hprefix tailTrace_1161994
  have hstable : (prefixWord ++ tailWord_1161994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161994).length < 2 ^ (prefixWord ++ tailWord_1161994).sum := by decide
  have hdescent : baseEnd_1161994 < baseStart_1161994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162010 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_1162010 : Nat := 118140960795 + 1162010 * 2 ^ 59
def prefixEnd_1162010 : Nat := 4983230072969 + 3 ^ 40 * 1162010 * 2
def baseEnd_1162010 : Nat := 198889885110367954743673

theorem tailTrace_1162010 : CollatzResearch.WordTrace tailWord_1162010 prefixEnd_1162010 198889885110367954743673 := by
  unfold tailWord_1162010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595496630060925088314871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28254657680162466902172989 10595496630060925088314871)
  ·
    refine ⟨15893244945091387632472307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595496630060925088314871 15893244945091387632472307)
    ·
      refine ⟨23839867417637081448708461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15893244945091387632472307 23839867417637081448708461)
      ·
        refine ⟨8939950281613905543265673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23839867417637081448708461 8939950281613905543265673)
        ·
          refine ⟨6704962711210429157449255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8939950281613905543265673 6704962711210429157449255)
          ·
            refine ⟨10057444066815643736173883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6704962711210429157449255 10057444066815643736173883)
            ·
              refine ⟨15086166100223465604260825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10057444066815643736173883 15086166100223465604260825)
              ·
                refine ⟨11314624575167599203195619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15086166100223465604260825 11314624575167599203195619)
                ·
                  refine ⟨16971936862751398804793429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11314624575167599203195619 16971936862751398804793429)
                  ·
                    refine ⟨198889885110367954743673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16971936862751398804793429 198889885110367954743673)
                    ·
                      rfl

theorem cell23_1162010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_1162010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162010 prefixEnd_1162010 := by exact prefixLift 1162010
  have htrace : WordTrace (prefixWord ++ tailWord_1162010) baseStart_1162010 baseEnd_1162010 := by
    simpa [prefixWord, tailWord_1162010, baseEnd_1162010] using wordTrace_append hprefix tailTrace_1162010
  have hstable : (prefixWord ++ tailWord_1162010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162010).length < 2 ^ (prefixWord ++ tailWord_1162010).sum := by decide
  have hdescent : baseEnd_1162010 < baseStart_1162010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162047 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_1162047 : Nat := 118140960795 + 1162047 * 2 ^ 59
def prefixEnd_1162047 : Nat := 4983230072969 + 3 ^ 40 * 1162047 * 2
def baseEnd_1162047 : Nat := 596688654115320219468349

theorem tailTrace_1162047 : CollatzResearch.WordTrace tailWord_1162047 prefixEnd_1162047 596688654115320219468349 := by
  unfold tailWord_1162047
  simp only [CollatzResearch.WordTrace]
  refine ⟨42383336021109655672356395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28255557347406437114904263 42383336021109655672356395)
  ·
    refine ⟨63575004031664483508534593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42383336021109655672356395 63575004031664483508534593)
    ·
      refine ⟨47681253023748362631400945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63575004031664483508534593 47681253023748362631400945)
      ·
        refine ⟨35760939767811271973550709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47681253023748362631400945 35760939767811271973550709)
        ·
          refine ⟨3352588103232306747520379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35760939767811271973550709 3352588103232306747520379)
          ·
            refine ⟨5028882154848460121280569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352588103232306747520379 5028882154848460121280569)
            ·
              refine ⟨3771661616136345090960427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5028882154848460121280569 3771661616136345090960427)
              ·
                refine ⟨5657492424204517636440641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771661616136345090960427 5657492424204517636440641)
                ·
                  refine ⟨4243119318153388227330481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5657492424204517636440641 4243119318153388227330481)
                  ·
                    refine ⟨3182339488615041170497861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4243119318153388227330481 3182339488615041170497861)
                    ·
                      refine ⟨596688654115320219468349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3182339488615041170497861 596688654115320219468349)
                      ·
                        rfl

theorem cell23_1162047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_1162047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162047 prefixEnd_1162047 := by exact prefixLift 1162047
  have htrace : WordTrace (prefixWord ++ tailWord_1162047) baseStart_1162047 baseEnd_1162047 := by
    simpa [prefixWord, tailWord_1162047, baseEnd_1162047] using wordTrace_append hprefix tailTrace_1162047
  have hstable : (prefixWord ++ tailWord_1162047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162047).length < 2 ^ (prefixWord ++ tailWord_1162047).sum := by decide
  have hdescent : baseEnd_1162047 < baseStart_1162047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162074 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_1162074 : Nat := 118140960795 + 1162074 * 2 ^ 59
def prefixEnd_1162074 : Nat := 4983230072969 + 3 ^ 40 * 1162074 * 2
def baseEnd_1162074 : Nat := 66300279788110179314525

theorem tailTrace_1162074 : CollatzResearch.WordTrace tailWord_1162074 prefixEnd_1162074 66300279788110179314525 := by
  unfold tailWord_1162074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596080198002959820897319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28256213861341226189059517 10596080198002959820897319)
  ·
    refine ⟨15894120297004439731345979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10596080198002959820897319 15894120297004439731345979)
    ·
      refine ⟨23841180445506659597018969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15894120297004439731345979 23841180445506659597018969)
      ·
        refine ⟨17880885334129994697764227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23841180445506659597018969 17880885334129994697764227)
        ·
          refine ⟨26821328001194992046646341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17880885334129994697764227 26821328001194992046646341)
          ·
            refine ⟨5028999000224061008746189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26821328001194992046646341 5028999000224061008746189)
            ·
              refine ⟨1885874625084022878279821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5028999000224061008746189 1885874625084022878279821)
              ·
                refine ⟨707202984406508579354933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1885874625084022878279821 707202984406508579354933)
                ·
                  refine ⟨66300279788110179314525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 707202984406508579354933 66300279788110179314525)
                  ·
                    rfl

theorem cell23_1162074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_1162074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162074 prefixEnd_1162074 := by exact prefixLift 1162074
  have htrace : WordTrace (prefixWord ++ tailWord_1162074) baseStart_1162074 baseEnd_1162074 := by
    simpa [prefixWord, tailWord_1162074, baseEnd_1162074] using wordTrace_append hprefix tailTrace_1162074
  have hstable : (prefixWord ++ tailWord_1162074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162074).length < 2 ^ (prefixWord ++ tailWord_1162074).sum := by decide
  have hdescent : baseEnd_1162074 < baseStart_1162074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162087 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1162087 : Nat := 118140960795 + 1162087 * 2 ^ 59
def prefixEnd_1162087 : Nat := 4983230072969 + 3 ^ 40 * 1162087 * 2
def baseEnd_1162087 : Nat := 198903064447166687656055

theorem tailTrace_1162087 : CollatzResearch.WordTrace tailWord_1162087 prefixEnd_1162087 198903064447166687656055 := by
  unfold tailWord_1162087
  simp only [CollatzResearch.WordTrace]
  refine ⟨42384794940964742503812515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28256529960643161669208343 42384794940964742503812515)
  ·
    refine ⟨63577192411447113755718773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42384794940964742503812515 63577192411447113755718773)
    ·
      refine ⟨5960361788573166914598635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63577192411447113755718773 5960361788573166914598635)
      ·
        refine ⟨8940542682859750371897953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5960361788573166914598635 8940542682859750371897953)
        ·
          refine ⟨6705407012144812778923465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8940542682859750371897953 6705407012144812778923465)
          ·
            refine ⟨5029055259108609584192599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6705407012144812778923465 5029055259108609584192599)
            ·
              refine ⟨7543582888662914376288899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029055259108609584192599 7543582888662914376288899)
              ·
                refine ⟨11315374332994371564433349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543582888662914376288899 11315374332994371564433349)
                ·
                  refine ⟨2121632687436444668331253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11315374332994371564433349 2121632687436444668331253)
                  ·
                    refine ⟨198903064447166687656055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2121632687436444668331253 198903064447166687656055)
                    ·
                      rfl

theorem cell23_1162087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1162087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162087 prefixEnd_1162087 := by exact prefixLift 1162087
  have htrace : WordTrace (prefixWord ++ tailWord_1162087) baseStart_1162087 baseEnd_1162087 := by
    simpa [prefixWord, tailWord_1162087, baseEnd_1162087] using wordTrace_append hprefix tailTrace_1162087
  have hstable : (prefixWord ++ tailWord_1162087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162087).length < 2 ^ (prefixWord ++ tailWord_1162087).sum := by decide
  have hdescent : baseEnd_1162087 < baseStart_1162087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162097 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_1162097 : Nat := 118140960795 + 1162097 * 2 ^ 59
def prefixEnd_1162097 : Nat := 4983230072969 + 3 ^ 40 * 1162097 * 2
def baseEnd_1162097 : Nat := 596714328148045023843119

theorem tailTrace_1162097 : CollatzResearch.WordTrace tailWord_1162097 prefixEnd_1162097 596714328148045023843119 := by
  unfold tailWord_1162097
  simp only [CollatzResearch.WordTrace]
  refine ⟨42385159670928514211676545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28256773113952342807784363 42385159670928514211676545)
  ·
    refine ⟨31788869753196385658757409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42385159670928514211676545 31788869753196385658757409)
    ·
      refine ⟨23841652314897289244068057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31788869753196385658757409 23841652314897289244068057)
      ·
        refine ⟨17881239236172966933051043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23841652314897289244068057 17881239236172966933051043)
        ·
          refine ⟨26821858854259450399576565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17881239236172966933051043 26821858854259450399576565)
          ·
            refine ⟨2514549267586823474960303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26821858854259450399576565 2514549267586823474960303)
            ·
              refine ⟨3771823901380235212440455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514549267586823474960303 3771823901380235212440455)
              ·
                refine ⟨5657735852070352818660683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771823901380235212440455 5657735852070352818660683)
                ·
                  refine ⟨8486603778105529227991025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657735852070352818660683 8486603778105529227991025)
                  ·
                    refine ⟨6364952833579146920993269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8486603778105529227991025 6364952833579146920993269)
                    ·
                      refine ⟨596714328148045023843119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6364952833579146920993269 596714328148045023843119)
                      ·
                        rfl

theorem cell23_1162097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_1162097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162097 prefixEnd_1162097 := by exact prefixLift 1162097
  have htrace : WordTrace (prefixWord ++ tailWord_1162097) baseStart_1162097 baseEnd_1162097 := by
    simpa [prefixWord, tailWord_1162097, baseEnd_1162097] using wordTrace_append hprefix tailTrace_1162097
  have hstable : (prefixWord ++ tailWord_1162097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162097).length < 2 ^ (prefixWord ++ tailWord_1162097).sum := by decide
  have hdescent : baseEnd_1162097 < baseStart_1162097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162102 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1162102 : Nat := 118140960795 + 1162102 * 2 ^ 59
def prefixEnd_1162102 : Nat := 4983230072969 + 3 ^ 40 * 1162102 * 2
def baseEnd_1162102 : Nat := 596716895551317504280597

theorem tailTrace_1162102 : CollatzResearch.WordTrace tailWord_1162102 prefixEnd_1162102 596716895551317504280597 := by
  unfold tailWord_1162102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649083877244400004100535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28256894690606933377072373 2649083877244400004100535)
  ·
    refine ⟨3973625815866600006150803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2649083877244400004100535 3973625815866600006150803)
    ·
      refine ⟨5960438723799900009226205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973625815866600006150803 5960438723799900009226205)
      ·
        refine ⟨2235164521424962503459827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5960438723799900009226205 2235164521424962503459827)
        ·
          refine ⟨3352746782137443755189741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235164521424962503459827 3352746782137443755189741)
          ·
            refine ⟨1257280043301541408196153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3352746782137443755189741 1257280043301541408196153)
            ·
              refine ⟨942960032476156056147115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257280043301541408196153 942960032476156056147115)
              ·
                refine ⟨1414440048714234084220673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942960032476156056147115 1414440048714234084220673)
                ·
                  refine ⟨1060830036535675563165505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414440048714234084220673 1060830036535675563165505)
                  ·
                    refine ⟨795622527401756672374129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060830036535675563165505 795622527401756672374129)
                    ·
                      refine ⟨596716895551317504280597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795622527401756672374129 596716895551317504280597)
                      ·
                        rfl

theorem cell23_1162102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1162102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162102 prefixEnd_1162102 := by exact prefixLift 1162102
  have htrace : WordTrace (prefixWord ++ tailWord_1162102) baseStart_1162102 baseEnd_1162102 := by
    simpa [prefixWord, tailWord_1162102, baseEnd_1162102] using wordTrace_append hprefix tailTrace_1162102
  have hstable : (prefixWord ++ tailWord_1162102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162102).length < 2 ^ (prefixWord ++ tailWord_1162102).sum := by decide
  have hdescent : baseEnd_1162102 < baseStart_1162102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162144 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1162144 : Nat := 118140960795 + 1162144 * 2 ^ 59
def prefixEnd_1162144 : Nat := 4983230072969 + 3 ^ 40 * 1162144 * 2
def baseEnd_1162144 : Nat := 596738461738806339955403

theorem tailTrace_1162144 : CollatzResearch.WordTrace tailWord_1162144 prefixEnd_1162144 596738461738806339955403 := by
  unfold tailWord_1162144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193436950879120619318743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28257915934505494159091657 21193436950879120619318743)
  ·
    refine ⟨31790155426318680928978115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21193436950879120619318743 31790155426318680928978115)
    ·
      refine ⟨47685233139478021393467173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31790155426318680928978115 47685233139478021393467173)
      ·
        refine ⟨8940981213652129011275095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47685233139478021393467173 8940981213652129011275095)
        ·
          refine ⟨13411471820478193516912643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940981213652129011275095 13411471820478193516912643)
          ·
            refine ⟨20117207730717290275368965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13411471820478193516912643 20117207730717290275368965)
            ·
              refine ⟨3771976449509491926631681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20117207730717290275368965 3771976449509491926631681)
              ·
                refine ⟨2828982337132118944973761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771976449509491926631681 2828982337132118944973761)
                ·
                  refine ⟨2121736752849089208730321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828982337132118944973761 2121736752849089208730321)
                  ·
                    refine ⟨1591302564636816906547741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121736752849089208730321 1591302564636816906547741)
                    ·
                      refine ⟨596738461738806339955403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591302564636816906547741 596738461738806339955403)
                      ·
                        rfl

theorem cell23_1162144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1162144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162144 prefixEnd_1162144 := by exact prefixLift 1162144
  have htrace : WordTrace (prefixWord ++ tailWord_1162144) baseStart_1162144 baseEnd_1162144 := by
    simpa [prefixWord, tailWord_1162144, baseEnd_1162144] using wordTrace_append hprefix tailTrace_1162144
  have hstable : (prefixWord ++ tailWord_1162144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162144).length < 2 ^ (prefixWord ++ tailWord_1162144).sum := by decide
  have hdescent : baseEnd_1162144 < baseStart_1162144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162147 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 6]
def baseStart_1162147 : Nat := 118140960795 + 1162147 * 2 ^ 59
def prefixEnd_1162147 : Nat := 4983230072969 + 3 ^ 40 * 1162147 * 2
def baseEnd_1162147 : Nat := 66304444686752203135321

theorem tailTrace_1162147 : CollatzResearch.WordTrace tailWord_1162147 prefixEnd_1162147 66304444686752203135321 := by
  unfold tailWord_1162147
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386983320747372750996695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28257988880498248500664463 42386983320747372750996695)
  ·
    refine ⟨63580474981121059126495043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42386983320747372750996695 63580474981121059126495043)
    ·
      refine ⟨95370712471681588689742565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63580474981121059126495043 95370712471681588689742565)
      ·
        refine ⟨17882008588440297879326731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95370712471681588689742565 17882008588440297879326731)
        ·
          refine ⟨26823012882660446818990097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17882008588440297879326731 26823012882660446818990097)
          ·
            refine ⟨20117259661995335114242573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26823012882660446818990097 20117259661995335114242573)
            ·
              refine ⟨7543972373248250667840965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20117259661995335114242573 7543972373248250667840965)
              ·
                refine ⟨1414494819984047000220181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7543972373248250667840965 1414494819984047000220181)
                ·
                  refine ⟨66304444686752203135321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1414494819984047000220181 66304444686752203135321)
                  ·
                    rfl

theorem cell23_1162147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 6].length) (baseStart_1162147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162147 prefixEnd_1162147 := by exact prefixLift 1162147
  have htrace : WordTrace (prefixWord ++ tailWord_1162147) baseStart_1162147 baseEnd_1162147 := by
    simpa [prefixWord, tailWord_1162147, baseEnd_1162147] using wordTrace_append hprefix tailTrace_1162147
  have hstable : (prefixWord ++ tailWord_1162147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162147).length < 2 ^ (prefixWord ++ tailWord_1162147).sum := by decide
  have hdescent : baseEnd_1162147 < baseStart_1162147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162198 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1162198 : Nat := 118140960795 + 1162198 * 2 ^ 59
def prefixEnd_1162198 : Nat := 4983230072969 + 3 ^ 40 * 1162198 * 2
def baseEnd_1162198 : Nat := 66307354410461014297795

theorem tailTrace_1162198 : CollatzResearch.WordTrace tailWord_1162198 prefixEnd_1162198 66307354410461014297795 := by
  unfold tailWord_1162198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649302715222663028818953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28259228962375072307402165 2649302715222663028818953)
  ·
    refine ⟨1986977036416997271614215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2649302715222663028818953 1986977036416997271614215)
    ·
      refine ⟨2980465554625495907421323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986977036416997271614215 2980465554625495907421323)
      ·
        refine ⟨4470698331938243861131985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980465554625495907421323 4470698331938243861131985)
        ·
          refine ⟨3353023748953682895848989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4470698331938243861131985 3353023748953682895848989)
          ·
            refine ⟨1257383905857631085943371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3353023748953682895848989 1257383905857631085943371)
            ·
              refine ⟨1886075858786446628915057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257383905857631085943371 1886075858786446628915057)
              ·
                refine ⟨1414556894089834971686293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886075858786446628915057 1414556894089834971686293)
                ·
                  refine ⟨66307354410461014297795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1414556894089834971686293 66307354410461014297795)
                  ·
                    rfl

theorem cell23_1162198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1162198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162198 prefixEnd_1162198 := by exact prefixLift 1162198
  have htrace : WordTrace (prefixWord ++ tailWord_1162198) baseStart_1162198 baseEnd_1162198 := by
    simpa [prefixWord, tailWord_1162198, baseEnd_1162198] using wordTrace_append hprefix tailTrace_1162198
  have hstable : (prefixWord ++ tailWord_1162198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162198).length < 2 ^ (prefixWord ++ tailWord_1162198).sum := by decide
  have hdescent : baseEnd_1162198 < baseStart_1162198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162234 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_1162234 : Nat := 118140960795 + 1162234 * 2 ^ 59
def prefixEnd_1162234 : Nat := 4983230072969 + 3 ^ 40 * 1162234 * 2
def baseEnd_1162234 : Nat := 596784674997710987829989

theorem tailTrace_1162234 : CollatzResearch.WordTrace tailWord_1162234 prefixEnd_1162234 596784674997710987829989 := by
  unfold tailWord_1162234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10597539117858046652353439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28260104314288124406275837 10597539117858046652353439)
  ·
    refine ⟨15896308676787069978530159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10597539117858046652353439 15896308676787069978530159)
    ·
      refine ⟨23844463015180604967795239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15896308676787069978530159 23844463015180604967795239)
      ·
        refine ⟨35766694522770907451692859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23844463015180604967795239 35766694522770907451692859)
        ·
          refine ⟨53650041784156361177539289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35766694522770907451692859 53650041784156361177539289)
          ·
            refine ⟨40237531338117270883154467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53650041784156361177539289 40237531338117270883154467)
            ·
              refine ⟨60356297007175906324731701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40237531338117270883154467 60356297007175906324731701)
              ·
                refine ⟨5658402844422741217943597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60356297007175906324731701 5658402844422741217943597)
                ·
                  refine ⟨2121901066658527956728849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5658402844422741217943597 2121901066658527956728849)
                  ·
                    refine ⟨1591425799993895967546637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121901066658527956728849 1591425799993895967546637)
                    ·
                      refine ⟨596784674997710987829989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591425799993895967546637 596784674997710987829989)
                      ·
                        rfl

theorem cell23_1162234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_1162234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162234 prefixEnd_1162234 := by exact prefixLift 1162234
  have htrace : WordTrace (prefixWord ++ tailWord_1162234) baseStart_1162234 baseEnd_1162234 := by
    simpa [prefixWord, tailWord_1162234, baseEnd_1162234] using wordTrace_append hprefix tailTrace_1162234
  have hstable : (prefixWord ++ tailWord_1162234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162234).length < 2 ^ (prefixWord ++ tailWord_1162234).sum := by decide
  have hdescent : baseEnd_1162234 < baseStart_1162234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162251 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 3]
def baseStart_1162251 : Nat := 118140960795 + 1162251 * 2 ^ 59
def prefixEnd_1162251 : Nat := 4983230072969 + 3 ^ 40 * 1162251 * 2
def baseEnd_1162251 : Nat := 596793404168837421317411

theorem tailTrace_1162251 : CollatzResearch.WordTrace tailWord_1162251 prefixEnd_1162251 596793404168837421317411 := by
  unfold tailWord_1162251
  simp only [CollatzResearch.WordTrace]
  refine ⟨42390776512370598512782607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28260517674913732341855071 42390776512370598512782607)
  ·
    refine ⟨63586164768555897769173911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42390776512370598512782607 63586164768555897769173911)
    ·
      refine ⟨95379247152833846653760867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63586164768555897769173911 95379247152833846653760867)
      ·
        refine ⟨143068870729250769980641301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95379247152833846653760867 143068870729250769980641301)
        ·
          refine ⟨6706353315433629842842561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143068870729250769980641301 6706353315433629842842561)
          ·
            refine ⟨5029764986575222382131921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6706353315433629842842561 5029764986575222382131921)
            ·
              refine ⟨3772323739931416786598941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029764986575222382131921 3772323739931416786598941)
              ·
                refine ⟨1414621402474281294974603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3772323739931416786598941 1414621402474281294974603)
                ·
                  refine ⟨2121932103711421942461905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414621402474281294974603 2121932103711421942461905)
                  ·
                    refine ⟨1591449077783566456846429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121932103711421942461905 1591449077783566456846429)
                    ·
                      refine ⟨596793404168837421317411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591449077783566456846429 596793404168837421317411)
                      ·
                        rfl

theorem cell23_1162251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 3].length) (baseStart_1162251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162251 prefixEnd_1162251 := by exact prefixLift 1162251
  have htrace : WordTrace (prefixWord ++ tailWord_1162251) baseStart_1162251 baseEnd_1162251 := by
    simpa [prefixWord, tailWord_1162251, baseEnd_1162251] using wordTrace_append hprefix tailTrace_1162251
  have hstable : (prefixWord ++ tailWord_1162251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162251).length < 2 ^ (prefixWord ++ tailWord_1162251).sum := by decide
  have hdescent : baseEnd_1162251 < baseStart_1162251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162254 : List Nat := [4, 1, 1, 2, 2, 4, 9]
def baseStart_1162254 : Nat := 118140960795 + 1162254 * 2 ^ 59
def prefixEnd_1162254 : Nat := 4983230072969 + 3 ^ 40 * 1162254 * 2
def baseEnd_1162254 : Nat := 7367838822355566784937

theorem tailTrace_1162254 : CollatzResearch.WordTrace tailWord_1162254 prefixEnd_1162254 7367838822355566784937 := by
  unfold tailWord_1162254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298860741419966253142727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28260590620906486683427877 5298860741419966253142727)
  ·
    refine ⟨7948291112129949379714091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298860741419966253142727 7948291112129949379714091)
    ·
      refine ⟨11922436668194924069571137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7948291112129949379714091 11922436668194924069571137)
      ·
        refine ⟨8941827501146193052178353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11922436668194924069571137 8941827501146193052178353)
        ·
          refine ⟨6706370625859644789133765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8941827501146193052178353 6706370625859644789133765)
          ·
            refine ⟨1257444492348683397962581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6706370625859644789133765 1257444492348683397962581)
            ·
              refine ⟨7367838822355566784937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1257444492348683397962581 7367838822355566784937)
              ·
                rfl

theorem cell23_1162254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 9].length) (baseStart_1162254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162254 prefixEnd_1162254 := by exact prefixLift 1162254
  have htrace : WordTrace (prefixWord ++ tailWord_1162254) baseStart_1162254 baseEnd_1162254 := by
    simpa [prefixWord, tailWord_1162254, baseEnd_1162254] using wordTrace_append hprefix tailTrace_1162254
  have hstable : (prefixWord ++ tailWord_1162254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162254).length < 2 ^ (prefixWord ++ tailWord_1162254).sum := by decide
  have hdescent : baseEnd_1162254 < baseStart_1162254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162324 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1162324 : Nat := 118140960795 + 1162324 * 2 ^ 59
def prefixEnd_1162324 : Nat := 4983230072969 + 3 ^ 40 * 1162324 * 2
def baseEnd_1162324 : Nat := 596830888256615635704575

theorem tailTrace_1162324 : CollatzResearch.WordTrace tailWord_1162324 prefixEnd_1162324 596830888256615635704575 := by
  unfold tailWord_1162324
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196719520553065990095013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28262292694070754653460017 21196719520553065990095013)
  ·
    refine ⟨3974384910103699873142815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21196719520553065990095013 3974384910103699873142815)
    ·
      refine ⟨5961577365155549809714223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974384910103699873142815 5961577365155549809714223)
      ·
        refine ⟨8942366047733324714571335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5961577365155549809714223 8942366047733324714571335)
        ·
          refine ⟨13413549071599987071857003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8942366047733324714571335 13413549071599987071857003)
          ·
            refine ⟨20120323607399980607785505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13413549071599987071857003 20120323607399980607785505)
            ·
              refine ⟨15090242705549985455839129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20120323607399980607785505 15090242705549985455839129)
              ·
                refine ⟨11317682029162489091879347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15090242705549985455839129 11317682029162489091879347)
                ·
                  refine ⟨16976523043743733637819021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11317682029162489091879347 16976523043743733637819021)
                  ·
                    refine ⟨6366196141403900114182133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16976523043743733637819021 6366196141403900114182133)
                    ·
                      refine ⟨596830888256615635704575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6366196141403900114182133 596830888256615635704575)
                      ·
                        rfl

theorem cell23_1162324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1162324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162324 prefixEnd_1162324 := by exact prefixLift 1162324
  have htrace : WordTrace (prefixWord ++ tailWord_1162324) baseStart_1162324 baseEnd_1162324 := by
    simpa [prefixWord, tailWord_1162324, baseEnd_1162324] using wordTrace_append hprefix tailTrace_1162324
  have hstable : (prefixWord ++ tailWord_1162324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162324).length < 2 ^ (prefixWord ++ tailWord_1162324).sum := by decide
  have hdescent : baseEnd_1162324 < baseStart_1162324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162366 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1162366 : Nat := 118140960795 + 1162366 * 2 ^ 59
def prefixEnd_1162366 : Nat := 4983230072969 + 3 ^ 40 * 1162366 * 2
def baseEnd_1162366 : Nat := 596852454444104471379383

theorem tailTrace_1162366 : CollatzResearch.WordTrace tailWord_1162366 prefixEnd_1162366 596852454444104471379383 := by
  unfold tailWord_1162366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299371363369246644152369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28263313937969315435479301 5299371363369246644152369)
  ·
    refine ⟨3974528522526934983114277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299371363369246644152369 3974528522526934983114277)
    ·
      refine ⟨745224097973800309333927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3974528522526934983114277 745224097973800309333927)
      ·
        refine ⟨1117836146960700464000891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745224097973800309333927 1117836146960700464000891)
        ·
          refine ⟨1676754220441050696001337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117836146960700464000891 1676754220441050696001337)
          ·
            refine ⟨1257565665330788022001003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676754220441050696001337 1257565665330788022001003)
            ·
              refine ⟨1886348497996182033001505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257565665330788022001003 1886348497996182033001505)
              ·
                refine ⟨1414761373497136524751129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886348497996182033001505 1414761373497136524751129)
                ·
                  refine ⟨1061071030122852393563347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414761373497136524751129 1061071030122852393563347)
                  ·
                    refine ⟨1591606545184278590345021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061071030122852393563347 1591606545184278590345021)
                    ·
                      refine ⟨596852454444104471379383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591606545184278590345021 596852454444104471379383)
                      ·
                        rfl

theorem cell23_1162366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1162366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162366 prefixEnd_1162366 := by exact prefixLift 1162366
  have htrace : WordTrace (prefixWord ++ tailWord_1162366) baseStart_1162366 baseEnd_1162366 := by
    simpa [prefixWord, tailWord_1162366, baseEnd_1162366] using wordTrace_append hprefix tailTrace_1162366
  have hstable : (prefixWord ++ tailWord_1162366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162366).length < 2 ^ (prefixWord ++ tailWord_1162366).sum := by decide
  have hdescent : baseEnd_1162366 < baseStart_1162366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162372 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_1162372 : Nat := 118140960795 + 1162372 * 2 ^ 59
def prefixEnd_1162372 : Nat := 4983230072969 + 3 ^ 40 * 1162372 * 2
def baseEnd_1162372 : Nat := 596855535328031447904355

theorem tailTrace_1162372 : CollatzResearch.WordTrace tailWord_1162372 prefixEnd_1162372 596855535328031447904355 := by
  unfold tailWord_1162372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21197594872466118088968685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28263459829954824118624913 21197594872466118088968685)
  ·
    refine ⟨7949098077174794283363257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21197594872466118088968685 7949098077174794283363257)
    ·
      refine ⟨5961823557881095712522443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7949098077174794283363257 5961823557881095712522443)
      ·
        refine ⟨8942735336821643568783665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5961823557881095712522443 8942735336821643568783665)
        ·
          refine ⟨6707051502616232676587749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8942735336821643568783665 6707051502616232676587749)
          ·
            refine ⟨1257572156740543626860203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6707051502616232676587749 1257572156740543626860203)
            ·
              refine ⟨1886358235110815440290305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257572156740543626860203 1886358235110815440290305)
              ·
                refine ⟨1414768676333111580217729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886358235110815440290305 1414768676333111580217729)
                ·
                  refine ⟨1061076507249833685163297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414768676333111580217729 1061076507249833685163297)
                  ·
                    refine ⟨795807380437375263872473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1061076507249833685163297 795807380437375263872473)
                    ·
                      refine ⟨596855535328031447904355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795807380437375263872473 596855535328031447904355)
                      ·
                        rfl

theorem cell23_1162372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_1162372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162372 prefixEnd_1162372 := by exact prefixLift 1162372
  have htrace : WordTrace (prefixWord ++ tailWord_1162372) baseStart_1162372 baseEnd_1162372 := by
    simpa [prefixWord, tailWord_1162372, baseEnd_1162372] using wordTrace_append hprefix tailTrace_1162372
  have hstable : (prefixWord ++ tailWord_1162372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162372).length < 2 ^ (prefixWord ++ tailWord_1162372).sum := by decide
  have hdescent : baseEnd_1162372 < baseStart_1162372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162424 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1162424 : Nat := 118140960795 + 1162424 * 2 ^ 59
def prefixEnd_1162424 : Nat := 4983230072969 + 3 ^ 40 * 1162424 * 2
def baseEnd_1162424 : Nat := 596882236322065244454115

theorem tailTrace_1162424 : CollatzResearch.WordTrace tailWord_1162424 prefixEnd_1162424 596882236322065244454115 := by
  unfold tailWord_1162424
  simp only [CollatzResearch.WordTrace]
  refine ⟨21198543170371924529415163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28264724227162566039220217 21198543170371924529415163)
  ·
    refine ⟨31797814755557886794122745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21198543170371924529415163 31797814755557886794122745)
    ·
      refine ⟨23848361066668415095592059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31797814755557886794122745 23848361066668415095592059)
      ·
        refine ⟨35772541600002622643388089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23848361066668415095592059 35772541600002622643388089)
        ·
          refine ⟨26829406200001966982541067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35772541600002622643388089 26829406200001966982541067)
          ·
            refine ⟨40244109300002950473811601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26829406200001966982541067 40244109300002950473811601)
            ·
              refine ⟨30183081975002212855358701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40244109300002950473811601 30183081975002212855358701)
              ·
                refine ⟨11318655740625829820759513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30183081975002212855358701 11318655740625829820759513)
                ·
                  refine ⟨8488991805469372365569635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11318655740625829820759513 8488991805469372365569635)
                  ·
                    refine ⟨12733487708204058548354453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8488991805469372365569635 12733487708204058548354453)
                    ·
                      refine ⟨596882236322065244454115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12733487708204058548354453 596882236322065244454115)
                      ·
                        rfl

theorem cell23_1162424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1162424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162424 prefixEnd_1162424 := by exact prefixLift 1162424
  have htrace : WordTrace (prefixWord ++ tailWord_1162424) baseStart_1162424 baseEnd_1162424 := by
    simpa [prefixWord, tailWord_1162424, baseEnd_1162424] using wordTrace_append hprefix tailTrace_1162424
  have hstable : (prefixWord ++ tailWord_1162424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162424).length < 2 ^ (prefixWord ++ tailWord_1162424).sum := by decide
  have hdescent : baseEnd_1162424 < baseStart_1162424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162428 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1162428 : Nat := 118140960795 + 1162428 * 2 ^ 59
def prefixEnd_1162428 : Nat := 4983230072969 + 3 ^ 40 * 1162428 * 2
def baseEnd_1162428 : Nat := 596884290244683228804097

theorem tailTrace_1162428 : CollatzResearch.WordTrace tailWord_1162428 prefixEnd_1162428 596884290244683228804097 := by
  unfold tailWord_1162428
  simp only [CollatzResearch.WordTrace]
  refine ⟨21198616116364678870987969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28264821488486238494650625 21198616116364678870987969)
  ·
    refine ⟨15898962087273509153240977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21198616116364678870987969 15898962087273509153240977)
    ·
      refine ⟨11924221565455131864930733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15898962087273509153240977 11924221565455131864930733)
      ·
        refine ⟨4471583087045674449349025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11924221565455131864930733 4471583087045674449349025)
        ·
          refine ⟨3353687315284255837011769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4471583087045674449349025 3353687315284255837011769)
          ·
            refine ⟨2515265486463191877758827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3353687315284255837011769 2515265486463191877758827)
            ·
              refine ⟨3772898229694787816638241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515265486463191877758827 3772898229694787816638241)
              ·
                refine ⟨2829673672271090862478681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772898229694787816638241 2829673672271090862478681)
                ·
                  refine ⟨2122255254203318146859011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2829673672271090862478681 2122255254203318146859011)
                  ·
                    refine ⟨3183382881304977220288517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2122255254203318146859011 3183382881304977220288517)
                    ·
                      refine ⟨596884290244683228804097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3183382881304977220288517 596884290244683228804097)
                      ·
                        rfl

theorem cell23_1162428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1162428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162428 prefixEnd_1162428 := by exact prefixLift 1162428
  have htrace : WordTrace (prefixWord ++ tailWord_1162428) baseStart_1162428 baseEnd_1162428 := by
    simpa [prefixWord, tailWord_1162428, baseEnd_1162428] using wordTrace_append hprefix tailTrace_1162428
  have hstable : (prefixWord ++ tailWord_1162428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162428).length < 2 ^ (prefixWord ++ tailWord_1162428).sum := by decide
  have hdescent : baseEnd_1162428 < baseStart_1162428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162431 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_1162431 : Nat := 118140960795 + 1162431 * 2 ^ 59
def prefixEnd_1162431 : Nat := 4983230072969 + 3 ^ 40 * 1162431 * 2
def baseEnd_1162431 : Nat := 596885830686646717066583

theorem tailTrace_1162431 : CollatzResearch.WordTrace tailWord_1162431 prefixEnd_1162431 596885830686646717066583 := by
  unfold tailWord_1162431
  simp only [CollatzResearch.WordTrace]
  refine ⟨42397341651718489254335147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28264894434478992836223431 42397341651718489254335147)
  ·
    refine ⟨63596012477577733881502721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42397341651718489254335147 63596012477577733881502721)
    ·
      refine ⟨47697009358183300411127041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63596012477577733881502721 47697009358183300411127041)
      ·
        refine ⟨35772757018637475308345281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47697009358183300411127041 35772757018637475308345281)
        ·
          refine ⟨26829567763978106481258961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35772757018637475308345281 26829567763978106481258961)
          ·
            refine ⟨20122175822983579860944221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26829567763978106481258961 20122175822983579860944221)
            ·
              refine ⟨7545815933618842447854083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20122175822983579860944221 7545815933618842447854083)
              ·
                refine ⟨11318723900428263671781125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7545815933618842447854083 11318723900428263671781125)
                ·
                  refine ⟨2122260731330299438458961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11318723900428263671781125 2122260731330299438458961)
                  ·
                    refine ⟨1591695548497724578844221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2122260731330299438458961 1591695548497724578844221)
                    ·
                      refine ⟨596885830686646717066583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591695548497724578844221 596885830686646717066583)
                      ·
                        rfl

theorem cell23_1162431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_1162431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162431 prefixEnd_1162431 := by exact prefixLift 1162431
  have htrace : WordTrace (prefixWord ++ tailWord_1162431) baseStart_1162431 baseEnd_1162431 := by
    simpa [prefixWord, tailWord_1162431, baseEnd_1162431] using wordTrace_append hprefix tailTrace_1162431
  have hstable : (prefixWord ++ tailWord_1162431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162431).length < 2 ^ (prefixWord ++ tailWord_1162431).sum := by decide
  have hdescent : baseEnd_1162431 < baseStart_1162431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162501 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_1162501 : Nat := 118140960795 + 1162501 * 2 ^ 59
def prefixEnd_1162501 : Nat := 4983230072969 + 3 ^ 40 * 1162501 * 2
def baseEnd_1162501 : Nat := 596921774332461443191261

theorem tailTrace_1162501 : CollatzResearch.WordTrace tailWord_1162501 prefixEnd_1162501 596921774332461443191261 := by
  unfold tailWord_1162501
  simp only [CollatzResearch.WordTrace]
  refine ⟨42399894761464891209383357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28266596507643260806255571 42399894761464891209383357)
  ·
    refine ⟨15899960535549334203518759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42399894761464891209383357 15899960535549334203518759)
    ·
      refine ⟨23849940803324001305278139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15899960535549334203518759 23849940803324001305278139)
      ·
        refine ⟨35774911204986001957917209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23849940803324001305278139 35774911204986001957917209)
        ·
          refine ⟨26831183403739501468437907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35774911204986001957917209 26831183403739501468437907)
          ·
            refine ⟨40246775105609252202656861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26831183403739501468437907 40246775105609252202656861)
            ·
              refine ⟨15092540664603469575996323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40246775105609252202656861 15092540664603469575996323)
              ·
                refine ⟨22638810996905204363994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15092540664603469575996323 22638810996905204363994485)
                ·
                  refine ⟨2122388530959862909124483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22638810996905204363994485 2122388530959862909124483)
                  ·
                    refine ⟨3183582796439794363686725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2122388530959862909124483 3183582796439794363686725)
                    ·
                      refine ⟨596921774332461443191261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3183582796439794363686725 596921774332461443191261)
                      ·
                        rfl

theorem cell23_1162501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_1162501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162501 prefixEnd_1162501 := by exact prefixLift 1162501
  have htrace : WordTrace (prefixWord ++ tailWord_1162501) baseStart_1162501 baseEnd_1162501 := by
    simpa [prefixWord, tailWord_1162501, baseEnd_1162501] using wordTrace_append hprefix tailTrace_1162501
  have hstable : (prefixWord ++ tailWord_1162501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162501).length < 2 ^ (prefixWord ++ tailWord_1162501).sum := by decide
  have hdescent : baseEnd_1162501 < baseStart_1162501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162511 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 8, 4]
def baseStart_1162511 : Nat := 118140960795 + 1162511 * 2 ^ 59
def prefixEnd_1162511 : Nat := 4983230072969 + 3 ^ 40 * 1162511 * 2
def baseEnd_1162511 : Nat := 198975636379668801355405

theorem tailTrace_1162511 : CollatzResearch.WordTrace tailWord_1162511 prefixEnd_1162511 198975636379668801355405 := by
  unfold tailWord_1162511
  simp only [CollatzResearch.WordTrace]
  refine ⟨42400259491428662917247387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28266839660952441944831591 42400259491428662917247387)
  ·
    refine ⟨63600389237142994375871081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42400259491428662917247387 63600389237142994375871081)
    ·
      refine ⟨47700291927857245781903311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63600389237142994375871081 47700291927857245781903311)
      ·
        refine ⟨71550437891785868672854967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47700291927857245781903311 71550437891785868672854967)
        ·
          refine ⟨107325656837678803009282451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71550437891785868672854967 107325656837678803009282451)
          ·
            refine ⟨160988485256518204513923677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107325656837678803009282451 160988485256518204513923677)
            ·
              refine ⟨60370681971194326692721379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160988485256518204513923677 60370681971194326692721379)
              ·
                refine ⟨90556022956791490039082069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60370681971194326692721379 90556022956791490039082069)
                ·
                  refine ⟨1061203394024900273895493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 90556022956791490039082069 1061203394024900273895493)
                  ·
                    refine ⟨198975636379668801355405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061203394024900273895493 198975636379668801355405)
                    ·
                      rfl

theorem cell23_1162511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_1162511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162511 prefixEnd_1162511 := by exact prefixLift 1162511
  have htrace : WordTrace (prefixWord ++ tailWord_1162511) baseStart_1162511 baseEnd_1162511 := by
    simpa [prefixWord, tailWord_1162511, baseEnd_1162511] using wordTrace_append hprefix tailTrace_1162511
  have hstable : (prefixWord ++ tailWord_1162511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162511).length < 2 ^ (prefixWord ++ tailWord_1162511).sum := by decide
  have hdescent : baseEnd_1162511 < baseStart_1162511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162522 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_1162522 : Nat := 118140960795 + 1162522 * 2 ^ 59
def prefixEnd_1162522 : Nat := 4983230072969 + 3 ^ 40 * 1162522 * 2
def baseEnd_1162522 : Nat := 596932557426205861028665

theorem tailTrace_1162522 : CollatzResearch.WordTrace tailWord_1162522 prefixEnd_1162522 596932557426205861028665 := by
  unfold tailWord_1162522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10600165173597202948974455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28267107129592541197265213 10600165173597202948974455)
  ·
    refine ⟨15900247760395804423461683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10600165173597202948974455 15900247760395804423461683)
    ·
      refine ⟨23850371640593706635192525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15900247760395804423461683 23850371640593706635192525)
      ·
        refine ⟨8943889365222639988197197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23850371640593706635192525 8943889365222639988197197)
        ·
          refine ⟨3353958511958489995573949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8943889365222639988197197 3353958511958489995573949)
          ·
            refine ⟨1257734441984433748340231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3353958511958489995573949 1257734441984433748340231)
            ·
              refine ⟨1886601662976650622510347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257734441984433748340231 1886601662976650622510347)
              ·
                refine ⟨2829902494464975933765521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886601662976650622510347 2829902494464975933765521)
                ·
                  refine ⟨2122426870848731950324141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2829902494464975933765521 2122426870848731950324141)
                  ·
                    refine ⟨795910076568274481371553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122426870848731950324141 795910076568274481371553)
                    ·
                      refine ⟨596932557426205861028665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 795910076568274481371553 596932557426205861028665)
                      ·
                        rfl

theorem cell23_1162522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_1162522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162522 prefixEnd_1162522 := by exact prefixLift 1162522
  have htrace : WordTrace (prefixWord ++ tailWord_1162522) baseStart_1162522 baseEnd_1162522 := by
    simpa [prefixWord, tailWord_1162522, baseEnd_1162522] using wordTrace_append hprefix tailTrace_1162522
  have hstable : (prefixWord ++ tailWord_1162522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162522).length < 2 ^ (prefixWord ++ tailWord_1162522).sum := by decide
  have hdescent : baseEnd_1162522 < baseStart_1162522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162545 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_1162545 : Nat := 118140960795 + 1162545 * 2 ^ 59
def prefixEnd_1162545 : Nat := 4983230072969 + 3 ^ 40 * 1162545 * 2
def baseEnd_1162545 : Nat := 198981455827086423680353

theorem tailTrace_1162545 : CollatzResearch.WordTrace tailWord_1162545 prefixEnd_1162545 198981455827086423680353 := by
  unfold tailWord_1162545
  simp only [CollatzResearch.WordTrace]
  refine ⟨42401499573305486723985089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28267666382203657815990059 42401499573305486723985089)
  ·
    refine ⟨31801124679979115042988817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42401499573305486723985089 31801124679979115042988817)
    ·
      refine ⟨23850843509984336282241613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31801124679979115042988817 23850843509984336282241613)
      ·
        refine ⟨8944066316244126105840605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23850843509984336282241613 8944066316244126105840605)
        ·
          refine ⟨3354024868591547289690227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8944066316244126105840605 3354024868591547289690227)
          ·
            refine ⟨5031037302887320934535341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354024868591547289690227 5031037302887320934535341)
            ·
              refine ⟨1886638988582745350450753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5031037302887320934535341 1886638988582745350450753)
              ·
                refine ⟨1414979241437059012838065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886638988582745350450753 1414979241437059012838065)
                ·
                  refine ⟨1061234431077794259628549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414979241437059012838065 1061234431077794259628549)
                  ·
                    refine ⟨198981455827086423680353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061234431077794259628549 198981455827086423680353)
                    ·
                      rfl

theorem cell23_1162545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_1162545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162545 prefixEnd_1162545 := by exact prefixLift 1162545
  have htrace : WordTrace (prefixWord ++ tailWord_1162545) baseStart_1162545 baseEnd_1162545 := by
    simpa [prefixWord, tailWord_1162545, baseEnd_1162545] using wordTrace_append hprefix tailTrace_1162545
  have hstable : (prefixWord ++ tailWord_1162545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162545).length < 2 ^ (prefixWord ++ tailWord_1162545).sum := by decide
  have hdescent : baseEnd_1162545 < baseStart_1162545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162548 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1162548 : Nat := 118140960795 + 1162548 * 2 ^ 59
def prefixEnd_1162548 : Nat := 4983230072969 + 3 ^ 40 * 1162548 * 2
def baseEnd_1162548 : Nat := 596945907923222759303545

theorem tailTrace_1162548 : CollatzResearch.WordTrace tailWord_1162548 prefixEnd_1162548 596945907923222759303545 := by
  unfold tailWord_1162548
  simp only [CollatzResearch.WordTrace]
  refine ⟨21200804496147309118172149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28267739328196412157562865 21200804496147309118172149)
  ·
    refine ⟨1987575421513810229828639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21200804496147309118172149 1987575421513810229828639)
    ·
      refine ⟨2981363132270715344742959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1987575421513810229828639 2981363132270715344742959)
      ·
        refine ⟨4472044698406073017114439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981363132270715344742959 4472044698406073017114439)
        ·
          refine ⟨6708067047609109525671659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472044698406073017114439 6708067047609109525671659)
          ·
            refine ⟨10062100571413664288507489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708067047609109525671659 10062100571413664288507489)
            ·
              refine ⟨7546575428560248216380617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10062100571413664288507489 7546575428560248216380617)
              ·
                refine ⟨5659931571420186162285463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7546575428560248216380617 5659931571420186162285463)
                ·
                  refine ⟨8489897357130279243428195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659931571420186162285463 8489897357130279243428195)
                  ·
                    refine ⟨12734846035695418865142293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8489897357130279243428195 12734846035695418865142293)
                    ·
                      refine ⟨596945907923222759303545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12734846035695418865142293 596945907923222759303545)
                      ·
                        rfl

theorem cell23_1162548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1162548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162548 prefixEnd_1162548 := by exact prefixLift 1162548
  have htrace : WordTrace (prefixWord ++ tailWord_1162548) baseStart_1162548 baseEnd_1162548 := by
    simpa [prefixWord, tailWord_1162548, baseEnd_1162548] using wordTrace_append hprefix tailTrace_1162548
  have hstable : (prefixWord ++ tailWord_1162548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162548).length < 2 ^ (prefixWord ++ tailWord_1162548).sum := by decide
  have hdescent : baseEnd_1162548 < baseStart_1162548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162551 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_1162551 : Nat := 118140960795 + 1162551 * 2 ^ 59
def prefixEnd_1162551 : Nat := 4983230072969 + 3 ^ 40 * 1162551 * 2
def baseEnd_1162551 : Nat := 596947448365186247566031

theorem tailTrace_1162551 : CollatzResearch.WordTrace tailWord_1162551 prefixEnd_1162551 596947448365186247566031 := by
  unfold tailWord_1162551
  simp only [CollatzResearch.WordTrace]
  refine ⟨42401718411283749748703507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28267812274189166499135671 42401718411283749748703507)
  ·
    refine ⟨63602577616925624623055261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42401718411283749748703507 63602577616925624623055261)
    ·
      refine ⟨23850966606347109233645723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63602577616925624623055261 23850966606347109233645723)
      ·
        refine ⟨35776449909520663850468585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23850966606347109233645723 35776449909520663850468585)
        ·
          refine ⟨26832337432140497887851439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35776449909520663850468585 26832337432140497887851439)
          ·
            refine ⟨40248506148210746831777159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26832337432140497887851439 40248506148210746831777159)
            ·
              refine ⟨60372759222316120247665739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40248506148210746831777159 60372759222316120247665739)
              ·
                refine ⟨90559138833474180371498609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60372759222316120247665739 90559138833474180371498609)
                ·
                  refine ⟨67919354125105635278623957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90559138833474180371498609 67919354125105635278623957)
                  ·
                    refine ⟨1591859862307163326842749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67919354125105635278623957 1591859862307163326842749)
                    ·
                      refine ⟨596947448365186247566031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1591859862307163326842749 596947448365186247566031)
                      ·
                        rfl

theorem cell23_1162551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_1162551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162551 prefixEnd_1162551 := by exact prefixLift 1162551
  have htrace : WordTrace (prefixWord ++ tailWord_1162551) baseStart_1162551 baseEnd_1162551 := by
    simpa [prefixWord, tailWord_1162551, baseEnd_1162551] using wordTrace_append hprefix tailTrace_1162551
  have hstable : (prefixWord ++ tailWord_1162551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162551).length < 2 ^ (prefixWord ++ tailWord_1162551).sum := by decide
  have hdescent : baseEnd_1162551 < baseStart_1162551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162589 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1162589 : Nat := 118140960795 + 1162589 * 2 ^ 59
def prefixEnd_1162589 : Nat := 4983230072969 + 3 ^ 40 * 1162589 * 2
def baseEnd_1162589 : Nat := 596966960630057098890857

theorem tailTrace_1162589 : CollatzResearch.WordTrace tailWord_1162589 prefixEnd_1162589 596966960630057098890857 := by
  unfold tailWord_1162589
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403104385146082238586821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28268736256764054825724547 42403104385146082238586821)
  ·
    refine ⟨7950582072214890419735029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42403104385146082238586821 7950582072214890419735029)
    ·
      refine ⟨745367069270145976850159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7950582072214890419735029 745367069270145976850159)
      ·
        refine ⟨1118050603905218965275239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745367069270145976850159 1118050603905218965275239)
        ·
          refine ⟨1677075905857828447912859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118050603905218965275239 1677075905857828447912859)
          ·
            refine ⟨2515613858786742671869289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677075905857828447912859 2515613858786742671869289)
            ·
              refine ⟨1886710394090057003901967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515613858786742671869289 1886710394090057003901967)
              ·
                refine ⟨2830065591135085505852951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886710394090057003901967 2830065591135085505852951)
                ·
                  refine ⟨4245098386702628258779427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830065591135085505852951 4245098386702628258779427)
                  ·
                    refine ⟨6367647580053942388169141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245098386702628258779427 6367647580053942388169141)
                    ·
                      refine ⟨596966960630057098890857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6367647580053942388169141 596966960630057098890857)
                      ·
                        rfl

theorem cell23_1162589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1162589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162589 prefixEnd_1162589 := by exact prefixLift 1162589
  have htrace : WordTrace (prefixWord ++ tailWord_1162589) baseStart_1162589 baseEnd_1162589 := by
    simpa [prefixWord, tailWord_1162589, baseEnd_1162589] using wordTrace_append hprefix tailTrace_1162589
  have hstable : (prefixWord ++ tailWord_1162589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162589).length < 2 ^ (prefixWord ++ tailWord_1162589).sum := by decide
  have hdescent : baseEnd_1162589 < baseStart_1162589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162591 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1162591 : Nat := 118140960795 + 1162591 * 2 ^ 59
def prefixEnd_1162591 : Nat := 4983230072969 + 3 ^ 40 * 1162591 * 2
def baseEnd_1162591 : Nat := 596967987591366091065847

theorem tailTrace_1162591 : CollatzResearch.WordTrace tailWord_1162591 prefixEnd_1162591 596967987591366091065847 := by
  unfold tailWord_1162591
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403177331138836580159627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28268784887425891053439751 42403177331138836580159627)
  ·
    refine ⟨63604765996708254870239441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42403177331138836580159627 63604765996708254870239441)
    ·
      refine ⟨47703574497531191152679581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63604765996708254870239441 47703574497531191152679581)
      ·
        refine ⟨17888840436574196682254843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47703574497531191152679581 17888840436574196682254843)
        ·
          refine ⟨26833260654861295023382265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17888840436574196682254843 26833260654861295023382265)
          ·
            refine ⟨20124945491145971267536699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26833260654861295023382265 20124945491145971267536699)
            ·
              refine ⟨30187418236718956901305049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20124945491145971267536699 30187418236718956901305049)
              ·
                refine ⟨22640563677539217675978787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30187418236718956901305049 22640563677539217675978787)
                ·
                  refine ⟨33960845516308826513968181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22640563677539217675978787 33960845516308826513968181)
                  ·
                    refine ⟨3183829267153952485684517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33960845516308826513968181 3183829267153952485684517)
                    ·
                      refine ⟨596967987591366091065847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3183829267153952485684517 596967987591366091065847)
                      ·
                        rfl

theorem cell23_1162591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1162591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162591 prefixEnd_1162591 := by exact prefixLift 1162591
  have htrace : WordTrace (prefixWord ++ tailWord_1162591) baseStart_1162591 baseEnd_1162591 := by
    simpa [prefixWord, tailWord_1162591, baseEnd_1162591] using wordTrace_append hprefix tailTrace_1162591
  have hstable : (prefixWord ++ tailWord_1162591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162591).length < 2 ^ (prefixWord ++ tailWord_1162591).sum := by decide
  have hdescent : baseEnd_1162591 < baseStart_1162591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162601 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_1162601 : Nat := 118140960795 + 1162601 * 2 ^ 59
def prefixEnd_1162601 : Nat := 4983230072969 + 3 ^ 40 * 1162601 * 2
def baseEnd_1162601 : Nat := 198991040799303683980267

theorem tailTrace_1162601 : CollatzResearch.WordTrace tailWord_1162601 prefixEnd_1162601 198991040799303683980267 := by
  unfold tailWord_1162601
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403542061102608288023657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28269028040735072192015771 42403542061102608288023657)
  ·
    refine ⟨31802656545826956216017743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42403542061102608288023657 31802656545826956216017743)
    ·
      refine ⟨47703984818740434324026615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31802656545826956216017743 47703984818740434324026615)
      ·
        refine ⟨71555977228110651486039923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47703984818740434324026615 71555977228110651486039923)
        ·
          refine ⟨107333965842165977229059885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71555977228110651486039923 107333965842165977229059885)
          ·
            refine ⟨40250237190812241460897457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107333965842165977229059885 40250237190812241460897457)
            ·
              refine ⟨30187677893109181095673093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40250237190812241460897457 30187677893109181095673093)
              ·
                refine ⟨5660189604957971455438705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30187677893109181095673093 5660189604957971455438705)
                ·
                  refine ⟨4245142203718478591579029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5660189604957971455438705 4245142203718478591579029)
                  ·
                    refine ⟨198991040799303683980267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4245142203718478591579029 198991040799303683980267)
                    ·
                      rfl

theorem cell23_1162601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_1162601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162601 prefixEnd_1162601 := by exact prefixLift 1162601
  have htrace : WordTrace (prefixWord ++ tailWord_1162601) baseStart_1162601 baseEnd_1162601 := by
    simpa [prefixWord, tailWord_1162601, baseEnd_1162601] using wordTrace_append hprefix tailTrace_1162601
  have hstable : (prefixWord ++ tailWord_1162601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162601).length < 2 ^ (prefixWord ++ tailWord_1162601).sum := by decide
  have hdescent : baseEnd_1162601 < baseStart_1162601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162611 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_1162611 : Nat := 118140960795 + 1162611 * 2 ^ 59
def prefixEnd_1162611 : Nat := 4983230072969 + 3 ^ 40 * 1162611 * 2
def baseEnd_1162611 : Nat := 596978257204456012815755

theorem tailTrace_1162611 : CollatzResearch.WordTrace tailWord_1162611 prefixEnd_1162611 596978257204456012815755 := by
  unfold tailWord_1162611
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403906791066379995887687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28269271194044253330591791 42403906791066379995887687)
  ·
    refine ⟨63605860186599569993831531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42403906791066379995887687 63605860186599569993831531)
    ·
      refine ⟨95408790279899354990747297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63605860186599569993831531 95408790279899354990747297)
      ·
        refine ⟨71556592709924516243060473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95408790279899354990747297 71556592709924516243060473)
        ·
          refine ⟨53667444532443387182295355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71556592709924516243060473 53667444532443387182295355)
          ·
            refine ⟨80501166798665080773443033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53667444532443387182295355 80501166798665080773443033)
            ·
              refine ⟨60375875098998810580082275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80501166798665080773443033 60375875098998810580082275)
              ·
                refine ⟨90563812648498215870123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60375875098998810580082275 90563812648498215870123413)
                ·
                  refine ⟨4245178717898353868912035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90563812648498215870123413 4245178717898353868912035)
                  ·
                    refine ⟨6367768076847530803368053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245178717898353868912035 6367768076847530803368053)
                    ·
                      refine ⟨596978257204456012815755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6367768076847530803368053 596978257204456012815755)
                      ·
                        rfl

theorem cell23_1162611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_1162611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162611 prefixEnd_1162611 := by exact prefixLift 1162611
  have htrace : WordTrace (prefixWord ++ tailWord_1162611) baseStart_1162611 baseEnd_1162611 := by
    simpa [prefixWord, tailWord_1162611, baseEnd_1162611] using wordTrace_append hprefix tailTrace_1162611
  have hstable : (prefixWord ++ tailWord_1162611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162611).length < 2 ^ (prefixWord ++ tailWord_1162611).sum := by decide
  have hdescent : baseEnd_1162611 < baseStart_1162611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162628 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1162628 : Nat := 118140960795 + 1162628 * 2 ^ 59
def prefixEnd_1162628 : Nat := 4983230072969 + 3 ^ 40 * 1162628 * 2
def baseEnd_1162628 : Nat := 596986986375582446303177

theorem tailTrace_1162628 : CollatzResearch.WordTrace tailWord_1162628 prefixEnd_1162628 596986986375582446303177 := by
  unfold tailWord_1162628
  simp only [CollatzResearch.WordTrace]
  refine ⟨21202263416002395949628269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28269684554669861266171025 21202263416002395949628269)
  ·
    refine ⟨7950848781000898481110601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21202263416002395949628269 7950848781000898481110601)
    ·
      refine ⟨5963136585750673860832951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7950848781000898481110601 5963136585750673860832951)
      ·
        refine ⟨8944704878626010791249427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963136585750673860832951 8944704878626010791249427)
        ·
          refine ⟨13417057317939016186874141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8944704878626010791249427 13417057317939016186874141)
          ·
            refine ⟨5031396494227131070077803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13417057317939016186874141 5031396494227131070077803)
            ·
              refine ⟨7547094741340696605116705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031396494227131070077803 7547094741340696605116705)
              ·
                refine ⟨5660321056005522453837529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7547094741340696605116705 5660321056005522453837529)
                ·
                  refine ⟨4245240792004141840378147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5660321056005522453837529 4245240792004141840378147)
                  ·
                    refine ⟨6367861188006212760567221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245240792004141840378147 6367861188006212760567221)
                    ·
                      refine ⟨596986986375582446303177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6367861188006212760567221 596986986375582446303177)
                      ·
                        rfl

theorem cell23_1162628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1162628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162628 prefixEnd_1162628 := by exact prefixLift 1162628
  have htrace : WordTrace (prefixWord ++ tailWord_1162628) baseStart_1162628 baseEnd_1162628 := by
    simpa [prefixWord, tailWord_1162628, baseEnd_1162628] using wordTrace_append hprefix tailTrace_1162628
  have hstable : (prefixWord ++ tailWord_1162628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162628).length < 2 ^ (prefixWord ++ tailWord_1162628).sum := by decide
  have hdescent : baseEnd_1162628 < baseStart_1162628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162685 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_1162685 : Nat := 118140960795 + 1162685 * 2 ^ 59
def prefixEnd_1162685 : Nat := 4983230072969 + 3 ^ 40 * 1162685 * 2
def baseEnd_1162685 : Nat := 597016254772888723290415

theorem tailTrace_1162685 : CollatzResearch.WordTrace tailWord_1162685 prefixEnd_1162685 597016254772888723290415 := by
  unfold tailWord_1162685
  simp only [CollatzResearch.WordTrace]
  refine ⟨42406605792798290634081509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28271070528532193756054339 42406605792798290634081509)
  ·
    refine ⟨7951238586149679493890283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42406605792798290634081509 7951238586149679493890283)
    ·
      refine ⟨11926857879224519240835425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7951238586149679493890283 11926857879224519240835425)
      ·
        refine ⟨8945143409418389430626569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11926857879224519240835425 8945143409418389430626569)
        ·
          refine ⟨6708857557063792072969927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8945143409418389430626569 6708857557063792072969927)
          ·
            refine ⟨10063286335595688109454891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708857557063792072969927 10063286335595688109454891)
            ·
              refine ⟨15094929503393532164182337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10063286335595688109454891 15094929503393532164182337)
              ·
                refine ⟨11321197127545149123136753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15094929503393532164182337 11321197127545149123136753)
                ·
                  refine ⟨8490897845658861842352565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11321197127545149123136753 8490897845658861842352565)
                  ·
                    refine ⟨796021673030518297720553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8490897845658861842352565 796021673030518297720553)
                    ·
                      refine ⟨597016254772888723290415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796021673030518297720553 597016254772888723290415)
                      ·
                        rfl

theorem cell23_1162685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_1162685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162685 prefixEnd_1162685 := by exact prefixLift 1162685
  have htrace : WordTrace (prefixWord ++ tailWord_1162685) baseStart_1162685 baseEnd_1162685 := by
    simpa [prefixWord, tailWord_1162685, baseEnd_1162685] using wordTrace_append hprefix tailTrace_1162685
  have hstable : (prefixWord ++ tailWord_1162685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162685).length < 2 ^ (prefixWord ++ tailWord_1162685).sum := by decide
  have hdescent : baseEnd_1162685 < baseStart_1162685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162728 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1162728 : Nat := 118140960795 + 1162728 * 2 ^ 59
def prefixEnd_1162728 : Nat := 4983230072969 + 3 ^ 40 * 1162728 * 2
def baseEnd_1162728 : Nat := 597038334441032055052717

theorem tailTrace_1162728 : CollatzResearch.WordTrace tailWord_1162728 prefixEnd_1162728 597038334441032055052717 := by
  unfold tailWord_1162728
  simp only [CollatzResearch.WordTrace]
  refine ⟨21204087065821254488948419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28272116087761672651931225 21204087065821254488948419)
  ·
    refine ⟨31806130598731881733422629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21204087065821254488948419 31806130598731881733422629)
    ·
      refine ⟨5963649487262227825016743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31806130598731881733422629 5963649487262227825016743)
      ·
        refine ⟨8945474230893341737525115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963649487262227825016743 8945474230893341737525115)
        ·
          refine ⟨13418211346340012606287673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945474230893341737525115 13418211346340012606287673)
          ·
            refine ⟨10063658509755009454715755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13418211346340012606287673 10063658509755009454715755)
            ·
              refine ⟨15095487764632514182073633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10063658509755009454715755 15095487764632514182073633)
              ·
                refine ⟨11321615823474385636555225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15095487764632514182073633 11321615823474385636555225)
                ·
                  refine ⟨8491211867605789227416419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11321615823474385636555225 8491211867605789227416419)
                  ·
                    refine ⟨12736817801408683841124629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8491211867605789227416419 12736817801408683841124629)
                    ·
                      refine ⟨597038334441032055052717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12736817801408683841124629 597038334441032055052717)
                      ·
                        rfl

theorem cell23_1162728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1162728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162728 prefixEnd_1162728 := by exact prefixLift 1162728
  have htrace : WordTrace (prefixWord ++ tailWord_1162728) baseStart_1162728 baseEnd_1162728 := by
    simpa [prefixWord, tailWord_1162728, baseEnd_1162728] using wordTrace_append hprefix tailTrace_1162728
  have hstable : (prefixWord ++ tailWord_1162728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162728).length < 2 ^ (prefixWord ++ tailWord_1162728).sum := by decide
  have hdescent : baseEnd_1162728 < baseStart_1162728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162742 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1162742 : Nat := 118140960795 + 1162742 * 2 ^ 59
def prefixEnd_1162742 : Nat := 4983230072969 + 3 ^ 40 * 1162742 * 2
def baseEnd_1162742 : Nat := 199015174390065000092551

theorem tailTrace_1162742 : CollatzResearch.WordTrace tailWord_1162742 prefixEnd_1162742 199015174390065000092551 := by
  unfold tailWord_1162742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650542797099486835556655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28272456502394526245937653 2650542797099486835556655)
  ·
    refine ⟨3975814195649230253334983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650542797099486835556655 3975814195649230253334983)
    ·
      refine ⟨5963721293473845380002475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975814195649230253334983 5963721293473845380002475)
      ·
        refine ⟨8945581940210768070003713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963721293473845380002475 8945581940210768070003713)
        ·
          refine ⟨6709186455158076052502785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8945581940210768070003713 6709186455158076052502785)
          ·
            refine ⟨5031889841368557039377089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6709186455158076052502785 5031889841368557039377089)
            ·
              refine ⟨3773917381026417779532817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031889841368557039377089 3773917381026417779532817)
              ·
                refine ⟨2830438035769813334649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773917381026417779532817 2830438035769813334649613)
                ·
                  refine ⟨1061414263413680000493605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2830438035769813334649613 1061414263413680000493605)
                  ·
                    refine ⟨199015174390065000092551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061414263413680000493605 199015174390065000092551)
                    ·
                      rfl

theorem cell23_1162742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1162742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162742 prefixEnd_1162742 := by exact prefixLift 1162742
  have htrace : WordTrace (prefixWord ++ tailWord_1162742) baseStart_1162742 baseEnd_1162742 := by
    simpa [prefixWord, tailWord_1162742, baseEnd_1162742] using wordTrace_append hprefix tailTrace_1162742
  have hstable : (prefixWord ++ tailWord_1162742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162742).length < 2 ^ (prefixWord ++ tailWord_1162742).sum := by decide
  have hdescent : baseEnd_1162742 < baseStart_1162742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162759 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 1, 4]
def baseStart_1162759 : Nat := 118140960795 + 1162759 * 2 ^ 59
def prefixEnd_1162759 : Nat := 4983230072969 + 3 ^ 40 * 1162759 * 2
def baseEnd_1162759 : Nat := 199018084113773811255025

theorem tailTrace_1162759 : CollatzResearch.WordTrace tailWord_1162759 prefixEnd_1162759 199018084113773811255025 := by
  unfold tailWord_1162759
  simp only [CollatzResearch.WordTrace]
  refine ⟨42409304794530201272275331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28272869863020134181516887 42409304794530201272275331)
  ·
    refine ⟨63613957191795301908412997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42409304794530201272275331 63613957191795301908412997)
    ·
      refine ⟨11927616973461619107827437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63613957191795301908412997 11927616973461619107827437)
      ·
        refine ⟨4472856365048107165435289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11927616973461619107827437 4472856365048107165435289)
        ·
          refine ⟨3354642273786080374076467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4472856365048107165435289 3354642273786080374076467)
          ·
            refine ⟨5031963410679120561114701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354642273786080374076467 5031963410679120561114701)
            ·
              refine ⟨1886986279004670210418013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5031963410679120561114701 1886986279004670210418013)
              ·
                refine ⟨707619854626751328906755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886986279004670210418013 707619854626751328906755)
                ·
                  refine ⟨1061429781940126993360133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707619854626751328906755 1061429781940126993360133)
                  ·
                    refine ⟨199018084113773811255025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061429781940126993360133 199018084113773811255025)
                    ·
                      rfl

theorem cell23_1162759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_1162759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162759 prefixEnd_1162759 := by exact prefixLift 1162759
  have htrace : WordTrace (prefixWord ++ tailWord_1162759) baseStart_1162759 baseEnd_1162759 := by
    simpa [prefixWord, tailWord_1162759, baseEnd_1162759] using wordTrace_append hprefix tailTrace_1162759
  have hstable : (prefixWord ++ tailWord_1162759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162759).length < 2 ^ (prefixWord ++ tailWord_1162759).sum := by decide
  have hdescent : baseEnd_1162759 < baseStart_1162759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162776 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 1, 4]
def baseStart_1162776 : Nat := 118140960795 + 1162776 * 2 ^ 59
def prefixEnd_1162776 : Nat := 4983230072969 + 3 ^ 40 * 1162776 * 2
def baseEnd_1162776 : Nat := 199020993837482622417499

theorem tailTrace_1162776 : CollatzResearch.WordTrace tailWord_1162776 prefixEnd_1162776 199020993837482622417499 := by
  unfold tailWord_1162776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21204962417734306587822091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28273283223645742117096121 21204962417734306587822091)
  ·
    refine ⟨31807443626601459881733137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21204962417734306587822091 31807443626601459881733137)
    ·
      refine ⟨23855582719951094911299853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31807443626601459881733137 23855582719951094911299853)
      ·
        refine ⟨8945843519981660591737445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23855582719951094911299853 8945843519981660591737445)
        ·
          refine ⟨1677345659996561360950771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8945843519981660591737445 1677345659996561360950771)
          ·
            refine ⟨2516018489994842041426157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677345659996561360950771 2516018489994842041426157)
            ·
              refine ⟨943506933748065765534809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2516018489994842041426157 943506933748065765534809)
              ·
                refine ⟨707630200311049324151107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943506933748065765534809 707630200311049324151107)
                ·
                  refine ⟨1061445300466573986226661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707630200311049324151107 1061445300466573986226661)
                  ·
                    refine ⟨199020993837482622417499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061445300466573986226661 199020993837482622417499)
                    ·
                      rfl

theorem cell23_1162776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_1162776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162776 prefixEnd_1162776 := by exact prefixLift 1162776
  have htrace : WordTrace (prefixWord ++ tailWord_1162776) baseStart_1162776 baseEnd_1162776 := by
    simpa [prefixWord, tailWord_1162776, baseEnd_1162776] using wordTrace_append hprefix tailTrace_1162776
  have hstable : (prefixWord ++ tailWord_1162776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162776).length < 2 ^ (prefixWord ++ tailWord_1162776).sum := by decide
  have hdescent : baseEnd_1162776 < baseStart_1162776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162778 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1162778 : Nat := 118140960795 + 1162778 * 2 ^ 59
def prefixEnd_1162778 : Nat := 4983230072969 + 3 ^ 40 * 1162778 * 2
def baseEnd_1162778 : Nat := 597064008473756859427487

theorem tailTrace_1162778 : CollatzResearch.WordTrace tailWord_1162778 prefixEnd_1162778 597064008473756859427487 := by
  unfold tailWord_1162778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10602499445365341879304247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28273331854307578344811325 10602499445365341879304247)
  ·
    refine ⟨15903749168048012818956371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10602499445365341879304247 15903749168048012818956371)
    ·
      refine ⟨23855623752072019228434557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15903749168048012818956371 23855623752072019228434557)
      ·
        refine ⟨8945858907027007210662959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23855623752072019228434557 8945858907027007210662959)
        ·
          refine ⟨13418788360540510815994439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945858907027007210662959 13418788360540510815994439)
          ·
            refine ⟨20128182540810766223991659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13418788360540510815994439 20128182540810766223991659)
            ·
              refine ⟨30192273811216149335987489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20128182540810766223991659 30192273811216149335987489)
              ·
                refine ⟨22644205358412112001990617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30192273811216149335987489 22644205358412112001990617)
                ·
                  refine ⟨16983154018809084001492963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22644205358412112001990617 16983154018809084001492963)
                  ·
                    refine ⟨25474731028213626002239445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16983154018809084001492963 25474731028213626002239445)
                    ·
                      refine ⟨597064008473756859427487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25474731028213626002239445 597064008473756859427487)
                      ·
                        rfl

theorem cell23_1162778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1162778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162778 prefixEnd_1162778 := by exact prefixLift 1162778
  have htrace : WordTrace (prefixWord ++ tailWord_1162778) baseStart_1162778 baseEnd_1162778 := by
    simpa [prefixWord, tailWord_1162778, baseEnd_1162778] using wordTrace_append hprefix tailTrace_1162778
  have hstable : (prefixWord ++ tailWord_1162778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162778).length < 2 ^ (prefixWord ++ tailWord_1162778).sum := by decide
  have hdescent : baseEnd_1162778 < baseStart_1162778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162809 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1162809 : Nat := 118140960795 + 1162809 * 2 ^ 59
def prefixEnd_1162809 : Nat := 4983230072969 + 3 ^ 40 * 1162809 * 2
def baseEnd_1162809 : Nat := 597079926374046238139845

theorem tailTrace_1162809 : CollatzResearch.WordTrace tailWord_1162809 prefixEnd_1162809 597079926374046238139845 := by
  unfold tailWord_1162809
  simp only [CollatzResearch.WordTrace]
  refine ⟨42411128444349059811595481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28274085629566039874396987 42411128444349059811595481)
  ·
    refine ⟨31808346333261794858696611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42411128444349059811595481 31808346333261794858696611)
    ·
      refine ⟨47712519499892692288044917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31808346333261794858696611 47712519499892692288044917)
      ·
        refine ⟨4473048703114939902004211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47712519499892692288044917 4473048703114939902004211)
        ·
          refine ⟨6709573054672409853006317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4473048703114939902004211 6709573054672409853006317)
          ·
            refine ⟨2516089895502153694877369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6709573054672409853006317 2516089895502153694877369)
            ·
              refine ⟨1887067421626615271158027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516089895502153694877369 1887067421626615271158027)
              ·
                refine ⟨2830601132439922906737041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887067421626615271158027 2830601132439922906737041)
                ·
                  refine ⟨2122950849329942180052781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2830601132439922906737041 2122950849329942180052781)
                  ·
                    refine ⟨796106568498728317519793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2122950849329942180052781 796106568498728317519793)
                    ·
                      refine ⟨597079926374046238139845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796106568498728317519793 597079926374046238139845)
                      ·
                        rfl

theorem cell23_1162809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1162809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162809 prefixEnd_1162809 := by exact prefixLift 1162809
  have htrace : WordTrace (prefixWord ++ tailWord_1162809) baseStart_1162809 baseEnd_1162809 := by
    simpa [prefixWord, tailWord_1162809, baseEnd_1162809] using wordTrace_append hprefix tailTrace_1162809
  have hstable : (prefixWord ++ tailWord_1162809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162809).length < 2 ^ (prefixWord ++ tailWord_1162809).sum := by decide
  have hdescent : baseEnd_1162809 < baseStart_1162809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162815 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 1, 6]
def baseStart_1162815 : Nat := 118140960795 + 1162815 * 2 ^ 59
def prefixEnd_1162815 : Nat := 4983230072969 + 3 ^ 40 * 1162815 * 2
def baseEnd_1162815 : Nat := 199027669085991071554939

theorem tailTrace_1162815 : CollatzResearch.WordTrace tailWord_1162815 prefixEnd_1162815 199027669085991071554939 := by
  unfold tailWord_1162815
  simp only [CollatzResearch.WordTrace]
  refine ⟨42411347282327322836313899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28274231521551548557542599 42411347282327322836313899)
  ·
    refine ⟨63617020923490984254470849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42411347282327322836313899 63617020923490984254470849)
    ·
      refine ⟨47712765692618238190853137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63617020923490984254470849 47712765692618238190853137)
      ·
        refine ⟨35784574269463678643139853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47712765692618238190853137 35784574269463678643139853)
        ·
          refine ⟨13419215351048879491177445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35784574269463678643139853 13419215351048879491177445)
          ·
            refine ⟨2516102878321664904595771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13419215351048879491177445 2516102878321664904595771)
            ·
              refine ⟨3774154317482497356893657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516102878321664904595771 3774154317482497356893657)
              ·
                refine ⟨2830615738111873017670243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774154317482497356893657 2830615738111873017670243)
                ·
                  refine ⟨4245923607167809526505365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830615738111873017670243 4245923607167809526505365)
                  ·
                    refine ⟨199027669085991071554939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4245923607167809526505365 199027669085991071554939)
                    ·
                      rfl

theorem cell23_1162815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_1162815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162815 prefixEnd_1162815 := by exact prefixLift 1162815
  have htrace : WordTrace (prefixWord ++ tailWord_1162815) baseStart_1162815 baseEnd_1162815 := by
    simpa [prefixWord, tailWord_1162815, baseEnd_1162815] using wordTrace_append hprefix tailTrace_1162815
  have hstable : (prefixWord ++ tailWord_1162815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162815).length < 2 ^ (prefixWord ++ tailWord_1162815).sum := by decide
  have hdescent : baseEnd_1162815 < baseStart_1162815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162828 : List Nat := [2, 2, 1, 3, 1, 14]
def baseStart_1162828 : Nat := 118140960795 + 1162828 * 2 ^ 59
def prefixEnd_1162828 : Nat := 4983230072969 + 3 ^ 40 * 1162828 * 2
def baseEnd_1162828 : Nat := 2457159187269471867499

theorem tailTrace_1162828 : CollatzResearch.WordTrace tailWord_1162828 prefixEnd_1162828 2457159187269471867499 := by
  unfold tailWord_1162828
  simp only [CollatzResearch.WordTrace]
  refine ⟨21205910715640113028268569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28274547620853484037691425 21205910715640113028268569)
  ·
    refine ⟨15904433036730084771201427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21205910715640113028268569 15904433036730084771201427)
    ·
      refine ⟨23856649555095127156802141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15904433036730084771201427 23856649555095127156802141)
      ·
        refine ⟨8946243583160672683800803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23856649555095127156802141 8946243583160672683800803)
        ·
          refine ⟨13419365374741009025701205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8946243583160672683800803 13419365374741009025701205)
          ·
            refine ⟨2457159187269471867499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 13419365374741009025701205 2457159187269471867499)
            ·
              rfl

theorem cell23_1162828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 14].length) (baseStart_1162828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162828 prefixEnd_1162828 := by exact prefixLift 1162828
  have htrace : WordTrace (prefixWord ++ tailWord_1162828) baseStart_1162828 baseEnd_1162828 := by
    simpa [prefixWord, tailWord_1162828, baseEnd_1162828] using wordTrace_append hprefix tailTrace_1162828
  have hstable : (prefixWord ++ tailWord_1162828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162828).length < 2 ^ (prefixWord ++ tailWord_1162828).sum := by decide
  have hdescent : baseEnd_1162828 < baseStart_1162828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162832 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_1162832 : Nat := 118140960795 + 1162832 * 2 ^ 59
def prefixEnd_1162832 : Nat := 4983230072969 + 3 ^ 40 * 1162832 * 2
def baseEnd_1162832 : Nat := 199030578809699882717413

theorem tailTrace_1162832 : CollatzResearch.WordTrace tailWord_1162832 prefixEnd_1162832 199030578809699882717413 := by
  unfold tailWord_1162832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21205983661632867369841375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28274644882177156493121833 21205983661632867369841375)
  ·
    refine ⟨31808975492449301054762063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21205983661632867369841375 31808975492449301054762063)
    ·
      refine ⟨47713463238673951582143095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31808975492449301054762063 47713463238673951582143095)
      ·
        refine ⟨71570194858010927373214643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47713463238673951582143095 71570194858010927373214643)
        ·
          refine ⟨107355292287016391059821965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71570194858010927373214643 107355292287016391059821965)
          ·
            refine ⟨40258234607631146647433237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107355292287016391059821965 40258234607631146647433237)
            ·
              refine ⟨1887104747232709999098433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40258234607631146647433237 1887104747232709999098433)
              ·
                refine ⟨1415328560424532499323825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887104747232709999098433 1415328560424532499323825)
                ·
                  refine ⟨1061496420318399374492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1415328560424532499323825 1061496420318399374492869)
                  ·
                    refine ⟨199030578809699882717413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061496420318399374492869 199030578809699882717413)
                    ·
                      rfl

theorem cell23_1162832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_1162832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162832 prefixEnd_1162832 := by exact prefixLift 1162832
  have htrace : WordTrace (prefixWord ++ tailWord_1162832) baseStart_1162832 baseEnd_1162832 := by
    simpa [prefixWord, tailWord_1162832, baseEnd_1162832] using wordTrace_append hprefix tailTrace_1162832
  have hstable : (prefixWord ++ tailWord_1162832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162832).length < 2 ^ (prefixWord ++ tailWord_1162832).sum := by decide
  have hdescent : baseEnd_1162832 < baseStart_1162832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162852 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1162852 : Nat := 118140960795 + 1162852 * 2 ^ 59
def prefixEnd_1162852 : Nat := 4983230072969 + 3 ^ 40 * 1162852 * 2
def baseEnd_1162852 : Nat := 597102006042189569902147

theorem tailTrace_1162852 : CollatzResearch.WordTrace tailWord_1162852 prefixEnd_1162852 597102006042189569902147 := by
  unfold tailWord_1162852
  simp only [CollatzResearch.WordTrace]
  refine ⟨21206348391596639077705405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28275131188795518770273873 21206348391596639077705405)
  ·
    refine ⟨7952380646848739654139527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21206348391596639077705405 7952380646848739654139527)
    ·
      refine ⟨11928570970273109481209291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952380646848739654139527 11928570970273109481209291)
      ·
        refine ⟨17892856455409664221813937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11928570970273109481209291 17892856455409664221813937)
        ·
          refine ⟨13419642341557248166360453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17892856455409664221813937 13419642341557248166360453)
          ·
            refine ⟨2516182939041984031192585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13419642341557248166360453 2516182939041984031192585)
            ·
              refine ⟨1887137204281488023394439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516182939041984031192585 1887137204281488023394439)
              ·
                refine ⟨2830705806422232035091659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887137204281488023394439 2830705806422232035091659)
                ·
                  refine ⟨4246058709633348052637489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830705806422232035091659 4246058709633348052637489)
                  ·
                    refine ⟨3184544032225011039478117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4246058709633348052637489 3184544032225011039478117)
                    ·
                      refine ⟨597102006042189569902147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3184544032225011039478117 597102006042189569902147)
                      ·
                        rfl

theorem cell23_1162852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1162852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162852 prefixEnd_1162852 := by exact prefixLift 1162852
  have htrace : WordTrace (prefixWord ++ tailWord_1162852) baseStart_1162852 baseEnd_1162852 := by
    simpa [prefixWord, tailWord_1162852, baseEnd_1162852] using wordTrace_append hprefix tailTrace_1162852
  have hstable : (prefixWord ++ tailWord_1162852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162852).length < 2 ^ (prefixWord ++ tailWord_1162852).sum := by decide
  have hdescent : baseEnd_1162852 < baseStart_1162852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162856 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1162856 : Nat := 118140960795 + 1162856 * 2 ^ 59
def prefixEnd_1162856 : Nat := 4983230072969 + 3 ^ 40 * 1162856 * 2
def baseEnd_1162856 : Nat := 597104059964807554252129

theorem tailTrace_1162856 : CollatzResearch.WordTrace tailWord_1162856 prefixEnd_1162856 597104059964807554252129 := by
  unfold tailWord_1162856
  simp only [CollatzResearch.WordTrace]
  refine ⟨21206421337589393419278211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28275228450119191225704281 21206421337589393419278211)
  ·
    refine ⟨31809632006384090128917317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21206421337589393419278211 31809632006384090128917317)
    ·
      refine ⟨5964306001197016899171997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31809632006384090128917317 5964306001197016899171997)
      ·
        refine ⟨2236614750448881337189499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5964306001197016899171997 2236614750448881337189499)
        ·
          refine ⟨3354922125673322005784249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236614750448881337189499 3354922125673322005784249)
          ·
            refine ⟨2516191594254991504338187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354922125673322005784249 2516191594254991504338187)
            ·
              refine ⟨3774287391382487256507281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516191594254991504338187 3774287391382487256507281)
              ·
                refine ⟨2830715543536865442380461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774287391382487256507281 2830715543536865442380461)
                ·
                  refine ⟨1061518328826324540892673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2830715543536865442380461 1061518328826324540892673)
                  ·
                    refine ⟨796138746619743405669505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1061518328826324540892673 796138746619743405669505)
                    ·
                      refine ⟨597104059964807554252129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796138746619743405669505 597104059964807554252129)
                      ·
                        rfl

theorem cell23_1162856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1162856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162856 prefixEnd_1162856 := by exact prefixLift 1162856
  have htrace : WordTrace (prefixWord ++ tailWord_1162856) baseStart_1162856 baseEnd_1162856 := by
    simpa [prefixWord, tailWord_1162856, baseEnd_1162856] using wordTrace_append hprefix tailTrace_1162856
  have hstable : (prefixWord ++ tailWord_1162856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162856).length < 2 ^ (prefixWord ++ tailWord_1162856).sum := by decide
  have hdescent : baseEnd_1162856 < baseStart_1162856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162889 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 3]
def baseStart_1162889 : Nat := 118140960795 + 1162889 * 2 ^ 59
def prefixEnd_1162889 : Nat := 4983230072969 + 3 ^ 40 * 1162889 * 2
def baseEnd_1162889 : Nat := 597121004826405925139477

theorem tailTrace_1162889 : CollatzResearch.WordTrace tailWord_1162889 prefixEnd_1162889 597121004826405925139477 := by
  unfold tailWord_1162889
  simp only [CollatzResearch.WordTrace]
  refine ⟨42414046284059233474507721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28276030856039488983005147 42414046284059233474507721)
  ·
    refine ⟨31810534713044425105880791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42414046284059233474507721 31810534713044425105880791)
    ·
      refine ⟨47715802069566637658821187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31810534713044425105880791 47715802069566637658821187)
      ·
        refine ⟨71573703104349956488231781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47715802069566637658821187 71573703104349956488231781)
        ·
          refine ⟨13420069332065616841543459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71573703104349956488231781 13420069332065616841543459)
          ·
            refine ⟨20130103998098425262315189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13420069332065616841543459 20130103998098425262315189)
            ·
              refine ⟨1887197249821727368342049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20130103998098425262315189 1887197249821727368342049)
              ·
                refine ⟨1415397937366295526256537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887197249821727368342049 1415397937366295526256537)
                ·
                  refine ⟨1061548453024721644692403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1415397937366295526256537 1061548453024721644692403)
                  ·
                    refine ⟨1592322679537082467038605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061548453024721644692403 1592322679537082467038605)
                    ·
                      refine ⟨597121004826405925139477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1592322679537082467038605 597121004826405925139477)
                      ·
                        rfl

theorem cell23_1162889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_1162889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162889 prefixEnd_1162889 := by exact prefixLift 1162889
  have htrace : WordTrace (prefixWord ++ tailWord_1162889) baseStart_1162889 baseEnd_1162889 := by
    simpa [prefixWord, tailWord_1162889, baseEnd_1162889] using wordTrace_append hprefix tailTrace_1162889
  have hstable : (prefixWord ++ tailWord_1162889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162889).length < 2 ^ (prefixWord ++ tailWord_1162889).sum := by decide
  have hdescent : baseEnd_1162889 < baseStart_1162889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162915 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1162915 : Nat := 118140960795 + 1162915 * 2 ^ 59
def prefixEnd_1162915 : Nat := 4983230072969 + 3 ^ 40 * 1162915 * 2
def baseEnd_1162915 : Nat := 597134355323422823414357

theorem tailTrace_1162915 : CollatzResearch.WordTrace tailWord_1162915 prefixEnd_1162915 597134355323422823414357 := by
  unfold tailWord_1162915
  simp only [CollatzResearch.WordTrace]
  refine ⟨42414994581965039914954199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28276663054643359943302799 42414994581965039914954199)
  ·
    refine ⟨63622491872947559872431299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42414994581965039914954199 63622491872947559872431299)
    ·
      refine ⟨95433737809421339808646949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63622491872947559872431299 95433737809421339808646949)
      ·
        refine ⟨17893825839266501214121303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95433737809421339808646949 17893825839266501214121303)
        ·
          refine ⟨26840738758899751821181955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17893825839266501214121303 26840738758899751821181955)
          ·
            refine ⟨40261108138349627731772933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26840738758899751821181955 40261108138349627731772933)
            ·
              refine ⟨7548957775940555199707425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40261108138349627731772933 7548957775940555199707425)
              ·
                refine ⟨5661718331955416399780569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7548957775940555199707425 5661718331955416399780569)
                ·
                  refine ⟨4246288748966562299835427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5661718331955416399780569 4246288748966562299835427)
                  ·
                    refine ⟨6369433123449843449753141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4246288748966562299835427 6369433123449843449753141)
                    ·
                      refine ⟨597134355323422823414357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6369433123449843449753141 597134355323422823414357)
                      ·
                        rfl

theorem cell23_1162915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1162915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162915 prefixEnd_1162915 := by exact prefixLift 1162915
  have htrace : WordTrace (prefixWord ++ tailWord_1162915) baseStart_1162915 baseEnd_1162915 := by
    simpa [prefixWord, tailWord_1162915, baseEnd_1162915] using wordTrace_append hprefix tailTrace_1162915
  have hstable : (prefixWord ++ tailWord_1162915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162915).length < 2 ^ (prefixWord ++ tailWord_1162915).sum := by decide
  have hdescent : baseEnd_1162915 < baseStart_1162915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162916 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_1162916 : Nat := 118140960795 + 1162916 * 2 ^ 59
def prefixEnd_1162916 : Nat := 4983230072969 + 3 ^ 40 * 1162916 * 2
def baseEnd_1162916 : Nat := 597134868804077319501853

theorem tailTrace_1162916 : CollatzResearch.WordTrace tailWord_1162916 prefixEnd_1162916 597134868804077319501853 := by
  unfold tailWord_1162916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21207515527480708542870301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28276687369974278057160401 21207515527480708542870301)
  ·
    refine ⟨7952818322805265703576363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21207515527480708542870301 7952818322805265703576363)
    ·
      refine ⟨11929227484207898555364545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952818322805265703576363 11929227484207898555364545)
      ·
        refine ⟨8946920613155923916523409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11929227484207898555364545 8946920613155923916523409)
        ·
          refine ⟨6710190459866942937392557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8946920613155923916523409 6710190459866942937392557)
          ·
            refine ⟨2516321422450103601522209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6710190459866942937392557 2516321422450103601522209)
            ·
              refine ⟨1887241066837577701141657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516321422450103601522209 1887241066837577701141657)
              ·
                refine ⟨1415430800128183275856243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887241066837577701141657 1415430800128183275856243)
                ·
                  refine ⟨2123146200192274913784365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415430800128183275856243 2123146200192274913784365)
                  ·
                    refine ⟨796179825072103092669137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123146200192274913784365 796179825072103092669137)
                    ·
                      refine ⟨597134868804077319501853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796179825072103092669137 597134868804077319501853)
                      ·
                        rfl

theorem cell23_1162916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_1162916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162916 prefixEnd_1162916 := by exact prefixLift 1162916
  have htrace : WordTrace (prefixWord ++ tailWord_1162916) baseStart_1162916 baseEnd_1162916 := by
    simpa [prefixWord, tailWord_1162916, baseEnd_1162916] using wordTrace_append hprefix tailTrace_1162916
  have hstable : (prefixWord ++ tailWord_1162916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162916).length < 2 ^ (prefixWord ++ tailWord_1162916).sum := by decide
  have hdescent : baseEnd_1162916 < baseStart_1162916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162975 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1162975 : Nat := 118140960795 + 1162975 * 2 ^ 59
def prefixEnd_1162975 : Nat := 4983230072969 + 3 ^ 40 * 1162975 * 2
def baseEnd_1162975 : Nat := 597165164162692588664081

theorem tailTrace_1162975 : CollatzResearch.WordTrace tailWord_1162975 prefixEnd_1162975 597165164162692588664081 := by
  unfold tailWord_1162975
  simp only [CollatzResearch.WordTrace]
  refine ⟨42417182961747670162138379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28278121974498446774758919 42417182961747670162138379)
  ·
    refine ⟨63625774442621505243207569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42417182961747670162138379 63625774442621505243207569)
    ·
      refine ⟨47719330831966128932405677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63625774442621505243207569 47719330831966128932405677)
      ·
        refine ⟨17894749061987298349652129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47719330831966128932405677 17894749061987298349652129)
        ·
          refine ⟨13421061796490473762239097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17894749061987298349652129 13421061796490473762239097)
          ·
            refine ⟨10065796347367855321679323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13421061796490473762239097 10065796347367855321679323)
            ·
              refine ⟨15098694521051782982518985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065796347367855321679323 15098694521051782982518985)
              ·
                refine ⟨11324020890788837236889239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15098694521051782982518985 11324020890788837236889239)
                ·
                  refine ⟨16986031336183255855333859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11324020890788837236889239 16986031336183255855333859)
                  ·
                    refine ⟨25479047004274883783000789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16986031336183255855333859 25479047004274883783000789)
                    ·
                      refine ⟨597165164162692588664081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25479047004274883783000789 597165164162692588664081)
                      ·
                        rfl

theorem cell23_1162975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1162975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1162975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1162975 prefixEnd_1162975 := by exact prefixLift 1162975
  have htrace : WordTrace (prefixWord ++ tailWord_1162975) baseStart_1162975 baseEnd_1162975 := by
    simpa [prefixWord, tailWord_1162975, baseEnd_1162975] using wordTrace_append hprefix tailTrace_1162975
  have hstable : (prefixWord ++ tailWord_1162975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162975).length < 2 ^ (prefixWord ++ tailWord_1162975).sum := by decide
  have hdescent : baseEnd_1162975 < baseStart_1162975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163014 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1163014 : Nat := 118140960795 + 1163014 * 2 ^ 59
def prefixEnd_1163014 : Nat := 4983230072969 + 3 ^ 40 * 1163014 * 2
def baseEnd_1163014 : Nat := 597185189908217936076403

theorem tailTrace_1163014 : CollatzResearch.WordTrace tailWord_1163014 prefixEnd_1163014 597185189908217936076403 := by
  unfold tailWord_1163014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325581419018949369462753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28279070272404253215205397 1325581419018949369462753)
  ·
    refine ⟨994186064264212027097065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1325581419018949369462753 994186064264212027097065)
    ·
      refine ⟨745639548198159020322799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 994186064264212027097065 745639548198159020322799)
      ·
        refine ⟨1118459322297238530484199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745639548198159020322799 1118459322297238530484199)
        ·
          refine ⟨1677688983445857795726299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118459322297238530484199 1677688983445857795726299)
          ·
            refine ⟨2516533475168786693589449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677688983445857795726299 2516533475168786693589449)
            ·
              refine ⟨1887400106376590020192087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516533475168786693589449 1887400106376590020192087)
              ·
                refine ⟨2831100159564885030288131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887400106376590020192087 2831100159564885030288131)
                ·
                  refine ⟨4246650239347327545432197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831100159564885030288131 4246650239347327545432197)
                  ·
                    refine ⟨796246919877623914768537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246650239347327545432197 796246919877623914768537)
                    ·
                      refine ⟨597185189908217936076403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796246919877623914768537 597185189908217936076403)
                      ·
                        rfl

theorem cell23_1163014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1163014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163014 prefixEnd_1163014 := by exact prefixLift 1163014
  have htrace : WordTrace (prefixWord ++ tailWord_1163014) baseStart_1163014 baseEnd_1163014 := by
    simpa [prefixWord, tailWord_1163014, baseEnd_1163014] using wordTrace_append hprefix tailTrace_1163014
  have hstable : (prefixWord ++ tailWord_1163014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163014).length < 2 ^ (prefixWord ++ tailWord_1163014).sum := by decide
  have hdescent : baseEnd_1163014 < baseStart_1163014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163025 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 10]
def baseStart_1163025 : Nat := 118140960795 + 1163025 * 2 ^ 59
def prefixEnd_1163025 : Nat := 4983230072969 + 3 ^ 40 * 1163025 * 2
def baseEnd_1163025 : Nat := 66354537577268599226539

theorem tailTrace_1163025 : CollatzResearch.WordTrace tailWord_1163025 prefixEnd_1163025 66354537577268599226539 := by
  unfold tailWord_1163025
  simp only [CollatzResearch.WordTrace]
  refine ⟨42419006611566528701458529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28279337741044352467639019 42419006611566528701458529)
  ·
    refine ⟨31814254958674896526093897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42419006611566528701458529 31814254958674896526093897)
    ·
      refine ⟨23860691219006172394570423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31814254958674896526093897 23860691219006172394570423)
      ·
        refine ⟨35791036828509258591855635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23860691219006172394570423 35791036828509258591855635)
        ·
          refine ⟨53686555242763887887783453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35791036828509258591855635 53686555242763887887783453)
          ·
            refine ⟨20132458216036457957918795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53686555242763887887783453 20132458216036457957918795)
            ·
              refine ⟨30198687324054686936878193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20132458216036457957918795 30198687324054686936878193)
              ·
                refine ⟨22649015493041015202658645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30198687324054686936878193 22649015493041015202658645)
                ·
                  refine ⟨66354537577268599226539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22649015493041015202658645 66354537577268599226539)
                  ·
                    rfl

theorem cell23_1163025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_1163025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163025 prefixEnd_1163025 := by exact prefixLift 1163025
  have htrace : WordTrace (prefixWord ++ tailWord_1163025) baseStart_1163025 baseEnd_1163025 := by
    simpa [prefixWord, tailWord_1163025, baseEnd_1163025] using wordTrace_append hprefix tailTrace_1163025
  have hstable : (prefixWord ++ tailWord_1163025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163025).length < 2 ^ (prefixWord ++ tailWord_1163025).sum := by decide
  have hdescent : baseEnd_1163025 < baseStart_1163025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163029 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1163029 : Nat := 118140960795 + 1163029 * 2 ^ 59
def prefixEnd_1163029 : Nat := 4983230072969 + 3 ^ 40 * 1163029 * 2
def baseEnd_1163029 : Nat := 199064297372678459129611

theorem tailTrace_1163029 : CollatzResearch.WordTrace tailWord_1163029 prefixEnd_1163029 199064297372678459129611 := by
  unfold tailWord_1163029
  simp only [CollatzResearch.WordTrace]
  refine ⟨42419152503552037384604141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28279435002368024923069427 42419152503552037384604141)
  ·
    refine ⟨15907182188832014019226553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42419152503552037384604141 15907182188832014019226553)
    ·
      refine ⟨11930386641624010514419915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15907182188832014019226553 11930386641624010514419915)
      ·
        refine ⟨17895579962436015771629873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11930386641624010514419915 17895579962436015771629873)
        ·
          refine ⟨13421684971827011828722405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17895579962436015771629873 13421684971827011828722405)
          ·
            refine ⟨2516565932217564717885451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13421684971827011828722405 2516565932217564717885451)
            ·
              refine ⟨3774848898326347076828177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516565932217564717885451 3774848898326347076828177)
              ·
                refine ⟨2831136673744760307621133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774848898326347076828177 2831136673744760307621133)
                ·
                  refine ⟨1061676252654285115357925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2831136673744760307621133 1061676252654285115357925)
                  ·
                    refine ⟨199064297372678459129611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061676252654285115357925 199064297372678459129611)
                    ·
                      rfl

theorem cell23_1163029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1163029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163029 prefixEnd_1163029 := by exact prefixLift 1163029
  have htrace : WordTrace (prefixWord ++ tailWord_1163029) baseStart_1163029 baseEnd_1163029 := by
    simpa [prefixWord, tailWord_1163029, baseEnd_1163029] using wordTrace_append hprefix tailTrace_1163029
  have hstable : (prefixWord ++ tailWord_1163029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163029).length < 2 ^ (prefixWord ++ tailWord_1163029).sum := by decide
  have hdescent : baseEnd_1163029 < baseStart_1163029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163042 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1163042 : Nat := 118140960795 + 1163042 * 2 ^ 59
def prefixEnd_1163042 : Nat := 4983230072969 + 3 ^ 40 * 1163042 * 2
def baseEnd_1163042 : Nat := 66355507485171536280697

theorem tailTrace_1163042 : CollatzResearch.WordTrace tailWord_1163042 prefixEnd_1163042 66355507485171536280697 := by
  unfold tailWord_1163042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604906663126235151206845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28279751101669960403218253 10604906663126235151206845)
  ·
    refine ⟨3976839998672338181702567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10604906663126235151206845 3976839998672338181702567)
    ·
      refine ⟨5965259998008507272553851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3976839998672338181702567 5965259998008507272553851)
      ·
        refine ⟨8947889997012760908830777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965259998008507272553851 8947889997012760908830777)
        ·
          refine ⟨6710917497759570681623083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8947889997012760908830777 6710917497759570681623083)
          ·
            refine ⟨10066376246639356022434625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710917497759570681623083 10066376246639356022434625)
            ·
              refine ⟨7549782184979517016825969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10066376246639356022434625 7549782184979517016825969)
              ·
                refine ⟨5662336638734637762619477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7549782184979517016825969 5662336638734637762619477)
                ·
                  refine ⟨66355507485171536280697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5662336638734637762619477 66355507485171536280697)
                  ·
                    rfl

theorem cell23_1163042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1163042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163042 prefixEnd_1163042 := by exact prefixLift 1163042
  have htrace : WordTrace (prefixWord ++ tailWord_1163042) baseStart_1163042 baseEnd_1163042 := by
    simpa [prefixWord, tailWord_1163042, baseEnd_1163042] using wordTrace_append hprefix tailTrace_1163042
  have hstable : (prefixWord ++ tailWord_1163042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163042).length < 2 ^ (prefixWord ++ tailWord_1163042).sum := by decide
  have hdescent : baseEnd_1163042 < baseStart_1163042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163079 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_1163079 : Nat := 118140960795 + 1163079 * 2 ^ 59
def prefixEnd_1163079 : Nat := 4983230072969 + 3 ^ 40 * 1163079 * 2
def baseEnd_1163079 : Nat := 597218566150760181763603

theorem tailTrace_1163079 : CollatzResearch.WordTrace tailWord_1163079 prefixEnd_1163079 597218566150760181763603 := by
  unfold tailWord_1163079
  simp only [CollatzResearch.WordTrace]
  refine ⟨42420976153370895923924291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28280650768913930615949527 42420976153370895923924291)
  ·
    refine ⟨63631464230056343885886437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42420976153370895923924291 63631464230056343885886437)
    ·
      refine ⟨11930899543135564478603707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63631464230056343885886437 11930899543135564478603707)
      ·
        refine ⟨17896349314703346717905561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11930899543135564478603707 17896349314703346717905561)
        ·
          refine ⟨13422261986027510038429171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17896349314703346717905561 13422261986027510038429171)
          ·
            refine ⟨20133392979041265057643757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13422261986027510038429171 20133392979041265057643757)
            ·
              refine ⟨7550022367140474396616409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20133392979041265057643757 7550022367140474396616409)
              ·
                refine ⟨5662516775355355797462307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550022367140474396616409 5662516775355355797462307)
                ·
                  refine ⟨8493775163033033696193461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5662516775355355797462307 8493775163033033696193461)
                  ·
                    refine ⟨796291421534346909018137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8493775163033033696193461 796291421534346909018137)
                    ·
                      refine ⟨597218566150760181763603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796291421534346909018137 597218566150760181763603)
                      ·
                        rfl

theorem cell23_1163079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_1163079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163079 prefixEnd_1163079 := by exact prefixLift 1163079
  have htrace : WordTrace (prefixWord ++ tailWord_1163079) baseStart_1163079 baseEnd_1163079 := by
    simpa [prefixWord, tailWord_1163079, baseEnd_1163079] using wordTrace_append hprefix tailTrace_1163079
  have hstable : (prefixWord ++ tailWord_1163079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163079).length < 2 ^ (prefixWord ++ tailWord_1163079).sum := by decide
  have hdescent : baseEnd_1163079 < baseStart_1163079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163089 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_1163089 : Nat := 118140960795 + 1163089 * 2 ^ 59
def prefixEnd_1163089 : Nat := 4983230072969 + 3 ^ 40 * 1163089 * 2
def baseEnd_1163089 : Nat := 199074566985768380879519

theorem tailTrace_1163089 : CollatzResearch.WordTrace tailWord_1163089 prefixEnd_1163089 199074566985768380879519 := by
  unfold tailWord_1163089
  simp only [CollatzResearch.WordTrace]
  refine ⟨42421340883334667631788321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28280893922223111754525547 42421340883334667631788321)
  ·
    refine ⟨31816005662501000723841241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42421340883334667631788321 31816005662501000723841241)
    ·
      refine ⟨23862004246875750542880931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31816005662501000723841241 23862004246875750542880931)
      ·
        refine ⟨35793006370313625814321397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23862004246875750542880931 35793006370313625814321397)
        ·
          refine ⟨3355594347216902420092631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35793006370313625814321397 3355594347216902420092631)
          ·
            refine ⟨5033391520825353630138947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355594347216902420092631 5033391520825353630138947)
            ·
              refine ⟨7550087281238030445208421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033391520825353630138947 7550087281238030445208421)
              ·
                refine ⟨1415641365232130708476579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7550087281238030445208421 1415641365232130708476579)
                ·
                  refine ⟨2123462047848196062714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415641365232130708476579 2123462047848196062714869)
                  ·
                    refine ⟨199074566985768380879519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2123462047848196062714869 199074566985768380879519)
                    ·
                      rfl

theorem cell23_1163089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_1163089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163089 prefixEnd_1163089 := by exact prefixLift 1163089
  have htrace : WordTrace (prefixWord ++ tailWord_1163089) baseStart_1163089 baseEnd_1163089 := by
    simpa [prefixWord, tailWord_1163089, baseEnd_1163089] using wordTrace_append hprefix tailTrace_1163089
  have hstable : (prefixWord ++ tailWord_1163089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163089).length < 2 ^ (prefixWord ++ tailWord_1163089).sum := by decide
  have hdescent : baseEnd_1163089 < baseStart_1163089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163103 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 1, 1, 3]
def baseStart_1163103 : Nat := 118140960795 + 1163103 * 2 ^ 59
def prefixEnd_1163103 : Nat := 4983230072969 + 3 ^ 40 * 1163103 * 2
def baseEnd_1163103 : Nat := 597230889686468087863493

theorem tailTrace_1163103 : CollatzResearch.WordTrace tailWord_1163103 prefixEnd_1163103 597230889686468087863493 := by
  unfold tailWord_1163103
  simp only [CollatzResearch.WordTrace]
  refine ⟨42421851505283948022797963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28281234336855965348531975 42421851505283948022797963)
  ·
    refine ⟨63632777257925922034196945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42421851505283948022797963 63632777257925922034196945)
    ·
      refine ⟨47724582943444441525647709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63632777257925922034196945 47724582943444441525647709)
      ·
        refine ⟨17896718603791665572117891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47724582943444441525647709 17896718603791665572117891)
        ·
          refine ⟨26845077905687498358176837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17896718603791665572117891 26845077905687498358176837)
          ·
            refine ⟨5033452107316405942158157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26845077905687498358176837 5033452107316405942158157)
            ·
              refine ⟨1887544540243652228309309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5033452107316405942158157 1887544540243652228309309)
              ·
                refine ⟨707829202591369585615991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1887544540243652228309309 707829202591369585615991)
                ·
                  refine ⟨1061743803887054378423987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707829202591369585615991 1061743803887054378423987)
                  ·
                    refine ⟨1592615705830581567635981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061743803887054378423987 1592615705830581567635981)
                    ·
                      refine ⟨597230889686468087863493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1592615705830581567635981 597230889686468087863493)
                      ·
                        rfl

theorem cell23_1163103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_1163103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163103 prefixEnd_1163103 := by exact prefixLift 1163103
  have htrace : WordTrace (prefixWord ++ tailWord_1163103) baseStart_1163103 baseEnd_1163103 := by
    simpa [prefixWord, tailWord_1163103, baseEnd_1163103] using wordTrace_append hprefix tailTrace_1163103
  have hstable : (prefixWord ++ tailWord_1163103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163103).length < 2 ^ (prefixWord ++ tailWord_1163103).sum := by decide
  have hdescent : baseEnd_1163103 < baseStart_1163103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163106 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1163106 : Nat := 118140960795 + 1163106 * 2 ^ 59
def prefixEnd_1163106 : Nat := 4983230072969 + 3 ^ 40 * 1163106 * 2
def baseEnd_1163106 : Nat := 199077476709477192041993

theorem tailTrace_1163106 : CollatzResearch.WordTrace tailWord_1163106 prefixEnd_1163106 199077476709477192041993 := by
  unfold tailWord_1163106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605490231068269883789293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28281307282848719690104781 10605490231068269883789293)
  ·
    refine ⟨3977058836650601206420985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10605490231068269883789293 3977058836650601206420985)
    ·
      refine ⟨2982794127487950904815739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3977058836650601206420985 2982794127487950904815739)
      ·
        refine ⟨4474191191231926357223609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982794127487950904815739 4474191191231926357223609)
        ·
          refine ⟨3355643393423944767917707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4474191191231926357223609 3355643393423944767917707)
          ·
            refine ⟨5033465090135917151876561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355643393423944767917707 5033465090135917151876561)
            ·
              refine ⟨3775098817601937863907421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5033465090135917151876561 3775098817601937863907421)
              ·
                refine ⟨1415662056600726698965283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3775098817601937863907421 1415662056600726698965283)
                ·
                  refine ⟨2123493084901090048447925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415662056600726698965283 2123493084901090048447925)
                  ·
                    refine ⟨199077476709477192041993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2123493084901090048447925 199077476709477192041993)
                    ·
                      rfl

theorem cell23_1163106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1163106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163106 prefixEnd_1163106 := by exact prefixLift 1163106
  have htrace : WordTrace (prefixWord ++ tailWord_1163106) baseStart_1163106 baseEnd_1163106 := by
    simpa [prefixWord, tailWord_1163106, baseEnd_1163106] using wordTrace_append hprefix tailTrace_1163106
  have hstable : (prefixWord ++ tailWord_1163106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163106).length < 2 ^ (prefixWord ++ tailWord_1163106).sum := by decide
  have hdescent : baseEnd_1163106 < baseStart_1163106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163129 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_1163129 : Nat := 118140960795 + 1163129 * 2 ^ 59
def prefixEnd_1163129 : Nat := 4983230072969 + 3 ^ 40 * 1163129 * 2
def baseEnd_1163129 : Nat := 597244240183484986138373

theorem tailTrace_1163129 : CollatzResearch.WordTrace tailWord_1163129 prefixEnd_1163129 597244240183484986138373 := by
  unfold tailWord_1163129
  simp only [CollatzResearch.WordTrace]
  refine ⟨42422799803189754463244441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28281866535459836308829627 42422799803189754463244441)
  ·
    refine ⟨31817099852392315847433331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42422799803189754463244441 31817099852392315847433331)
    ·
      refine ⟨47725649778588473771149997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31817099852392315847433331 47725649778588473771149997)
      ·
        refine ⟨17897118666970677664181249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47725649778588473771149997 17897118666970677664181249)
        ·
          refine ⟨13422839000228008248135937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17897118666970677664181249 13422839000228008248135937)
          ·
            refine ⟨10067129250171006186101953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13422839000228008248135937 10067129250171006186101953)
            ·
              refine ⟨7550346937628254639576465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067129250171006186101953 7550346937628254639576465)
              ·
                refine ⟨5662760203221190979682349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550346937628254639576465 5662760203221190979682349)
                ·
                  refine ⟨2123535076207946617380881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5662760203221190979682349 2123535076207946617380881)
                  ·
                    refine ⟨1592651307155959963035661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123535076207946617380881 1592651307155959963035661)
                    ·
                      refine ⟨597244240183484986138373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1592651307155959963035661 597244240183484986138373)
                      ·
                        rfl

theorem cell23_1163129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_1163129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163129 prefixEnd_1163129 := by exact prefixLift 1163129
  have htrace : WordTrace (prefixWord ++ tailWord_1163129) baseStart_1163129 baseEnd_1163129 := by
    simpa [prefixWord, tailWord_1163129, baseEnd_1163129] using wordTrace_append hprefix tailTrace_1163129
  have hstable : (prefixWord ++ tailWord_1163129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163129).length < 2 ^ (prefixWord ++ tailWord_1163129).sum := by decide
  have hdescent : baseEnd_1163129 < baseStart_1163129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163143 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1163143 : Nat := 118140960795 + 1163143 * 2 ^ 59
def prefixEnd_1163143 : Nat := 4983230072969 + 3 ^ 40 * 1163143 * 2
def baseEnd_1163143 : Nat := 597251428912647931363309

theorem tailTrace_1163143 : CollatzResearch.WordTrace tailWord_1163143 prefixEnd_1163143 597251428912647931363309 := by
  unfold tailWord_1163143
  simp only [CollatzResearch.WordTrace]
  refine ⟨42423310425139034854254083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28282206950092689902836055 42423310425139034854254083)
  ·
    refine ⟨63634965637708552281381125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42423310425139034854254083 63634965637708552281381125)
    ·
      refine ⟨11931556057070353552758961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63634965637708552281381125 11931556057070353552758961)
      ·
        refine ⟨8948667042802765164569221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11931556057070353552758961 8948667042802765164569221)
        ·
          refine ⟨1677875070525518468356729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8948667042802765164569221 1677875070525518468356729)
          ·
            refine ⟨1258406302894138851267547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677875070525518468356729 1258406302894138851267547)
            ·
              refine ⟨1887609454341208276901321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258406302894138851267547 1887609454341208276901321)
              ·
                refine ⟨1415707090755906207675991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887609454341208276901321 1415707090755906207675991)
                ·
                  refine ⟨2123560636133859311513987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415707090755906207675991 2123560636133859311513987)
                  ·
                    refine ⟨3185340954200788967270981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2123560636133859311513987 3185340954200788967270981)
                    ·
                      refine ⟨597251428912647931363309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3185340954200788967270981 597251428912647931363309)
                      ·
                        rfl

theorem cell23_1163143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1163143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163143 prefixEnd_1163143 := by exact prefixLift 1163143
  have htrace : WordTrace (prefixWord ++ tailWord_1163143) baseStart_1163143 baseEnd_1163143 := by
    simpa [prefixWord, tailWord_1163143, baseEnd_1163143] using wordTrace_append hprefix tailTrace_1163143
  have hstable : (prefixWord ++ tailWord_1163143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163143).length < 2 ^ (prefixWord ++ tailWord_1163143).sum := by decide
  have hdescent : baseEnd_1163143 < baseStart_1163143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163156 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1163156 : Nat := 118140960795 + 1163156 * 2 ^ 59
def prefixEnd_1163156 : Nat := 4983230072969 + 3 ^ 40 * 1163156 * 2
def baseEnd_1163156 : Nat := 597258104161156380500749

theorem tailTrace_1163156 : CollatzResearch.WordTrace tailWord_1163156 prefixEnd_1163156 597258104161156380500749 := by
  unfold tailWord_1163156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21211892287045969037238661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28282523049394625382984881 21211892287045969037238661)
  ·
    refine ⟨3977229803821119194482249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21211892287045969037238661 3977229803821119194482249)
    ·
      refine ⟨2982922352865839395861687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3977229803821119194482249 2982922352865839395861687)
      ·
        refine ⟨4474383529298759093792531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982922352865839395861687 4474383529298759093792531)
        ·
          refine ⟨6711575293948138640688797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474383529298759093792531 6711575293948138640688797)
          ·
            refine ⟨2516840735230551990258299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6711575293948138640688797 2516840735230551990258299)
            ·
              refine ⟨3775261102845827985387449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516840735230551990258299 3775261102845827985387449)
              ·
                refine ⟨2831445827134370989040587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775261102845827985387449 2831445827134370989040587)
                ·
                  refine ⟨4247168740701556483560881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831445827134370989040587 4247168740701556483560881)
                  ·
                    refine ⟨3185376555526167362670661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247168740701556483560881 3185376555526167362670661)
                    ·
                      refine ⟨597258104161156380500749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3185376555526167362670661 597258104161156380500749)
                      ·
                        rfl

theorem cell23_1163156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1163156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163156 prefixEnd_1163156 := by exact prefixLift 1163156
  have htrace : WordTrace (prefixWord ++ tailWord_1163156) baseStart_1163156 baseEnd_1163156 := by
    simpa [prefixWord, tailWord_1163156, baseEnd_1163156] using wordTrace_append hprefix tailTrace_1163156
  have hstable : (prefixWord ++ tailWord_1163156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163156).length < 2 ^ (prefixWord ++ tailWord_1163156).sum := by decide
  have hdescent : baseEnd_1163156 < baseStart_1163156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163159 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1163159 : Nat := 118140960795 + 1163159 * 2 ^ 59
def prefixEnd_1163159 : Nat := 4983230072969 + 3 ^ 40 * 1163159 * 2
def baseEnd_1163159 : Nat := 597259644603119868763235

theorem tailTrace_1163159 : CollatzResearch.WordTrace tailWord_1163159 prefixEnd_1163159 597259644603119868763235 := by
  unfold tailWord_1163159
  simp only [CollatzResearch.WordTrace]
  refine ⟨42423893993081069586836531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28282595995387379724557687 42423893993081069586836531)
  ·
    refine ⟨63635840989621604380254797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42423893993081069586836531 63635840989621604380254797)
    ·
      refine ⟨23863440371108101642595549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63635840989621604380254797 23863440371108101642595549)
      ·
        refine ⟨8948790139165538115973331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23863440371108101642595549 8948790139165538115973331)
        ·
          refine ⟨13423185208748307173959997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8948790139165538115973331 13423185208748307173959997)
          ·
            refine ⟨5033694453280615190234999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13423185208748307173959997 5033694453280615190234999)
            ·
              refine ⟨7550541679920922785352499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033694453280615190234999 7550541679920922785352499)
              ·
                refine ⟨11325812519881384178028749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550541679920922785352499 11325812519881384178028749)
                ·
                  refine ⟨4247179694955519066760781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11325812519881384178028749 4247179694955519066760781)
                  ·
                    refine ⟨1592692385608319650035293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4247179694955519066760781 1592692385608319650035293)
                    ·
                      refine ⟨597259644603119868763235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1592692385608319650035293 597259644603119868763235)
                      ·
                        rfl

theorem cell23_1163159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1163159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163159 prefixEnd_1163159 := by exact prefixLift 1163159
  have htrace : WordTrace (prefixWord ++ tailWord_1163159) baseStart_1163159 baseEnd_1163159 := by
    simpa [prefixWord, tailWord_1163159, baseEnd_1163159] using wordTrace_append hprefix tailTrace_1163159
  have hstable : (prefixWord ++ tailWord_1163159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163159).length < 2 ^ (prefixWord ++ tailWord_1163159).sum := by decide
  have hdescent : baseEnd_1163159 < baseStart_1163159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163160 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1163160 : Nat := 118140960795 + 1163160 * 2 ^ 59
def prefixEnd_1163160 : Nat := 4983230072969 + 3 ^ 40 * 1163160 * 2
def baseEnd_1163160 : Nat := 597260158083774364850731

theorem tailTrace_1163160 : CollatzResearch.WordTrace tailWord_1163160 prefixEnd_1163160 597260158083774364850731 := by
  unfold tailWord_1163160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21211965233038723378811467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28282620310718297838415289 21211965233038723378811467)
  ·
    refine ⟨31817947849558085068217201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21211965233038723378811467 31817947849558085068217201)
    ·
      refine ⟨23863460887168563801162901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31817947849558085068217201 23863460887168563801162901)
      ·
        refine ⟨1118599729086026428179511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23863460887168563801162901 1118599729086026428179511)
        ·
          refine ⟨1677899593629039642269267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118599729086026428179511 1677899593629039642269267)
          ·
            refine ⟨2516849390443559463403901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677899593629039642269267 2516849390443559463403901)
            ·
              refine ⟨943818521416334798776463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2516849390443559463403901 943818521416334798776463)
              ·
                refine ⟨1415727782124502198164695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943818521416334798776463 1415727782124502198164695)
                ·
                  refine ⟨2123591673186753297247043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415727782124502198164695 2123591673186753297247043)
                  ·
                    refine ⟨3185387509780129945870565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2123591673186753297247043 3185387509780129945870565)
                    ·
                      refine ⟨597260158083774364850731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3185387509780129945870565 597260158083774364850731)
                      ·
                        rfl

theorem cell23_1163160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1163160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163160 prefixEnd_1163160 := by exact prefixLift 1163160
  have htrace : WordTrace (prefixWord ++ tailWord_1163160) baseStart_1163160 baseEnd_1163160 := by
    simpa [prefixWord, tailWord_1163160, baseEnd_1163160] using wordTrace_append hprefix tailTrace_1163160
  have hstable : (prefixWord ++ tailWord_1163160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163160).length < 2 ^ (prefixWord ++ tailWord_1163160).sum := by decide
  have hdescent : baseEnd_1163160 < baseStart_1163160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163166 : List Nat := [4, 3, 1, 3, 1, 11]
def baseStart_1163166 : Nat := 118140960795 + 1163166 * 2 ^ 59
def prefixEnd_1163166 : Nat := 4983230072969 + 3 ^ 40 * 1163166 * 2
def baseEnd_1163166 : Nat := 2457873411389717454221

theorem tailTrace_1163166 : CollatzResearch.WordTrace tailWord_1163166 prefixEnd_1163166 2457873411389717454221 := by
  unfold tailWord_1163166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303018663006963722792669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28282766202703806521560901 5303018663006963722792669)
  ·
    refine ⟨1988631998627611396047251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5303018663006963722792669 1988631998627611396047251)
    ·
      refine ⟨2982947997941417094070877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1988631998627611396047251 2982947997941417094070877)
      ·
        refine ⟨1118605499228031410276579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2982947997941417094070877 1118605499228031410276579)
        ·
          refine ⟨1677908248842047115414869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118605499228031410276579 1677908248842047115414869)
          ·
            refine ⟨2457873411389717454221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1677908248842047115414869 2457873411389717454221)
            ·
              rfl

theorem cell23_1163166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 11].length) (baseStart_1163166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163166 prefixEnd_1163166 := by exact prefixLift 1163166
  have htrace : WordTrace (prefixWord ++ tailWord_1163166) baseStart_1163166 baseEnd_1163166 := by
    simpa [prefixWord, tailWord_1163166, baseEnd_1163166] using wordTrace_append hprefix tailTrace_1163166
  have hstable : (prefixWord ++ tailWord_1163166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163166).length < 2 ^ (prefixWord ++ tailWord_1163166).sum := by decide
  have hdescent : baseEnd_1163166 < baseStart_1163166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163216 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2]
def baseStart_1163216 : Nat := 118140960795 + 1163216 * 2 ^ 59
def prefixEnd_1163216 : Nat := 4983230072969 + 3 ^ 40 * 1163216 * 2
def baseEnd_1163216 : Nat := 597288913000426145750473

theorem tailTrace_1163216 : CollatzResearch.WordTrace tailWord_1163216 prefixEnd_1163216 597288913000426145750473 := by
  unfold tailWord_1163216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21212986476937284160830751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28283981969249712214441001 21212986476937284160830751)
  ·
    refine ⟨31819479715405926241246127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21212986476937284160830751 31819479715405926241246127)
    ·
      refine ⟨47729219573108889361869191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31819479715405926241246127 47729219573108889361869191)
      ·
        refine ⟨71593829359663334042803787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47729219573108889361869191 71593829359663334042803787)
        ·
          refine ⟨107390744039495001064205681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71593829359663334042803787 107390744039495001064205681)
          ·
            refine ⟨80543058029621250798154261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107390744039495001064205681 80543058029621250798154261)
            ·
              refine ⟨3775455845138496131163481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80543058029621250798154261 3775455845138496131163481)
              ·
                refine ⟨2831591883853872098372611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775455845138496131163481 2831591883853872098372611)
                ·
                  refine ⟨4247387825780808147558917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831591883853872098372611 4247387825780808147558917)
                  ·
                    refine ⟨796385217333901527667297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4247387825780808147558917 796385217333901527667297)
                    ·
                      refine ⟨597288913000426145750473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796385217333901527667297 597288913000426145750473)
                      ·
                        rfl

theorem cell23_1163216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2].length) (baseStart_1163216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163216 prefixEnd_1163216 := by exact prefixLift 1163216
  have htrace : WordTrace (prefixWord ++ tailWord_1163216) baseStart_1163216 baseEnd_1163216 := by
    simpa [prefixWord, tailWord_1163216, baseEnd_1163216] using wordTrace_append hprefix tailTrace_1163216
  have hstable : (prefixWord ++ tailWord_1163216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163216).length < 2 ^ (prefixWord ++ tailWord_1163216).sum := by decide
  have hdescent : baseEnd_1163216 < baseStart_1163216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163246 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1163246 : Nat := 118140960795 + 1163246 * 2 ^ 59
def prefixEnd_1163246 : Nat := 4983230072969 + 3 ^ 40 * 1163246 * 2
def baseEnd_1163246 : Nat := 597304317420061028375335

theorem tailTrace_1163246 : CollatzResearch.WordTrace tailWord_1163246 prefixEnd_1163246 597304317420061028375335 := by
  unfold tailWord_1163246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303383392970735430656699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28284711429177255630169061 5303383392970735430656699)
  ·
    refine ⟨7955075089456103145985049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5303383392970735430656699 7955075089456103145985049)
    ·
      refine ⟨5966306317092077359488787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7955075089456103145985049 5966306317092077359488787)
      ·
        refine ⟨8949459475638116039233181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966306317092077359488787 8949459475638116039233181)
        ·
          refine ⟨3356047303364293514712443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8949459475638116039233181 3356047303364293514712443)
          ·
            refine ⟨5034070955046440272068665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356047303364293514712443 5034070955046440272068665)
            ·
              refine ⟨3775553216284830204051499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034070955046440272068665 3775553216284830204051499)
              ·
                refine ⟨5663329824427245306077249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775553216284830204051499 5663329824427245306077249)
                ·
                  refine ⟨4247497368320433979557937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663329824427245306077249 4247497368320433979557937)
                  ·
                    refine ⟨3185623026240325484668453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247497368320433979557937 3185623026240325484668453)
                    ·
                      refine ⟨597304317420061028375335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3185623026240325484668453 597304317420061028375335)
                      ·
                        rfl

theorem cell23_1163246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1163246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163246 prefixEnd_1163246 := by exact prefixLift 1163246
  have htrace : WordTrace (prefixWord ++ tailWord_1163246) baseStart_1163246 baseEnd_1163246 := by
    simpa [prefixWord, tailWord_1163246, baseEnd_1163246] using wordTrace_append hprefix tailTrace_1163246
  have hstable : (prefixWord ++ tailWord_1163246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163246).length < 2 ^ (prefixWord ++ tailWord_1163246).sum := by decide
  have hdescent : baseEnd_1163246 < baseStart_1163246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163269 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_1163269 : Nat := 118140960795 + 1163269 * 2 ^ 59
def prefixEnd_1163269 : Nat := 4983230072969 + 3 ^ 40 * 1163269 * 2
def baseEnd_1163269 : Nat := 199105375825038146129243

theorem tailTrace_1163269 : CollatzResearch.WordTrace tailWord_1163269 prefixEnd_1163269 199105375825038146129243 := by
  unfold tailWord_1163269
  simp only [CollatzResearch.WordTrace]
  refine ⟨42427906022682558373340861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28285270681788372248893907 42427906022682558373340861)
  ·
    refine ⟨15910464758505959390002823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42427906022682558373340861 15910464758505959390002823)
    ·
      refine ⟨23865697137758939085004235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15910464758505959390002823 23865697137758939085004235)
      ·
        refine ⟨35798545706638408627506353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23865697137758939085004235 35798545706638408627506353)
        ·
          refine ⟨26848909279978806470629765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35798545706638408627506353 26848909279978806470629765)
          ·
            refine ⟨5034170489996026213243081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26848909279978806470629765 5034170489996026213243081)
            ·
              refine ⟨3775627867497019659932311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034170489996026213243081 3775627867497019659932311)
              ·
                refine ⟨5663441801245529489898467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775627867497019659932311 5663441801245529489898467)
                ·
                  refine ⟨8495162701868294234847701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5663441801245529489898467 8495162701868294234847701)
                  ·
                    refine ⟨199105375825038146129243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8495162701868294234847701 199105375825038146129243)
                    ·
                      rfl

theorem cell23_1163269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_1163269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163269 prefixEnd_1163269 := by exact prefixLift 1163269
  have htrace : WordTrace (prefixWord ++ tailWord_1163269) baseStart_1163269 baseEnd_1163269 := by
    simpa [prefixWord, tailWord_1163269, baseEnd_1163269] using wordTrace_append hprefix tailTrace_1163269
  have hstable : (prefixWord ++ tailWord_1163269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163269).length < 2 ^ (prefixWord ++ tailWord_1163269).sum := by decide
  have hdescent : baseEnd_1163269 < baseStart_1163269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163319 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1163319 : Nat := 118140960795 + 1163319 * 2 ^ 59
def prefixEnd_1163319 : Nat := 4983230072969 + 3 ^ 40 * 1163319 * 2
def baseEnd_1163319 : Nat := 597341801507839242762499

theorem tailTrace_1163319 : CollatzResearch.WordTrace tailWord_1163319 prefixEnd_1163319 597341801507839242762499 := by
  unfold tailWord_1163319
  simp only [CollatzResearch.WordTrace]
  refine ⟨42429729672501416912661011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28286486448334277941774007 42429729672501416912661011)
  ·
    refine ⟨63644594508752125368991517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42429729672501416912661011 63644594508752125368991517)
    ·
      refine ⟨23866722940782047013371819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63644594508752125368991517 23866722940782047013371819)
      ·
        refine ⟨35800084411173070520057729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23866722940782047013371819 35800084411173070520057729)
        ·
          refine ⟨26850063308379802890043297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35800084411173070520057729 26850063308379802890043297)
          ·
            refine ⟨20137547481284852167532473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26850063308379802890043297 20137547481284852167532473)
            ·
              refine ⟨15103160610963639125649355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20137547481284852167532473 15103160610963639125649355)
              ·
                refine ⟨22654740916445458688474033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15103160610963639125649355 22654740916445458688474033)
                ·
                  refine ⟨16991055687334094016355525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22654740916445458688474033 16991055687334094016355525)
                  ·
                    refine ⟨3185822941375142628066661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16991055687334094016355525 3185822941375142628066661)
                    ·
                      refine ⟨597341801507839242762499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3185822941375142628066661 597341801507839242762499)
                      ·
                        rfl

theorem cell23_1163319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1163319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163319 prefixEnd_1163319 := by exact prefixLift 1163319
  have htrace : WordTrace (prefixWord ++ tailWord_1163319) baseStart_1163319 baseEnd_1163319 := by
    simpa [prefixWord, tailWord_1163319, baseEnd_1163319] using wordTrace_append hprefix tailTrace_1163319
  have hstable : (prefixWord ++ tailWord_1163319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163319).length < 2 ^ (prefixWord ++ tailWord_1163319).sum := by decide
  have hdescent : baseEnd_1163319 < baseStart_1163319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163333 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_1163333 : Nat := 118140960795 + 1163333 * 2 ^ 59
def prefixEnd_1163333 : Nat := 4983230072969 + 3 ^ 40 * 1163333 * 2
def baseEnd_1163333 : Nat := 199116330079000729329145

theorem tailTrace_1163333 : CollatzResearch.WordTrace tailWord_1163333 prefixEnd_1163333 199116330079000729329145 := by
  unfold tailWord_1163333
  simp only [CollatzResearch.WordTrace]
  refine ⟨42430240294450697303670653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28286826862967131535780435 42430240294450697303670653)
  ·
    refine ⟨15911340110419011488876495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42430240294450697303670653 15911340110419011488876495)
    ·
      refine ⟨23867010165628517233314743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15911340110419011488876495 23867010165628517233314743)
      ·
        refine ⟨35800515248442775849972115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23867010165628517233314743 35800515248442775849972115)
        ·
          refine ⟨53700772872664163774958173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35800515248442775849972115 53700772872664163774958173)
          ·
            refine ⟨20137789827249061415609315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53700772872664163774958173 20137789827249061415609315)
            ·
              refine ⟨30206684740873592123413973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20137789827249061415609315 30206684740873592123413973)
              ·
                refine ⟨707969173614224815392515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30206684740873592123413973 707969173614224815392515)
                ·
                  refine ⟨1061953760421337223088773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707969173614224815392515 1061953760421337223088773)
                  ·
                    refine ⟨199116330079000729329145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1061953760421337223088773 199116330079000729329145)
                    ·
                      rfl

theorem cell23_1163333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_1163333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163333 prefixEnd_1163333 := by exact prefixLift 1163333
  have htrace : WordTrace (prefixWord ++ tailWord_1163333) baseStart_1163333 baseEnd_1163333 := by
    simpa [prefixWord, tailWord_1163333, baseEnd_1163333] using wordTrace_append hprefix tailTrace_1163333
  have hstable : (prefixWord ++ tailWord_1163333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163333).length < 2 ^ (prefixWord ++ tailWord_1163333).sum := by decide
  have hdescent : baseEnd_1163333 < baseStart_1163333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163369 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_1163369 : Nat := 118140960795 + 1163369 * 2 ^ 59
def prefixEnd_1163369 : Nat := 4983230072969 + 3 ^ 40 * 1163369 * 2
def baseEnd_1163369 : Nat := 597367475540564047137269

theorem tailTrace_1163369 : CollatzResearch.WordTrace tailWord_1163369 prefixEnd_1163369 597367475540564047137269 := by
  unfold tailWord_1163369
  simp only [CollatzResearch.WordTrace]
  refine ⟨42431553322320275451981161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28287702214880183634654107 42431553322320275451981161)
  ·
    refine ⟨31823664991740206588985871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42431553322320275451981161 31823664991740206588985871)
    ·
      refine ⟨47735497487610309883478807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31823664991740206588985871 47735497487610309883478807)
      ·
        refine ⟨71603246231415464825218211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47735497487610309883478807 71603246231415464825218211)
        ·
          refine ⟨107404869347123197237827317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71603246231415464825218211 107404869347123197237827317)
          ·
            refine ⟨10069206501292799741046311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107404869347123197237827317 10069206501292799741046311)
            ·
              refine ⟨15103809751939199611569467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10069206501292799741046311 15103809751939199611569467)
              ·
                refine ⟨22655714627908799417354201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15103809751939199611569467 22655714627908799417354201)
                ·
                  refine ⟨16991785970931599563015651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22655714627908799417354201 16991785970931599563015651)
                  ·
                    refine ⟨25487678956397399344523477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16991785970931599563015651 25487678956397399344523477)
                    ·
                      refine ⟨597367475540564047137269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25487678956397399344523477 597367475540564047137269)
                      ·
                        rfl

theorem cell23_1163369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_1163369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163369 prefixEnd_1163369 := by exact prefixLift 1163369
  have htrace : WordTrace (prefixWord ++ tailWord_1163369) baseStart_1163369 baseEnd_1163369 := by
    simpa [prefixWord, tailWord_1163369, baseEnd_1163369] using wordTrace_append hprefix tailTrace_1163369
  have hstable : (prefixWord ++ tailWord_1163369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163369).length < 2 ^ (prefixWord ++ tailWord_1163369).sum := by decide
  have hdescent : baseEnd_1163369 < baseStart_1163369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163376 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_1163376 : Nat := 118140960795 + 1163376 * 2 ^ 59
def prefixEnd_1163376 : Nat := 4983230072969 + 3 ^ 40 * 1163376 * 2
def baseEnd_1163376 : Nat := 199123689968381839916579

theorem tailTrace_1163376 : CollatzResearch.WordTrace tailWord_1163376 prefixEnd_1163376 199123689968381839916579 := by
  unfold tailWord_1163376
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215904316647457823742991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28287872422196610431657321 21215904316647457823742991)
  ·
    refine ⟨31823856474971186735614487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21215904316647457823742991 31823856474971186735614487)
    ·
      refine ⟨47735784712456780103421731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31823856474971186735614487 47735784712456780103421731)
      ·
        refine ⟨71603677068685170155132597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47735784712456780103421731 71603677068685170155132597)
        ·
          refine ⟨6712844725189234702043681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71603677068685170155132597 6712844725189234702043681)
          ·
            refine ⟨5034633543891926026532761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6712844725189234702043681 5034633543891926026532761)
            ·
              refine ⟨3775975157918944519899571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034633543891926026532761 3775975157918944519899571)
              ·
                refine ⟨5663962736878416779849357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775975157918944519899571 5663962736878416779849357)
                ·
                  refine ⟨2123986026329406292443509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5663962736878416779849357 2123986026329406292443509)
                  ·
                    refine ⟨199123689968381839916579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2123986026329406292443509 199123689968381839916579)
                    ·
                      rfl

theorem cell23_1163376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_1163376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163376 prefixEnd_1163376 := by exact prefixLift 1163376
  have htrace : WordTrace (prefixWord ++ tailWord_1163376) baseStart_1163376 baseEnd_1163376 := by
    simpa [prefixWord, tailWord_1163376, baseEnd_1163376] using wordTrace_append hprefix tailTrace_1163376
  have hstable : (prefixWord ++ tailWord_1163376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163376).length < 2 ^ (prefixWord ++ tailWord_1163376).sum := by decide
  have hdescent : baseEnd_1163376 < baseStart_1163376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163383 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_1163383 : Nat := 118140960795 + 1163383 * 2 ^ 59
def prefixEnd_1163383 : Nat := 4983230072969 + 3 ^ 40 * 1163383 * 2
def baseEnd_1163383 : Nat := 597374664269726992362205

theorem tailTrace_1163383 : CollatzResearch.WordTrace tailWord_1163383 prefixEnd_1163383 597374664269726992362205 := by
  unfold tailWord_1163383
  simp only [CollatzResearch.WordTrace]
  refine ⟨42432063944269555842990803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28288042629513037228660535 42432063944269555842990803)
  ·
    refine ⟨63648095916404333764486205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42432063944269555842990803 63648095916404333764486205)
    ·
      refine ⟨23868035968651625161682327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63648095916404333764486205 23868035968651625161682327)
      ·
        refine ⟨35802053952977437742523491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23868035968651625161682327 35802053952977437742523491)
        ·
          refine ⟨53703080929466156613785237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35802053952977437742523491 53703080929466156613785237)
          ·
            refine ⟨2517331918568726091271183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53703080929466156613785237 2517331918568726091271183)
            ·
              refine ⟨3775997877853089136906775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517331918568726091271183 3775997877853089136906775)
              ·
                refine ⟨5663996816779633705360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775997877853089136906775 5663996816779633705360163)
                ·
                  refine ⟨8495995225169450558040245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5663996816779633705360163 8495995225169450558040245)
                  ·
                    refine ⟨796499552359635989816273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8495995225169450558040245 796499552359635989816273)
                    ·
                      refine ⟨597374664269726992362205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796499552359635989816273 597374664269726992362205)
                      ·
                        rfl

theorem cell23_1163383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_1163383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163383 prefixEnd_1163383 := by exact prefixLift 1163383
  have htrace : WordTrace (prefixWord ++ tailWord_1163383) baseStart_1163383 baseEnd_1163383 := by
    simpa [prefixWord, tailWord_1163383, baseEnd_1163383] using wordTrace_append hprefix tailTrace_1163383
  have hstable : (prefixWord ++ tailWord_1163383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163383).length < 2 ^ (prefixWord ++ tailWord_1163383).sum := by decide
  have hdescent : baseEnd_1163383 < baseStart_1163383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163423 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 1, 6]
def baseStart_1163423 : Nat := 118140960795 + 1163423 * 2 ^ 59
def prefixEnd_1163423 : Nat := 4983230072969 + 3 ^ 40 * 1163423 * 2
def baseEnd_1163423 : Nat := 199131734498635611954007

theorem tailTrace_1163423 : CollatzResearch.WordTrace tailWord_1163423 prefixEnd_1163423 199131734498635611954007 := by
  unfold tailWord_1163423
  simp only [CollatzResearch.WordTrace]
  refine ⟨42433522864124642674446923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28289015242749761782964615 42433522864124642674446923)
  ·
    refine ⟨63650284296186964011670385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42433522864124642674446923 63650284296186964011670385)
    ·
      refine ⟨47737713222140223008752789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63650284296186964011670385 47737713222140223008752789)
      ·
        refine ⟨2237705307287822953535287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47737713222140223008752789 2237705307287822953535287)
        ·
          refine ⟨3356557960931734430302931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237705307287822953535287 3356557960931734430302931)
          ·
            refine ⟨5034836941397601645454397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356557960931734430302931 5034836941397601645454397)
            ·
              refine ⟨1888063853024100617045399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5034836941397601645454397 1888063853024100617045399)
              ·
                refine ⟨2832095779536150925568099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1888063853024100617045399 2832095779536150925568099)
                ·
                  refine ⟨4248143669304226388352149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832095779536150925568099 4248143669304226388352149)
                  ·
                    refine ⟨199131734498635611954007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4248143669304226388352149 199131734498635611954007)
                    ·
                      rfl

theorem cell23_1163423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_1163423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163423 prefixEnd_1163423 := by exact prefixLift 1163423
  have htrace : WordTrace (prefixWord ++ tailWord_1163423) baseStart_1163423 baseEnd_1163423 := by
    simpa [prefixWord, tailWord_1163423, baseEnd_1163423] using wordTrace_append hprefix tailTrace_1163423
  have hstable : (prefixWord ++ tailWord_1163423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163423).length < 2 ^ (prefixWord ++ tailWord_1163423).sum := by decide
  have hdescent : baseEnd_1163423 < baseStart_1163423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163441 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1163441 : Nat := 118140960795 + 1163441 * 2 ^ 59
def prefixEnd_1163441 : Nat := 4983230072969 + 3 ^ 40 * 1163441 * 2
def baseEnd_1163441 : Nat := 597404446147687765436939

theorem tailTrace_1163441 : CollatzResearch.WordTrace tailWord_1163441 prefixEnd_1163441 597404446147687765436939 := by
  unfold tailWord_1163441
  simp only [CollatzResearch.WordTrace]
  refine ⟨42434179378059431748602177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28289452918706287832401451 42434179378059431748602177)
  ·
    refine ⟨31825634533544573811451633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42434179378059431748602177 31825634533544573811451633)
    ·
      refine ⟨23869225900158430358588725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31825634533544573811451633 23869225900158430358588725)
      ·
        refine ⟨2237739928139852846117693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23869225900158430358588725 2237739928139852846117693)
        ·
          refine ⟨839152473052444817294135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2237739928139852846117693 839152473052444817294135)
          ·
            refine ⟨1258728709578667225941203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839152473052444817294135 1258728709578667225941203)
            ·
              refine ⟨1888093064368000838911805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258728709578667225941203 1888093064368000838911805)
              ·
                refine ⟨708034899138000314591927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888093064368000838911805 708034899138000314591927)
                ·
                  refine ⟨1062052348707000471887891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708034899138000314591927 1062052348707000471887891)
                  ·
                    refine ⟨1593078523060500707831837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1062052348707000471887891 1593078523060500707831837)
                    ·
                      refine ⟨597404446147687765436939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1593078523060500707831837 597404446147687765436939)
                      ·
                        rfl

theorem cell23_1163441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1163441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163441 prefixEnd_1163441 := by exact prefixLift 1163441
  have htrace : WordTrace (prefixWord ++ tailWord_1163441) baseStart_1163441 baseEnd_1163441 := by
    simpa [prefixWord, tailWord_1163441, baseEnd_1163441] using wordTrace_append hprefix tailTrace_1163441
  have hstable : (prefixWord ++ tailWord_1163441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163441).length < 2 ^ (prefixWord ++ tailWord_1163441).sum := by decide
  have hdescent : baseEnd_1163441 < baseStart_1163441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163458 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1163458 : Nat := 118140960795 + 1163458 * 2 ^ 59
def prefixEnd_1163458 : Nat := 4983230072969 + 3 ^ 40 * 1163458 * 2
def baseEnd_1163458 : Nat := 597413175318814198924361

theorem tailTrace_1163458 : CollatzResearch.WordTrace tailWord_1163458 prefixEnd_1163458 597413175318814198924361 := by
  unfold tailWord_1163458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608699854749460912992757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28289866279331895767980685 10608699854749460912992757)
  ·
    refine ⟨994565611382761960593071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10608699854749460912992757 994565611382761960593071)
    ·
      refine ⟨1491848417074142940889607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994565611382761960593071 1491848417074142940889607)
      ·
        refine ⟨2237772625611214411334411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491848417074142940889607 2237772625611214411334411)
        ·
          refine ⟨3356658938416821617001617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237772625611214411334411 3356658938416821617001617)
          ·
            refine ⟨2517494203812616212751213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356658938416821617001617 2517494203812616212751213)
            ·
              refine ⟨944060326429731079781705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517494203812616212751213 944060326429731079781705)
              ·
                refine ⟨708045244822298309836279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944060326429731079781705 708045244822298309836279)
                ·
                  refine ⟨1062067867233447464754419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708045244822298309836279 1062067867233447464754419)
                  ·
                    refine ⟨1593101800850171197131629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1062067867233447464754419 1593101800850171197131629)
                    ·
                      refine ⟨597413175318814198924361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1593101800850171197131629 597413175318814198924361)
                      ·
                        rfl

theorem cell23_1163458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1163458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163458 prefixEnd_1163458 := by exact prefixLift 1163458
  have htrace : WordTrace (prefixWord ++ tailWord_1163458) baseStart_1163458 baseEnd_1163458 := by
    simpa [prefixWord, tailWord_1163458, baseEnd_1163458] using wordTrace_append hprefix tailTrace_1163458
  have hstable : (prefixWord ++ tailWord_1163458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163458).length < 2 ^ (prefixWord ++ tailWord_1163458).sum := by decide
  have hdescent : baseEnd_1163458 < baseStart_1163458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163466 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1163466 : Nat := 118140960795 + 1163466 * 2 ^ 59
def prefixEnd_1163466 : Nat := 4983230072969 + 3 ^ 40 * 1163466 * 2
def baseEnd_1163466 : Nat := 199139094388016722541441

theorem tailTrace_1163466 : CollatzResearch.WordTrace tailWord_1163466 prefixEnd_1163466 199139094388016722541441 := by
  unfold tailWord_1163466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608772800742215254565563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28290060801979240678841501 10608772800742215254565563)
  ·
    refine ⟨15913159201113322881848345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608772800742215254565563 15913159201113322881848345)
    ·
      refine ⟨11934869400834992161386259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15913159201113322881848345 11934869400834992161386259)
      ·
        refine ⟨17902304101252488242079389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11934869400834992161386259 17902304101252488242079389)
        ·
          refine ⟨6713364037969683090779771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17902304101252488242079389 6713364037969683090779771)
          ·
            refine ⟨10070046056954524636169657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713364037969683090779771 10070046056954524636169657)
            ·
              refine ⟨7552534542715893477127243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10070046056954524636169657 7552534542715893477127243)
              ·
                refine ⟨11328801814073840215690865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7552534542715893477127243 11328801814073840215690865)
                ·
                  refine ⟨8496601360555380161768149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11328801814073840215690865 8496601360555380161768149)
                  ·
                    refine ⟨199139094388016722541441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8496601360555380161768149 199139094388016722541441)
                    ·
                      rfl

theorem cell23_1163466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1163466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163466 prefixEnd_1163466 := by exact prefixLift 1163466
  have htrace : WordTrace (prefixWord ++ tailWord_1163466) baseStart_1163466 baseEnd_1163466 := by
    simpa [prefixWord, tailWord_1163466, baseEnd_1163466] using wordTrace_append hprefix tailTrace_1163466
  have hstable : (prefixWord ++ tailWord_1163466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163466).length < 2 ^ (prefixWord ++ tailWord_1163466).sum := by decide
  have hdescent : baseEnd_1163466 < baseStart_1163466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163507 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 1, 3, 2]
def baseStart_1163507 : Nat := 118140960795 + 1163507 * 2 ^ 59
def prefixEnd_1163507 : Nat := 4983230072969 + 3 ^ 40 * 1163507 * 2
def baseEnd_1163507 : Nat := 597438335870884507211635

theorem tailTrace_1163507 : CollatzResearch.WordTrace tailWord_1163507 prefixEnd_1163507 597438335870884507211635 := by
  unfold tailWord_1163507
  simp only [CollatzResearch.WordTrace]
  refine ⟨42436586595820325020504775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28291057730546883347003183 42436586595820325020504775)
  ·
    refine ⟨63654879893730487530757163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42436586595820325020504775 63654879893730487530757163)
    ·
      refine ⟨95482319840595731296135745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63654879893730487530757163 95482319840595731296135745)
      ·
        refine ⟨71611739880446798472101809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95482319840595731296135745 71611739880446798472101809)
        ·
          refine ⟨53708804910335098854076357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71611739880446798472101809 53708804910335098854076357)
          ·
            refine ⟨10070400920687831035139317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53708804910335098854076357 10070400920687831035139317)
            ·
              refine ⟨944100086314484159544311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10070400920687831035139317 944100086314484159544311)
              ·
                refine ⟨1416150129471726239316467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944100086314484159544311 1416150129471726239316467)
                ·
                  refine ⟨2124225194207589358974701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416150129471726239316467 2124225194207589358974701)
                  ·
                    refine ⟨796584447827846009615513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124225194207589358974701 796584447827846009615513)
                    ·
                      refine ⟨597438335870884507211635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796584447827846009615513 597438335870884507211635)
                      ·
                        rfl

theorem cell23_1163507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 3, 2].length) (baseStart_1163507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163507 prefixEnd_1163507 := by exact prefixLift 1163507
  have htrace : WordTrace (prefixWord ++ tailWord_1163507) baseStart_1163507 baseEnd_1163507 := by
    simpa [prefixWord, tailWord_1163507, baseEnd_1163507] using wordTrace_append hprefix tailTrace_1163507
  have hstable : (prefixWord ++ tailWord_1163507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163507).length < 2 ^ (prefixWord ++ tailWord_1163507).sum := by decide
  have hdescent : baseEnd_1163507 < baseStart_1163507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163520 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2]
def baseStart_1163520 : Nat := 118140960795 + 1163520 * 2 ^ 59
def prefixEnd_1163520 : Nat := 4983230072969 + 3 ^ 40 * 1163520 * 2
def baseEnd_1163520 : Nat := 597445011119392956349075

theorem tailTrace_1163520 : CollatzResearch.WordTrace tailWord_1163520 prefixEnd_1163520 597445011119392956349075 := by
  unfold tailWord_1163520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218530372386614120364007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28291373829848818827152009 21218530372386614120364007)
  ·
    refine ⟨31827795558579921180546011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21218530372386614120364007 31827795558579921180546011)
    ·
      refine ⟨47741693337869881770819017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31827795558579921180546011 47741693337869881770819017)
      ·
        refine ⟨35806270003402411328114263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47741693337869881770819017 35806270003402411328114263)
        ·
          refine ⟨53709405005103616992171395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35806270003402411328114263 53709405005103616992171395)
          ·
            refine ⟨80564107507655425488257093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53709405005103616992171395 80564107507655425488257093)
            ·
              refine ⟨15105770157685392279048205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80564107507655425488257093 15105770157685392279048205)
              ·
                refine ⟨5664663809132022104643077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15105770157685392279048205 5664663809132022104643077)
                ·
                  refine ⟨1062124464212254144620577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5664663809132022104643077 1062124464212254144620577)
                  ·
                    refine ⟨796593348159190608465433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1062124464212254144620577 796593348159190608465433)
                    ·
                      refine ⟨597445011119392956349075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796593348159190608465433 597445011119392956349075)
                      ·
                        rfl

theorem cell23_1163520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_1163520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163520 prefixEnd_1163520 := by exact prefixLift 1163520
  have htrace : WordTrace (prefixWord ++ tailWord_1163520) baseStart_1163520 baseEnd_1163520 := by
    simpa [prefixWord, tailWord_1163520, baseEnd_1163520] using wordTrace_append hprefix tailTrace_1163520
  have hstable : (prefixWord ++ tailWord_1163520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163520).length < 2 ^ (prefixWord ++ tailWord_1163520).sum := by decide
  have hdescent : baseEnd_1163520 < baseStart_1163520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163537 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_1163537 : Nat := 118140960795 + 1163537 * 2 ^ 59
def prefixEnd_1163537 : Nat := 4983230072969 + 3 ^ 40 * 1163537 * 2
def baseEnd_1163537 : Nat := 597453740290519389836497

theorem tailTrace_1163537 : CollatzResearch.WordTrace tailWord_1163537 prefixEnd_1163537 597453740290519389836497 := by
  unfold tailWord_1163537
  simp only [CollatzResearch.WordTrace]
  refine ⟨42437680785711640144096865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28291787190474426762731243 42437680785711640144096865)
  ·
    refine ⟨31828260589283730108072649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42437680785711640144096865 31828260589283730108072649)
    ·
      refine ⟨23871195441962797581054487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31828260589283730108072649 23871195441962797581054487)
      ·
        refine ⟨35806793162944196371581731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23871195441962797581054487 35806793162944196371581731)
        ·
          refine ⟨53710189744416294557372597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35806793162944196371581731 53710189744416294557372597)
          ·
            refine ⟨5035330288539027614753681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53710189744416294557372597 5035330288539027614753681)
            ·
              refine ⟨3776497716404270711065261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5035330288539027614753681 3776497716404270711065261)
              ·
                refine ⟨1416186643651601516649473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3776497716404270711065261 1416186643651601516649473)
                ·
                  refine ⟨1062139982738701137487105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416186643651601516649473 1062139982738701137487105)
                  ·
                    refine ⟨796604987054025853115329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1062139982738701137487105 796604987054025853115329)
                    ·
                      refine ⟨597453740290519389836497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796604987054025853115329 597453740290519389836497)
                      ·
                        rfl

theorem cell23_1163537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_1163537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163537 prefixEnd_1163537 := by exact prefixLift 1163537
  have htrace : WordTrace (prefixWord ++ tailWord_1163537) baseStart_1163537 baseEnd_1163537 := by
    simpa [prefixWord, tailWord_1163537, baseEnd_1163537] using wordTrace_append hprefix tailTrace_1163537
  have hstable : (prefixWord ++ tailWord_1163537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163537).length < 2 ^ (prefixWord ++ tailWord_1163537).sum := by decide
  have hdescent : baseEnd_1163537 < baseStart_1163537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163543 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 7]
def baseStart_1163543 : Nat := 118140960795 + 1163543 * 2 ^ 59
def prefixEnd_1163543 : Nat := 4983230072969 + 3 ^ 40 * 1163543 * 2
def baseEnd_1163543 : Nat := 66384091241605151817941

theorem tailTrace_1163543 : CollatzResearch.WordTrace tailWord_1163543 prefixEnd_1163543 66384091241605151817941 := by
  unfold tailWord_1163543
  simp only [CollatzResearch.WordTrace]
  refine ⟨42437899623689903168815283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28291933082459935445876855 42437899623689903168815283)
  ·
    refine ⟨63656849435534854753222925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42437899623689903168815283 63656849435534854753222925)
    ·
      refine ⟨23871318538325570532458597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63656849435534854753222925 23871318538325570532458597)
      ·
        refine ⟨4475872225936044474835987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23871318538325570532458597 4475872225936044474835987)
        ·
          refine ⟨6713808338904066712253981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475872225936044474835987 6713808338904066712253981)
          ·
            refine ⟨2517678127089025017095243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6713808338904066712253981 2517678127089025017095243)
            ·
              refine ⟨3776517190633537525642865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517678127089025017095243 3776517190633537525642865)
              ·
                refine ⟨2832387892975153144232149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776517190633537525642865 2832387892975153144232149)
                ·
                  refine ⟨66384091241605151817941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2832387892975153144232149 66384091241605151817941)
                  ·
                    rfl

theorem cell23_1163543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 7].length) (baseStart_1163543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163543 prefixEnd_1163543 := by exact prefixLift 1163543
  have htrace : WordTrace (prefixWord ++ tailWord_1163543) baseStart_1163543 baseEnd_1163543 := by
    simpa [prefixWord, tailWord_1163543, baseEnd_1163543] using wordTrace_append hprefix tailTrace_1163543
  have hstable : (prefixWord ++ tailWord_1163543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163543).length < 2 ^ (prefixWord ++ tailWord_1163543).sum := by decide
  have hdescent : baseEnd_1163543 < baseStart_1163543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163573 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1163573 : Nat := 118140960795 + 1163573 * 2 ^ 59
def prefixEnd_1163573 : Nat := 4983230072969 + 3 ^ 40 * 1163573 * 2
def baseEnd_1163573 : Nat := 199157408531360416328777

theorem tailTrace_1163573 : CollatzResearch.WordTrace tailWord_1163573 prefixEnd_1163573 199157408531360416328777 := by
  unfold tailWord_1163573
  simp only [CollatzResearch.WordTrace]
  refine ⟨42438993813581218292407373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28292662542387478861604915 42438993813581218292407373)
  ·
    refine ⟨15914622680092956859652765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42438993813581218292407373 15914622680092956859652765)
    ·
      refine ⟨5967983505034858822369787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15914622680092956859652765 5967983505034858822369787)
      ·
        refine ⟨8951975257552288233554681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967983505034858822369787 8951975257552288233554681)
        ·
          refine ⟨6713981443164216175166011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8951975257552288233554681 6713981443164216175166011)
          ·
            refine ⟨10070972164746324262749017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713981443164216175166011 10070972164746324262749017)
            ·
              refine ⟨7553229123559743197061763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10070972164746324262749017 7553229123559743197061763)
              ·
                refine ⟨11329843685339614795592645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7553229123559743197061763 11329843685339614795592645)
                ·
                  refine ⟨2124345691001177774173621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11329843685339614795592645 2124345691001177774173621)
                  ·
                    refine ⟨199157408531360416328777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2124345691001177774173621 199157408531360416328777)
                    ·
                      rfl

theorem cell23_1163573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1163573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163573 prefixEnd_1163573 := by exact prefixLift 1163573
  have htrace : WordTrace (prefixWord ++ tailWord_1163573) baseStart_1163573 baseEnd_1163573 := by
    simpa [prefixWord, tailWord_1163573, baseEnd_1163573] using wordTrace_append hprefix tailTrace_1163573
  have hstable : (prefixWord ++ tailWord_1163573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163573).length < 2 ^ (prefixWord ++ tailWord_1163573).sum := by decide
  have hdescent : baseEnd_1163573 < baseStart_1163573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163588 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1163588 : Nat := 118140960795 + 1163588 * 2 ^ 59
def prefixEnd_1163588 : Nat := 4983230072969 + 3 ^ 40 * 1163588 * 2
def baseEnd_1163588 : Nat := 597479927803898690298763

theorem tailTrace_1163588 : CollatzResearch.WordTrace tailWord_1163588 prefixEnd_1163588 597479927803898690298763 := by
  unfold tailWord_1163588
  simp only [CollatzResearch.WordTrace]
  refine ⟨21219770454263437927101709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28293027272351250569468945 21219770454263437927101709)
  ·
    refine ⟨7957413920348789222663141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21219770454263437927101709 7957413920348789222663141)
    ·
      refine ⟨1492015110065397979249339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7957413920348789222663141 1492015110065397979249339)
      ·
        refine ⟨2238022665098096968874009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492015110065397979249339 2238022665098096968874009)
        ·
          refine ⟨1678516998823572726655507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238022665098096968874009 1678516998823572726655507)
          ·
            refine ⟨2517775498235359089983261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678516998823572726655507 2517775498235359089983261)
            ·
              refine ⟨944165811838259658743723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517775498235359089983261 944165811838259658743723)
              ·
                refine ⟨1416248717757389488115585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944165811838259658743723 1416248717757389488115585)
                ·
                  refine ⟨1062186538318042116086689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416248717757389488115585 1062186538318042116086689)
                  ·
                    refine ⟨796639903738531587065017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1062186538318042116086689 796639903738531587065017)
                    ·
                      refine ⟨597479927803898690298763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796639903738531587065017 597479927803898690298763)
                      ·
                        rfl

theorem cell23_1163588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1163588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163588 prefixEnd_1163588 := by exact prefixLift 1163588
  have htrace : WordTrace (prefixWord ++ tailWord_1163588) baseStart_1163588 baseEnd_1163588 := by
    simpa [prefixWord, tailWord_1163588, baseEnd_1163588] using wordTrace_append hprefix tailTrace_1163588
  have hstable : (prefixWord ++ tailWord_1163588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163588).length < 2 ^ (prefixWord ++ tailWord_1163588).sum := by decide
  have hdescent : baseEnd_1163588 < baseStart_1163588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163603 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 5, 4]
def baseStart_1163603 : Nat := 118140960795 + 1163603 * 2 ^ 59
def prefixEnd_1163603 : Nat := 4983230072969 + 3 ^ 40 * 1163603 * 2
def baseEnd_1163603 : Nat := 199162543337905377203731

theorem tailTrace_1163603 : CollatzResearch.WordTrace tailWord_1163603 prefixEnd_1163603 199162543337905377203731 := by
  unfold tailWord_1163603
  simp only [CollatzResearch.WordTrace]
  refine ⟨42440088003472533415999463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28293392002315022277332975 42440088003472533415999463)
  ·
    refine ⟨63660132005208800123999195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42440088003472533415999463 63660132005208800123999195)
    ·
      refine ⟨95490198007813200185998793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63660132005208800123999195 95490198007813200185998793)
      ·
        refine ⟨71617648505859900139499095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95490198007813200185998793 71617648505859900139499095)
        ·
          refine ⟨107426472758789850209248643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71617648505859900139499095 107426472758789850209248643)
          ·
            refine ⟨161139709138184775313872965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107426472758789850209248643 161139709138184775313872965)
            ·
              refine ⟨30213695463409645371351181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161139709138184775313872965 30213695463409645371351181)
              ·
                refine ⟨11330135798778617014256693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30213695463409645371351181 11330135798778617014256693)
                ·
                  refine ⟨1062200231135495345086565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11330135798778617014256693 1062200231135495345086565)
                  ·
                    refine ⟨199162543337905377203731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062200231135495345086565 199162543337905377203731)
                    ·
                      rfl

theorem cell23_1163603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 4].length) (baseStart_1163603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163603 prefixEnd_1163603 := by exact prefixLift 1163603
  have htrace : WordTrace (prefixWord ++ tailWord_1163603) baseStart_1163603 baseEnd_1163603 := by
    simpa [prefixWord, tailWord_1163603, baseEnd_1163603] using wordTrace_append hprefix tailTrace_1163603
  have hstable : (prefixWord ++ tailWord_1163603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163603).length < 2 ^ (prefixWord ++ tailWord_1163603).sum := by decide
  have hdescent : baseEnd_1163603 < baseStart_1163603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163633 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 6]
def baseStart_1163633 : Nat := 118140960795 + 1163633 * 2 ^ 59
def prefixEnd_1163633 : Nat := 4983230072969 + 3 ^ 40 * 1163633 * 2
def baseEnd_1163633 : Nat := 66389226048150112692895

theorem tailTrace_1163633 : CollatzResearch.WordTrace tailWord_1163633 prefixEnd_1163633 66389226048150112692895 := by
  unfold tailWord_1163633
  simp only [CollatzResearch.WordTrace]
  refine ⟨42441182193363848539591553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28294121462242565693061035 42441182193363848539591553)
  ·
    refine ⟨31830886645022886404693665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42441182193363848539591553 31830886645022886404693665)
    ·
      refine ⟨23873164983767164803520249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31830886645022886404693665 23873164983767164803520249)
      ·
        refine ⟨17904873737825373602640187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23873164983767164803520249 17904873737825373602640187)
        ·
          refine ⟨26857310606738060403960281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17904873737825373602640187 26857310606738060403960281)
          ·
            refine ⟨20142982955053545302970211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26857310606738060403960281 20142982955053545302970211)
            ·
              refine ⟨30214474432580317954455317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20142982955053545302970211 30214474432580317954455317)
              ·
                refine ⟨1416303489027202404115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30214474432580317954455317 1416303489027202404115093)
                ·
                  refine ⟨66389226048150112692895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1416303489027202404115093 66389226048150112692895)
                  ·
                    rfl

theorem cell23_1163633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_1163633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163633 prefixEnd_1163633 := by exact prefixLift 1163633
  have htrace : WordTrace (prefixWord ++ tailWord_1163633) baseStart_1163633 baseEnd_1163633 := by
    simpa [prefixWord, tailWord_1163633, baseEnd_1163633] using wordTrace_append hprefix tailTrace_1163633
  have hstable : (prefixWord ++ tailWord_1163633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163633).length < 2 ^ (prefixWord ++ tailWord_1163633).sum := by decide
  have hdescent : baseEnd_1163633 < baseStart_1163633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163637 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1163637 : Nat := 118140960795 + 1163637 * 2 ^ 59
def prefixEnd_1163637 : Nat := 4983230072969 + 3 ^ 40 * 1163637 * 2
def baseEnd_1163637 : Nat := 199168362785322999528679

theorem tailTrace_1163637 : CollatzResearch.WordTrace tailWord_1163637 prefixEnd_1163637 199168362785322999528679 := by
  unfold tailWord_1163637
  simp only [CollatzResearch.WordTrace]
  refine ⟨42441328085349357222737165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28294218723566238148491443 42441328085349357222737165)
  ·
    refine ⟨15915498032006008958526437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42441328085349357222737165 15915498032006008958526437)
    ·
      refine ⟨2984155881001126679723707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15915498032006008958526437 2984155881001126679723707)
      ·
        refine ⟨4476233821501690019585561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984155881001126679723707 4476233821501690019585561)
        ·
          refine ⟨3357175366126267514689171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4476233821501690019585561 3357175366126267514689171)
          ·
            refine ⟨5035763049189401272033757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357175366126267514689171 5035763049189401272033757)
            ·
              refine ⟨1888411143446025477012659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5035763049189401272033757 1888411143446025477012659)
              ·
                refine ⟨2832616715169038215518989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1888411143446025477012659 2832616715169038215518989)
                ·
                  refine ⟨1062231268188389330819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2832616715169038215518989 1062231268188389330819621)
                  ·
                    refine ⟨199168362785322999528679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062231268188389330819621 199168362785322999528679)
                    ·
                      rfl

theorem cell23_1163637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1163637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163637 prefixEnd_1163637 := by exact prefixLift 1163637
  have htrace : WordTrace (prefixWord ++ tailWord_1163637) baseStart_1163637 baseEnd_1163637 := by
    simpa [prefixWord, tailWord_1163637, baseEnd_1163637] using wordTrace_append hprefix tailTrace_1163637
  have hstable : (prefixWord ++ tailWord_1163637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163637).length < 2 ^ (prefixWord ++ tailWord_1163637).sum := by decide
  have hdescent : baseEnd_1163637 < baseStart_1163637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163688 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1163688 : Nat := 118140960795 + 1163688 * 2 ^ 59
def prefixEnd_1163688 : Nat := 4983230072969 + 3 ^ 40 * 1163688 * 2
def baseEnd_1163688 : Nat := 199177091956449433016101

theorem tailTrace_1163688 : CollatzResearch.WordTrace tailWord_1163688 prefixEnd_1163688 199177091956449433016101 := by
  unfold tailWord_1163688
  simp only [CollatzResearch.WordTrace]
  refine ⟨21221594104082296466421859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28295458805443061955229145 21221594104082296466421859)
  ·
    refine ⟨31832391156123444699632789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21221594104082296466421859 31832391156123444699632789)
    ·
      refine ⟨1492143335443286470295287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31832391156123444699632789 1492143335443286470295287)
      ·
        refine ⟨2238215003164929705442931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492143335443286470295287 2238215003164929705442931)
        ·
          refine ⟨3357322504747394558164397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238215003164929705442931 3357322504747394558164397)
          ·
            refine ⟨1258995939280272959311649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3357322504747394558164397 1258995939280272959311649)
            ·
              refine ⟨944246954460204719483737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258995939280272959311649 944246954460204719483737)
              ·
                refine ⟨708185215845153539612803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944246954460204719483737 708185215845153539612803)
                ·
                  refine ⟨1062277823767730309419205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708185215845153539612803 1062277823767730309419205)
                  ·
                    refine ⟨199177091956449433016101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1062277823767730309419205 199177091956449433016101)
                    ·
                      rfl

theorem cell23_1163688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1163688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163688 prefixEnd_1163688 := by exact prefixLift 1163688
  have htrace : WordTrace (prefixWord ++ tailWord_1163688) baseStart_1163688 baseEnd_1163688 := by
    simpa [prefixWord, tailWord_1163688, baseEnd_1163688] using wordTrace_append hprefix tailTrace_1163688
  have hstable : (prefixWord ++ tailWord_1163688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163688).length < 2 ^ (prefixWord ++ tailWord_1163688).sum := by decide
  have hdescent : baseEnd_1163688 < baseStart_1163688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163710 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1163710 : Nat := 118140960795 + 1163710 * 2 ^ 59
def prefixEnd_1163710 : Nat := 4983230072969 + 3 ^ 40 * 1163710 * 2
def baseEnd_1163710 : Nat := 199180857481249070991067

theorem tailTrace_1163710 : CollatzResearch.WordTrace tailWord_1163710 prefixEnd_1163710 199180857481249070991067 := by
  unfold tailWord_1163710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305498826760611336268073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28295993742723260460096389 5305498826760611336268073)
  ·
    refine ⟨3979124120070458502201055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5305498826760611336268073 3979124120070458502201055)
    ·
      refine ⟨5968686180105687753301583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979124120070458502201055 5968686180105687753301583)
      ·
        refine ⟨8953029270158531629952375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968686180105687753301583 8953029270158531629952375)
        ·
          refine ⟨13429543905237797444928563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8953029270158531629952375 13429543905237797444928563)
          ·
            refine ⟨20144315857856696167392845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429543905237797444928563 20144315857856696167392845)
            ·
              refine ⟨7554118446696261062772317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20144315857856696167392845 7554118446696261062772317)
              ·
                refine ⟨2832794417511097898539619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7554118446696261062772317 2832794417511097898539619)
                ·
                  refine ⟨4249191626266646847809429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832794417511097898539619 4249191626266646847809429)
                  ·
                    refine ⟨199180857481249070991067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4249191626266646847809429 199180857481249070991067)
                    ·
                      rfl

theorem cell23_1163710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1163710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163710 prefixEnd_1163710 := by exact prefixLift 1163710
  have htrace : WordTrace (prefixWord ++ tailWord_1163710) baseStart_1163710 baseEnd_1163710 := by
    simpa [prefixWord, tailWord_1163710, baseEnd_1163710] using wordTrace_append hprefix tailTrace_1163710
  have hstable : (prefixWord ++ tailWord_1163710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163710).length < 2 ^ (prefixWord ++ tailWord_1163710).sum := by decide
  have hdescent : baseEnd_1163710 < baseStart_1163710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163734 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1163734 : Nat := 118140960795 + 1163734 * 2 ^ 59
def prefixEnd_1163734 : Nat := 4983230072969 + 3 ^ 40 * 1163734 * 2
def baseEnd_1163734 : Nat := 597554895979455119073091

theorem tailTrace_1163734 : CollatzResearch.WordTrace tailWord_1163734 prefixEnd_1163734 597554895979455119073091 := by
  unfold tailWord_1163734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652804122874871424313641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28296577310665295192678837 2652804122874871424313641)
  ·
    refine ⟨1989603092156153568235231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2652804122874871424313641 1989603092156153568235231)
    ·
      refine ⟨2984404638234230352352847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989603092156153568235231 2984404638234230352352847)
      ·
        refine ⟨4476606957351345528529271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984404638234230352352847 4476606957351345528529271)
        ·
          refine ⟨6714910436027018292793907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476606957351345528529271 6714910436027018292793907)
          ·
            refine ⟨10072365654040527439190861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714910436027018292793907 10072365654040527439190861)
            ·
              refine ⟨3777137120265197789696573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10072365654040527439190861 3777137120265197789696573)
              ·
                refine ⟨1416426420099449171136215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3777137120265197789696573 1416426420099449171136215)
                ·
                  refine ⟨2124639630149173756704323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416426420099449171136215 2124639630149173756704323)
                  ·
                    refine ⟨3186959445223760635056485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124639630149173756704323 3186959445223760635056485)
                    ·
                      refine ⟨597554895979455119073091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3186959445223760635056485 597554895979455119073091)
                      ·
                        rfl

theorem cell23_1163734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1163734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163734 prefixEnd_1163734 := by exact prefixLift 1163734
  have htrace : WordTrace (prefixWord ++ tailWord_1163734) baseStart_1163734 baseEnd_1163734 := by
    simpa [prefixWord, tailWord_1163734, baseEnd_1163734] using wordTrace_append hprefix tailTrace_1163734
  have hstable : (prefixWord ++ tailWord_1163734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163734).length < 2 ^ (prefixWord ++ tailWord_1163734).sum := by decide
  have hdescent : baseEnd_1163734 < baseStart_1163734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163737 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_1163737 : Nat := 118140960795 + 1163737 * 2 ^ 59
def prefixEnd_1163737 : Nat := 4983230072969 + 3 ^ 40 * 1163737 * 2
def baseEnd_1163737 : Nat := 597556436421418607335577

theorem tailTrace_1163737 : CollatzResearch.WordTrace tailWord_1163737 prefixEnd_1163737 597556436421418607335577 := by
  unfold tailWord_1163737
  simp only [CollatzResearch.WordTrace]
  refine ⟨42444975384987074301377465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28296650256658049534251643 42444975384987074301377465)
  ·
    refine ⟨31833731538740305726033099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42444975384987074301377465 31833731538740305726033099)
    ·
      refine ⟨47750597308110458589049649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31833731538740305726033099 47750597308110458589049649)
      ·
        refine ⟨35812947981082843941787237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47750597308110458589049649 35812947981082843941787237)
        ·
          refine ⟨6714927746453033239085107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35812947981082843941787237 6714927746453033239085107)
          ·
            refine ⟨10072391619679549858627661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714927746453033239085107 10072391619679549858627661)
            ·
              refine ⟨3777146857379831196985373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10072391619679549858627661 3777146857379831196985373)
              ·
                refine ⟨1416430071517436698869515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3777146857379831196985373 1416430071517436698869515)
                ·
                  refine ⟨2124645107276155048304273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416430071517436698869515 2124645107276155048304273)
                  ·
                    refine ⟨1593483830457116286228205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2124645107276155048304273 1593483830457116286228205)
                    ·
                      refine ⟨597556436421418607335577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1593483830457116286228205 597556436421418607335577)
                      ·
                        rfl

theorem cell23_1163737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_1163737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163737 prefixEnd_1163737 := by exact prefixLift 1163737
  have htrace : WordTrace (prefixWord ++ tailWord_1163737) baseStart_1163737 baseEnd_1163737 := by
    simpa [prefixWord, tailWord_1163737, baseEnd_1163737] using wordTrace_append hprefix tailTrace_1163737
  have hstable : (prefixWord ++ tailWord_1163737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163737).length < 2 ^ (prefixWord ++ tailWord_1163737).sum := by decide
  have hdescent : baseEnd_1163737 < baseStart_1163737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163751 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1163751 : Nat := 118140960795 + 1163751 * 2 ^ 59
def prefixEnd_1163751 : Nat := 4983230072969 + 3 ^ 40 * 1163751 * 2
def baseEnd_1163751 : Nat := 597563625150581552560513

theorem tailTrace_1163751 : CollatzResearch.WordTrace tailWord_1163751 prefixEnd_1163751 597563625150581552560513 := by
  unfold tailWord_1163751
  simp only [CollatzResearch.WordTrace]
  refine ⟨42445486006936354692387107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28296990671290903128258071 42445486006936354692387107)
  ·
    refine ⟨63668229010404532038580661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42445486006936354692387107 63668229010404532038580661)
    ·
      refine ⟨5968896469725424878616937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63668229010404532038580661 5968896469725424878616937)
      ·
        refine ⟨4476672352294068658962703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5968896469725424878616937 4476672352294068658962703)
        ·
          refine ⟨6715008528441102988444055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476672352294068658962703 6715008528441102988444055)
          ·
            refine ⟨10072512792661654482666083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715008528441102988444055 10072512792661654482666083)
            ·
              refine ⟨15108769188992481723999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10072512792661654482666083 15108769188992481723999125)
              ·
                refine ⟨708223555734022580812459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15108769188992481723999125 708223555734022580812459)
                ·
                  refine ⟨1062335333601033871218689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708223555734022580812459 1062335333601033871218689)
                  ·
                    refine ⟨796751500200775403414017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1062335333601033871218689 796751500200775403414017)
                    ·
                      refine ⟨597563625150581552560513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796751500200775403414017 597563625150581552560513)
                      ·
                        rfl

theorem cell23_1163751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1163751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163751 prefixEnd_1163751 := by exact prefixLift 1163751
  have htrace : WordTrace (prefixWord ++ tailWord_1163751) baseStart_1163751 baseEnd_1163751 := by
    simpa [prefixWord, tailWord_1163751, baseEnd_1163751] using wordTrace_append hprefix tailTrace_1163751
  have hstable : (prefixWord ++ tailWord_1163751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163751).length < 2 ^ (prefixWord ++ tailWord_1163751).sum := by decide
  have hdescent : baseEnd_1163751 < baseStart_1163751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163753 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_1163753 : Nat := 118140960795 + 1163753 * 2 ^ 59
def prefixEnd_1163753 : Nat := 4983230072969 + 3 ^ 40 * 1163753 * 2
def baseEnd_1163753 : Nat := 199188217370630181578501

theorem tailTrace_1163753 : CollatzResearch.WordTrace tailWord_1163753 prefixEnd_1163753 199188217370630181578501 := by
  unfold tailWord_1163753
  simp only [CollatzResearch.WordTrace]
  refine ⟨42445558952929109033959913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28297039301952739355973275 42445558952929109033959913)
  ·
    refine ⟨31834169214696831775469935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42445558952929109033959913 31834169214696831775469935)
    ·
      refine ⟨47751253822045247663204903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31834169214696831775469935 47751253822045247663204903)
      ·
        refine ⟨71626880733067871494807355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47751253822045247663204903 71626880733067871494807355)
        ·
          refine ⟨107440321099601807242211033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71626880733067871494807355 107440321099601807242211033)
          ·
            refine ⟨80580240824701355431658275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107440321099601807242211033 80580240824701355431658275)
            ·
              refine ⟨120870361237052033147487413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80580240824701355431658275 120870361237052033147487413)
              ·
                refine ⟨11331596365973628107576945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120870361237052033147487413 11331596365973628107576945)
                ·
                  refine ⟨8498697274480221080682709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11331596365973628107576945 8498697274480221080682709)
                  ·
                    refine ⟨199188217370630181578501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8498697274480221080682709 199188217370630181578501)
                    ·
                      rfl

theorem cell23_1163753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_1163753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163753 prefixEnd_1163753 := by exact prefixLift 1163753
  have htrace : WordTrace (prefixWord ++ tailWord_1163753) baseStart_1163753 baseEnd_1163753 := by
    simpa [prefixWord, tailWord_1163753, baseEnd_1163753] using wordTrace_append hprefix tailTrace_1163753
  have hstable : (prefixWord ++ tailWord_1163753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163753).length < 2 ^ (prefixWord ++ tailWord_1163753).sum := by decide
  have hdescent : baseEnd_1163753 < baseStart_1163753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163810 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1163810 : Nat := 118140960795 + 1163810 * 2 ^ 59
def prefixEnd_1163810 : Nat := 4983230072969 + 3 ^ 40 * 1163810 * 2
def baseEnd_1163810 : Nat := 597593920509196821722741

theorem tailTrace_1163810 : CollatzResearch.WordTrace tailWord_1163810 prefixEnd_1163810 597593920509196821722741 := by
  unfold tailWord_1163810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611909478430651942196221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28298425275815071845856589 10611909478430651942196221)
  ·
    refine ⟨3979466054411494478323583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10611909478430651942196221 3979466054411494478323583)
    ·
      refine ⟨5969199081617241717485375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979466054411494478323583 5969199081617241717485375)
      ·
        refine ⟨8953798622425862576228063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969199081617241717485375 8953798622425862576228063)
        ·
          refine ⟨13430697933638793864342095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8953798622425862576228063 13430697933638793864342095)
          ·
            refine ⟨20146046900458190796513143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13430697933638793864342095 20146046900458190796513143)
            ·
              refine ⟨30219070350687286194769715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20146046900458190796513143 30219070350687286194769715)
              ·
                refine ⟨45328605526030929292154573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30219070350687286194769715 45328605526030929292154573)
                ·
                  refine ⟨16998227072261598484557965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45328605526030929292154573 16998227072261598484557965)
                  ·
                    refine ⟨6374335152098099431709237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16998227072261598484557965 6374335152098099431709237)
                    ·
                      refine ⟨597593920509196821722741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6374335152098099431709237 597593920509196821722741)
                      ·
                        rfl

theorem cell23_1163810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1163810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163810 prefixEnd_1163810 := by exact prefixLift 1163810
  have htrace : WordTrace (prefixWord ++ tailWord_1163810) baseStart_1163810 baseEnd_1163810 := by
    simpa [prefixWord, tailWord_1163810, baseEnd_1163810] using wordTrace_append hprefix tailTrace_1163810
  have hstable : (prefixWord ++ tailWord_1163810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163810).length < 2 ^ (prefixWord ++ tailWord_1163810).sum := by decide
  have hdescent : baseEnd_1163810 < baseStart_1163810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163818 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1163818 : Nat := 118140960795 + 1163818 * 2 ^ 59
def prefixEnd_1163818 : Nat := 4983230072969 + 3 ^ 40 * 1163818 * 2
def baseEnd_1163818 : Nat := 597598028354432790422705

theorem tailTrace_1163818 : CollatzResearch.WordTrace tailWord_1163818 prefixEnd_1163818 597598028354432790422705 := by
  unfold tailWord_1163818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611982424423406283769027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28298619798462416756717405 10611982424423406283769027)
  ·
    refine ⟨15917973636635109425653541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10611982424423406283769027 15917973636635109425653541)
    ·
      refine ⟨2984620056869083017310039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15917973636635109425653541 2984620056869083017310039)
      ·
        refine ⟨4476930085303624525965059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984620056869083017310039 4476930085303624525965059)
        ·
          refine ⟨6715395127955436788947589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476930085303624525965059 6715395127955436788947589)
          ·
            refine ⟨1259136586491644397927673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6715395127955436788947589 1259136586491644397927673)
            ·
              refine ⟨944352439868733298445755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259136586491644397927673 944352439868733298445755)
              ·
                refine ⟨1416528659803099947668633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944352439868733298445755 1416528659803099947668633)
                ·
                  refine ⟨1062396494852324960751475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416528659803099947668633 1062396494852324960751475)
                  ·
                    refine ⟨1593594742278487441127213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1062396494852324960751475 1593594742278487441127213)
                    ·
                      refine ⟨597598028354432790422705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1593594742278487441127213 597598028354432790422705)
                      ·
                        rfl

theorem cell23_1163818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1163818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163818 prefixEnd_1163818 := by exact prefixLift 1163818
  have htrace : WordTrace (prefixWord ++ tailWord_1163818) baseStart_1163818 baseEnd_1163818 := by
    simpa [prefixWord, tailWord_1163818, baseEnd_1163818] using wordTrace_append hprefix tailTrace_1163818
  have hstable : (prefixWord ++ tailWord_1163818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163818).length < 2 ^ (prefixWord ++ tailWord_1163818).sum := by decide
  have hdescent : baseEnd_1163818 < baseStart_1163818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163820 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1163820 : Nat := 118140960795 + 1163820 * 2 ^ 59
def prefixEnd_1163820 : Nat := 4983230072969 + 3 ^ 40 * 1163820 * 2
def baseEnd_1163820 : Nat := 597599055315741782597695

theorem tailTrace_1163820 : CollatzResearch.WordTrace tailWord_1163820 prefixEnd_1163820 597599055315741782597695 := by
  unfold tailWord_1163820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21224001321843189738324457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28298668429124252984432609 21224001321843189738324457)
  ·
    refine ⟨15918000991382392303743343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21224001321843189738324457 15918000991382392303743343)
    ·
      refine ⟨23877001487073588455615015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15918000991382392303743343 23877001487073588455615015)
      ·
        refine ⟨35815502230610382683422523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23877001487073588455615015 35815502230610382683422523)
        ·
          refine ⟨53723253345915574025133785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35815502230610382683422523 53723253345915574025133785)
          ·
            refine ⟨40292440009436680518850339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53723253345915574025133785 40292440009436680518850339)
            ·
              refine ⟨60438660014155020778275509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40292440009436680518850339 60438660014155020778275509)
              ·
                refine ⟨5666124376327033197963329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60438660014155020778275509 5666124376327033197963329)
                ·
                  refine ⟨4249593282245274898472497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5666124376327033197963329 4249593282245274898472497)
                  ·
                    refine ⟨3187194961683956173854373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4249593282245274898472497 3187194961683956173854373)
                    ·
                      refine ⟨597599055315741782597695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3187194961683956173854373 597599055315741782597695)
                      ·
                        rfl

theorem cell23_1163820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1163820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163820 prefixEnd_1163820 := by exact prefixLift 1163820
  have htrace : WordTrace (prefixWord ++ tailWord_1163820) baseStart_1163820 baseEnd_1163820 := by
    simpa [prefixWord, tailWord_1163820, baseEnd_1163820] using wordTrace_append hprefix tailTrace_1163820
  have hstable : (prefixWord ++ tailWord_1163820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163820).length < 2 ^ (prefixWord ++ tailWord_1163820).sum := by decide
  have hdescent : baseEnd_1163820 < baseStart_1163820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163828 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1163828 : Nat := 118140960795 + 1163828 * 2 ^ 59
def prefixEnd_1163828 : Nat := 4983230072969 + 3 ^ 40 * 1163828 * 2
def baseEnd_1163828 : Nat := 597603163160977751297659

theorem tailTrace_1163828 : CollatzResearch.WordTrace tailWord_1163828 prefixEnd_1163828 597603163160977751297659 := by
  unfold tailWord_1163828
  simp only [CollatzResearch.WordTrace]
  refine ⟨21224147213828698421470069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28298862951771597895293425 21224147213828698421470069)
  ·
    refine ⟨1989763801296440477012819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21224147213828698421470069 1989763801296440477012819)
    ·
      refine ⟨2984645701944660715519229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989763801296440477012819 2984645701944660715519229)
      ·
        refine ⟨1119242138229247768319711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2984645701944660715519229 1119242138229247768319711)
        ·
          refine ⟨1678863207343871652479567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119242138229247768319711 1678863207343871652479567)
          ·
            refine ⟨2518294811015807478719351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678863207343871652479567 2518294811015807478719351)
            ·
              refine ⟨3777442216523711218079027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518294811015807478719351 3777442216523711218079027)
              ·
                refine ⟨5666163324785566827118541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777442216523711218079027 5666163324785566827118541)
                ·
                  refine ⟨2124811246794587560169453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5666163324785566827118541 2124811246794587560169453)
                  ·
                    refine ⟨796804217547970335063545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124811246794587560169453 796804217547970335063545)
                    ·
                      refine ⟨597603163160977751297659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796804217547970335063545 597603163160977751297659)
                      ·
                        rfl

theorem cell23_1163828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1163828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163828 prefixEnd_1163828 := by exact prefixLift 1163828
  have htrace : WordTrace (prefixWord ++ tailWord_1163828) baseStart_1163828 baseEnd_1163828 := by
    simpa [prefixWord, tailWord_1163828, baseEnd_1163828] using wordTrace_append hprefix tailTrace_1163828
  have hstable : (prefixWord ++ tailWord_1163828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163828).length < 2 ^ (prefixWord ++ tailWord_1163828).sum := by decide
  have hdescent : baseEnd_1163828 < baseStart_1163828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163864 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 5]
def baseStart_1163864 : Nat := 118140960795 + 1163864 * 2 ^ 59
def prefixEnd_1163864 : Nat := 4983230072969 + 3 ^ 40 * 1163864 * 2
def baseEnd_1163864 : Nat := 66402405384948845605277

theorem tailTrace_1163864 : CollatzResearch.WordTrace tailWord_1163864 prefixEnd_1163864 66402405384948845605277 := by
  unfold tailWord_1163864
  simp only [CollatzResearch.WordTrace]
  refine ⟨21224803727763487495625323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28299738303684649994167097 21224803727763487495625323)
  ·
    refine ⟨31837205591645231243437985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21224803727763487495625323 31837205591645231243437985)
    ·
      refine ⟨23877904193733923432578489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31837205591645231243437985 23877904193733923432578489)
      ·
        refine ⟨17908428145300442574433867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23877904193733923432578489 17908428145300442574433867)
        ·
          refine ⟨26862642217950663861650801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17908428145300442574433867 26862642217950663861650801)
          ·
            refine ⟨20146981663462997896238101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26862642217950663861650801 20146981663462997896238101)
            ·
              refine ⟨944389765474828026386161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20146981663462997896238101 944389765474828026386161)
              ·
                refine ⟨708292324106121019789621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944389765474828026386161 708292324106121019789621)
                ·
                  refine ⟨66402405384948845605277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 708292324106121019789621 66402405384948845605277)
                  ·
                    rfl

theorem cell23_1163864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 5].length) (baseStart_1163864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163864 prefixEnd_1163864 := by exact prefixLift 1163864
  have htrace : WordTrace (prefixWord ++ tailWord_1163864) baseStart_1163864 baseEnd_1163864 := by
    simpa [prefixWord, tailWord_1163864, baseEnd_1163864] using wordTrace_append hprefix tailTrace_1163864
  have hstable : (prefixWord ++ tailWord_1163864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163864).length < 2 ^ (prefixWord ++ tailWord_1163864).sum := by decide
  have hdescent : baseEnd_1163864 < baseStart_1163864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163894 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1163894 : Nat := 118140960795 + 1163894 * 2 ^ 59
def prefixEnd_1163894 : Nat := 4983230072969 + 3 ^ 40 * 1163894 * 2
def baseEnd_1163894 : Nat := 199212350961391497690785

theorem tailTrace_1163894 : CollatzResearch.WordTrace tailWord_1163894 prefixEnd_1163894 199212350961391497690785 := by
  unfold tailWord_1163894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653168852838643132177671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28300467763612193409895157 2653168852838643132177671)
  ·
    refine ⟨3979753279257964698266507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2653168852838643132177671 3979753279257964698266507)
    ·
      refine ⟨5969629918886947047399761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979753279257964698266507 5969629918886947047399761)
      ·
        refine ⟨4477222439165210285549821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5969629918886947047399761 4477222439165210285549821)
        ·
          refine ⟨1678958414686953857081183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4477222439165210285549821 1678958414686953857081183)
          ·
            refine ⟨2518437622030430785621775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678958414686953857081183 2518437622030430785621775)
            ·
              refine ⟨3777656433045646178432663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518437622030430785621775 3777656433045646178432663)
              ·
                refine ⟨5666484649568469267648995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777656433045646178432663 5666484649568469267648995)
                ·
                  refine ⟨8499726974352703901473493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5666484649568469267648995 8499726974352703901473493)
                  ·
                    refine ⟨199212350961391497690785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8499726974352703901473493 199212350961391497690785)
                    ·
                      rfl

theorem cell23_1163894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1163894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163894 prefixEnd_1163894 := by exact prefixLift 1163894
  have htrace : WordTrace (prefixWord ++ tailWord_1163894) baseStart_1163894 baseEnd_1163894 := by
    simpa [prefixWord, tailWord_1163894, baseEnd_1163894] using wordTrace_append hprefix tailTrace_1163894
  have hstable : (prefixWord ++ tailWord_1163894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163894).length < 2 ^ (prefixWord ++ tailWord_1163894).sum := by decide
  have hdescent : baseEnd_1163894 < baseStart_1163894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163897 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1163897 : Nat := 118140960795 + 1163897 * 2 ^ 59
def prefixEnd_1163897 : Nat := 4983230072969 + 3 ^ 40 * 1163897 * 2
def baseEnd_1163897 : Nat := 597638593326137981334841

theorem tailTrace_1163897 : CollatzResearch.WordTrace tailWord_1163897 prefixEnd_1163897 597638593326137981334841 := by
  unfold tailWord_1163897
  simp only [CollatzResearch.WordTrace]
  refine ⟨42450811064407421627201945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28300540709604947751467963 42450811064407421627201945)
  ·
    refine ⟨31838108298305566220401459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42450811064407421627201945 31838108298305566220401459)
    ·
      refine ⟨47757162447458349330602189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31838108298305566220401459 47757162447458349330602189)
      ·
        refine ⟨17908935917796880998975821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47757162447458349330602189 17908935917796880998975821)
        ·
          refine ⟨6715850969173830374615933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17908935917796880998975821 6715850969173830374615933)
          ·
            refine ⟨2518444113440186390480975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6715850969173830374615933 2518444113440186390480975)
            ·
              refine ⟨3777666170160279585721463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518444113440186390480975 3777666170160279585721463)
              ·
                refine ⟨5666499255240419378582195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777666170160279585721463 5666499255240419378582195)
                ·
                  refine ⟨8499748882860629067873293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5666499255240419378582195 8499748882860629067873293)
                  ·
                    refine ⟨3187405831072735900452485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8499748882860629067873293 3187405831072735900452485)
                    ·
                      refine ⟨597638593326137981334841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3187405831072735900452485 597638593326137981334841)
                      ·
                        rfl

theorem cell23_1163897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1163897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163897 prefixEnd_1163897 := by exact prefixLift 1163897
  have htrace : WordTrace (prefixWord ++ tailWord_1163897) baseStart_1163897 baseEnd_1163897 := by
    simpa [prefixWord, tailWord_1163897, baseEnd_1163897] using wordTrace_append hprefix tailTrace_1163897
  have hstable : (prefixWord ++ tailWord_1163897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163897).length < 2 ^ (prefixWord ++ tailWord_1163897).sum := by decide
  have hdescent : baseEnd_1163897 < baseStart_1163897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163934 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1163934 : Nat := 118140960795 + 1163934 * 2 ^ 59
def prefixEnd_1163934 : Nat := 4983230072969 + 3 ^ 40 * 1163934 * 2
def baseEnd_1163934 : Nat := 597657592110354336572171

theorem tailTrace_1163934 : CollatzResearch.WordTrace tailWord_1163934 prefixEnd_1163934 597657592110354336572171 := by
  unfold tailWord_1163934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306520070659172118287357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28301440376848917964199237 5306520070659172118287357)
  ·
    refine ⟨1989945026497189544357759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5306520070659172118287357 1989945026497189544357759)
    ·
      refine ⟨2984917539745784316536639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989945026497189544357759 2984917539745784316536639)
      ·
        refine ⟨4477376309618676474804959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984917539745784316536639 4477376309618676474804959)
        ·
          refine ⟨6716064464428014712207439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477376309618676474804959 6716064464428014712207439)
          ·
            refine ⟨10074096696642022068311159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716064464428014712207439 10074096696642022068311159)
            ·
              refine ⟨15111145044963033102466739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10074096696642022068311159 15111145044963033102466739)
              ·
                refine ⟨22666717567444549653700109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15111145044963033102466739 22666717567444549653700109)
                ·
                  refine ⟨8500019087791706120137541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22666717567444549653700109 8500019087791706120137541)
                  ·
                    refine ⟨1593753578960944897525789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8500019087791706120137541 1593753578960944897525789)
                    ·
                      refine ⟨597657592110354336572171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1593753578960944897525789 597657592110354336572171)
                      ·
                        rfl

theorem cell23_1163934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1163934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163934 prefixEnd_1163934 := by exact prefixLift 1163934
  have htrace : WordTrace (prefixWord ++ tailWord_1163934) baseStart_1163934 baseEnd_1163934 := by
    simpa [prefixWord, tailWord_1163934, baseEnd_1163934] using wordTrace_append hprefix tailTrace_1163934
  have hstable : (prefixWord ++ tailWord_1163934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163934).length < 2 ^ (prefixWord ++ tailWord_1163934).sum := by decide
  have hdescent : baseEnd_1163934 < baseStart_1163934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163988 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1163988 : Nat := 118140960795 + 1163988 * 2 ^ 59
def prefixEnd_1163988 : Nat := 4983230072969 + 3 ^ 40 * 1163988 * 2
def baseEnd_1163988 : Nat := 66409480007299680588547

theorem tailTrace_1163988 : CollatzResearch.WordTrace tailWord_1163988 prefixEnd_1163988 66409480007299680588547 := by
  unfold tailWord_1163988
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227065053538872084382309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28302753404718496112509745 21227065053538872084382309)
  ·
    refine ⟨3980074697538538515821683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21227065053538872084382309 3980074697538538515821683)
    ·
      refine ⟨5970112046307807773732525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980074697538538515821683 5970112046307807773732525)
      ·
        refine ⟨2238792017365427915149697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5970112046307807773732525 2238792017365427915149697)
        ·
          refine ⟨1679094013024070936362273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238792017365427915149697 1679094013024070936362273)
          ·
            refine ⟨1259320509768053202271705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679094013024070936362273 1259320509768053202271705)
            ·
              refine ⟨944490382326039901703779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259320509768053202271705 944490382326039901703779)
              ·
                refine ⟨1416735573489059852555669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944490382326039901703779 1416735573489059852555669)
                ·
                  refine ⟨66409480007299680588547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1416735573489059852555669 66409480007299680588547)
                  ·
                    rfl

theorem cell23_1163988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1163988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1163988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1163988 prefixEnd_1163988 := by exact prefixLift 1163988
  have htrace : WordTrace (prefixWord ++ tailWord_1163988) baseStart_1163988 baseEnd_1163988 := by
    simpa [prefixWord, tailWord_1163988, baseEnd_1163988] using wordTrace_append hprefix tailTrace_1163988
  have hstable : (prefixWord ++ tailWord_1163988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163988).length < 2 ^ (prefixWord ++ tailWord_1163988).sum := by decide
  have hdescent : baseEnd_1163988 < baseStart_1163988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164001 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1164001 : Nat := 118140960795 + 1164001 * 2 ^ 59
def prefixEnd_1164001 : Nat := 4983230072969 + 3 ^ 40 * 1164001 * 2
def baseEnd_1164001 : Nat := 199230665104735191478121

theorem tailTrace_1164001 : CollatzResearch.WordTrace tailWord_1164001 prefixEnd_1164001 199230665104735191478121 := by
  unfold tailWord_1164001
  simp only [CollatzResearch.WordTrace]
  refine ⟨42454604256030647388987857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28303069504020431592658571 42454604256030647388987857)
  ·
    refine ⟨31840953192022985541740893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42454604256030647388987857 31840953192022985541740893)
    ·
      refine ⟨11940357447008619578152835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31840953192022985541740893 11940357447008619578152835)
      ·
        refine ⟨17910536170512929367229253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940357447008619578152835 17910536170512929367229253)
        ·
          refine ⟨3358225531971174256355485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17910536170512929367229253 3358225531971174256355485)
          ·
            refine ⟨1259334574489190346133307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3358225531971174256355485 1259334574489190346133307)
            ·
              refine ⟨1889001861733785519199961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259334574489190346133307 1889001861733785519199961)
              ·
                refine ⟨1416751396300339139399971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889001861733785519199961 1416751396300339139399971)
                ·
                  refine ⟨2125127094450508709099957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416751396300339139399971 2125127094450508709099957)
                  ·
                    refine ⟨199230665104735191478121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2125127094450508709099957 199230665104735191478121)
                    ·
                      rfl

theorem cell23_1164001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1164001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164001 prefixEnd_1164001 := by exact prefixLift 1164001
  have htrace : WordTrace (prefixWord ++ tailWord_1164001) baseStart_1164001 baseEnd_1164001 := by
    simpa [prefixWord, tailWord_1164001, baseEnd_1164001] using wordTrace_append hprefix tailTrace_1164001
  have hstable : (prefixWord ++ tailWord_1164001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164001).length < 2 ^ (prefixWord ++ tailWord_1164001).sum := by decide
  have hdescent : baseEnd_1164001 < baseStart_1164001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164004 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1164004 : Nat := 118140960795 + 1164004 * 2 ^ 59
def prefixEnd_1164004 : Nat := 4983230072969 + 3 ^ 40 * 1164004 * 2
def baseEnd_1164004 : Nat := 597693535756169062696849

theorem tailTrace_1164004 : CollatzResearch.WordTrace tailWord_1164004 prefixEnd_1164004 597693535756169062696849 := by
  unfold tailWord_1164004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227356837509889450673533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28303142450013185934231377 21227356837509889450673533)
  ·
    refine ⟨7960258814066208544002575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21227356837509889450673533 7960258814066208544002575)
    ·
      refine ⟨11940388221099312816003863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7960258814066208544002575 11940388221099312816003863)
      ·
        refine ⟨17910582331648969224005795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940388221099312816003863 17910582331648969224005795)
        ·
          refine ⟨26865873497473453836008693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17910582331648969224005795 26865873497473453836008693)
          ·
            refine ⟨2518675640388136297125815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26865873497473453836008693 2518675640388136297125815)
            ·
              refine ⟨3778013460582204445688723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518675640388136297125815 3778013460582204445688723)
              ·
                refine ⟨5667020190873306668533085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778013460582204445688723 5667020190873306668533085)
                ·
                  refine ⟨2125132571577490000699907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5667020190873306668533085 2125132571577490000699907)
                  ·
                    refine ⟨3187698857366235001049861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125132571577490000699907 3187698857366235001049861)
                    ·
                      refine ⟨597693535756169062696849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3187698857366235001049861 597693535756169062696849)
                      ·
                        rfl

theorem cell23_1164004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1164004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164004 prefixEnd_1164004 := by exact prefixLift 1164004
  have htrace : WordTrace (prefixWord ++ tailWord_1164004) baseStart_1164004 baseEnd_1164004 := by
    simpa [prefixWord, tailWord_1164004, baseEnd_1164004] using wordTrace_append hprefix tailTrace_1164004
  have hstable : (prefixWord ++ tailWord_1164004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164004).length < 2 ^ (prefixWord ++ tailWord_1164004).sum := by decide
  have hdescent : baseEnd_1164004 < baseStart_1164004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164008 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1164008 : Nat := 118140960795 + 1164008 * 2 ^ 59
def prefixEnd_1164008 : Nat := 4983230072969 + 3 ^ 40 * 1164008 * 2
def baseEnd_1164008 : Nat := 597695589678787047046831

theorem tailTrace_1164008 : CollatzResearch.WordTrace tailWord_1164008 prefixEnd_1164008 597695589678787047046831 := by
  unfold tailWord_1164008
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227429783502643792246339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28303239711336858389661785 21227429783502643792246339)
  ·
    refine ⟨31841144675253965688369509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21227429783502643792246339 31841144675253965688369509)
    ·
      refine ⟨5970214626610118566569283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31841144675253965688369509 5970214626610118566569283)
      ·
        refine ⟨8955321939915177849853925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970214626610118566569283 8955321939915177849853925)
        ·
          refine ⟨1679122863734095846847611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8955321939915177849853925 1679122863734095846847611)
          ·
            refine ⟨2518684295601143770271417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679122863734095846847611 2518684295601143770271417)
            ·
              refine ⟨1889013221700857827703563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2518684295601143770271417 1889013221700857827703563)
              ·
                refine ⟨2833519832551286741555345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889013221700857827703563 2833519832551286741555345)
                ·
                  refine ⟨2125139874413465056166509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2833519832551286741555345 2125139874413465056166509)
                  ·
                    refine ⟨796927452905049396062441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125139874413465056166509 796927452905049396062441)
                    ·
                      refine ⟨597695589678787047046831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 796927452905049396062441 597695589678787047046831)
                      ·
                        rfl

theorem cell23_1164008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1164008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164008 prefixEnd_1164008 := by exact prefixLift 1164008
  have htrace : WordTrace (prefixWord ++ tailWord_1164008) baseStart_1164008 baseEnd_1164008 := by
    simpa [prefixWord, tailWord_1164008, baseEnd_1164008] using wordTrace_append hprefix tailTrace_1164008
  have hstable : (prefixWord ++ tailWord_1164008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164008).length < 2 ^ (prefixWord ++ tailWord_1164008).sum := by decide
  have hdescent : baseEnd_1164008 < baseStart_1164008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164014 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1164014 : Nat := 118140960795 + 1164014 * 2 ^ 59
def prefixEnd_1164014 : Nat := 4983230072969 + 3 ^ 40 * 1164014 * 2
def baseEnd_1164014 : Nat := 199232890187571341190601

theorem tailTrace_1164014 : CollatzResearch.WordTrace tailWord_1164014 prefixEnd_1164014 199232890187571341190601 := by
  unfold tailWord_1164014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306884800622943826151387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28303385603322367072807397 5306884800622943826151387)
  ·
    refine ⟨7960327200934415739227081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306884800622943826151387 7960327200934415739227081)
    ·
      refine ⟨5970245400700811804420311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7960327200934415739227081 5970245400700811804420311)
      ·
        refine ⟨8955368101051217706630467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970245400700811804420311 8955368101051217706630467)
        ·
          refine ⟨13433052151576826559945701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8955368101051217706630467 13433052151576826559945701)
          ·
            refine ⟨2518697278420654979989819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13433052151576826559945701 2518697278420654979989819)
            ·
              refine ⟨3778045917630982469984729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518697278420654979989819 3778045917630982469984729)
              ·
                refine ⟨2833534438223236852488547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778045917630982469984729 2833534438223236852488547)
                ·
                  refine ⟨4250301657334855278732821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833534438223236852488547 4250301657334855278732821)
                  ·
                    refine ⟨199232890187571341190601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4250301657334855278732821 199232890187571341190601)
                    ·
                      rfl

theorem cell23_1164014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1164014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164014 prefixEnd_1164014 := by exact prefixLift 1164014
  have htrace : WordTrace (prefixWord ++ tailWord_1164014) baseStart_1164014 baseEnd_1164014 := by
    simpa [prefixWord, tailWord_1164014, baseEnd_1164014] using wordTrace_append hprefix tailTrace_1164014
  have hstable : (prefixWord ++ tailWord_1164014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164014).length < 2 ^ (prefixWord ++ tailWord_1164014).sum := by decide
  have hdescent : baseEnd_1164014 < baseStart_1164014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164067 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1164067 : Nat := 118140960795 + 1164067 * 2 ^ 59
def prefixEnd_1164067 : Nat := 4983230072969 + 3 ^ 40 * 1164067 * 2
def baseEnd_1164067 : Nat := 597725885037402316209059

theorem tailTrace_1164067 : CollatzResearch.WordTrace tailWord_1164067 prefixEnd_1164067 597725885037402316209059 := by
  unfold tailWord_1164067
  simp only [CollatzResearch.WordTrace]
  refine ⟨42457011473791540660890455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28304674315861027107260303 42457011473791540660890455)
  ·
    refine ⟨63685517210687310991335683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42457011473791540660890455 63685517210687310991335683)
    ·
      refine ⟨95528275816030966487003525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63685517210687310991335683 95528275816030966487003525)
      ·
        refine ⟨17911551715505806216313161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95528275816030966487003525 17911551715505806216313161)
        ·
          refine ⟨13433663786629354662234871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17911551715505806216313161 13433663786629354662234871)
          ·
            refine ⟨20150495679944031993352307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13433663786629354662234871 20150495679944031993352307)
            ·
              refine ⟨30225743519916047990028461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20150495679944031993352307 30225743519916047990028461)
              ·
                refine ⟨11334653819968517996260673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30225743519916047990028461 11334653819968517996260673)
                ·
                  refine ⟨8500990364976388497195505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11334653819968517996260673 8500990364976388497195505)
                  ·
                    refine ⟨6375742773732291372896629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8500990364976388497195505 6375742773732291372896629)
                    ·
                      refine ⟨597725885037402316209059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6375742773732291372896629 597725885037402316209059)
                      ·
                        rfl

theorem cell23_1164067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1164067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164067 prefixEnd_1164067 := by exact prefixLift 1164067
  have htrace : WordTrace (prefixWord ++ tailWord_1164067) baseStart_1164067 baseEnd_1164067 := by
    simpa [prefixWord, tailWord_1164067, baseEnd_1164067] using wordTrace_append hprefix tailTrace_1164067
  have hstable : (prefixWord ++ tailWord_1164067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164067).length < 2 ^ (prefixWord ++ tailWord_1164067).sum := by decide
  have hdescent : baseEnd_1164067 < baseStart_1164067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164087 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 4, 6]
def baseStart_1164087 : Nat := 118140960795 + 1164087 * 2 ^ 59
def prefixEnd_1164087 : Nat := 4983230072969 + 3 ^ 40 * 1164087 * 2
def baseEnd_1164087 : Nat := 199245384883497412652989

theorem tailTrace_1164087 : CollatzResearch.WordTrace tailWord_1164087 prefixEnd_1164087 199245384883497412652989 := by
  unfold tailWord_1164087
  simp only [CollatzResearch.WordTrace]
  refine ⟨42457740933719084076618515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28305160622479389384412343 42457740933719084076618515)
  ·
    refine ⟨63686611400578626114927773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42457740933719084076618515 63686611400578626114927773)
    ·
      refine ⟨23882479275216984793097915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63686611400578626114927773 23882479275216984793097915)
      ·
        refine ⟨35823718912825477189646873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23882479275216984793097915 35823718912825477189646873)
        ·
          refine ⟨26867789184619107892235155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35823718912825477189646873 26867789184619107892235155)
          ·
            refine ⟨40301683776928661838352733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26867789184619107892235155 40301683776928661838352733)
            ·
              refine ⟨15113131416348248189382275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40301683776928661838352733 15113131416348248189382275)
              ·
                refine ⟨22669697124522372284073413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15113131416348248189382275 22669697124522372284073413)
                ·
                  refine ⟨4250568210847944803263765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22669697124522372284073413 4250568210847944803263765)
                  ·
                    refine ⟨199245384883497412652989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4250568210847944803263765 199245384883497412652989)
                    ·
                      rfl

theorem cell23_1164087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_1164087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164087 prefixEnd_1164087 := by exact prefixLift 1164087
  have htrace : WordTrace (prefixWord ++ tailWord_1164087) baseStart_1164087 baseEnd_1164087 := by
    simpa [prefixWord, tailWord_1164087, baseEnd_1164087] using wordTrace_append hprefix tailTrace_1164087
  have hstable : (prefixWord ++ tailWord_1164087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164087).length < 2 ^ (prefixWord ++ tailWord_1164087).sum := by decide
  have hdescent : baseEnd_1164087 < baseStart_1164087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164102 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1164102 : Nat := 118140960795 + 1164102 * 2 ^ 59
def prefixEnd_1164102 : Nat := 4983230072969 + 3 ^ 40 * 1164102 * 2
def baseEnd_1164102 : Nat := 597743856860309679271399

theorem tailTrace_1164102 : CollatzResearch.WordTrace tailWord_1164102 prefixEnd_1164102 597743856860309679271399 := by
  unfold tailWord_1164102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326821500895773176200455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28305525352443161092276373 1326821500895773176200455)
  ·
    refine ⟨1990232251343659764300683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1326821500895773176200455 1990232251343659764300683)
    ·
      refine ⟨2985348377015489646451025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990232251343659764300683 2985348377015489646451025)
      ·
        refine ⟨2239011282761617234838269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2985348377015489646451025 2239011282761617234838269)
        ·
          refine ⟨839629231035606463064351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2239011282761617234838269 839629231035606463064351)
          ·
            refine ⟨1259443846553409694596527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839629231035606463064351 1259443846553409694596527)
            ·
              refine ⟨1889165769830114541894791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259443846553409694596527 1889165769830114541894791)
              ·
                refine ⟨2833748654745171812842187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889165769830114541894791 2833748654745171812842187)
                ·
                  refine ⟨4250622982117757719263281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833748654745171812842187 4250622982117757719263281)
                  ·
                    refine ⟨3187967236588318289447461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250622982117757719263281 3187967236588318289447461)
                    ·
                      refine ⟨597743856860309679271399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3187967236588318289447461 597743856860309679271399)
                      ·
                        rfl

theorem cell23_1164102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1164102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164102 prefixEnd_1164102 := by exact prefixLift 1164102
  have htrace : WordTrace (prefixWord ++ tailWord_1164102) baseStart_1164102 baseEnd_1164102 := by
    simpa [prefixWord, tailWord_1164102, baseEnd_1164102] using wordTrace_append hprefix tailTrace_1164102
  have hstable : (prefixWord ++ tailWord_1164102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164102).length < 2 ^ (prefixWord ++ tailWord_1164102).sum := by decide
  have hdescent : baseEnd_1164102 < baseStart_1164102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164114 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1164114 : Nat := 118140960795 + 1164114 * 2 ^ 59
def prefixEnd_1164114 : Nat := 4983230072969 + 3 ^ 40 * 1164114 * 2
def baseEnd_1164114 : Nat := 597750018628163632321343

theorem tailTrace_1164114 : CollatzResearch.WordTrace tailWord_1164114 prefixEnd_1164114 597750018628163632321343 := by
  unfold tailWord_1164114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614681426155316921962849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28305817136414178458567597 10614681426155316921962849)
  ·
    refine ⟨7961011069616487691472137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10614681426155316921962849 7961011069616487691472137)
    ·
      refine ⟨5970758302212365768604103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7961011069616487691472137 5970758302212365768604103)
      ·
        refine ⟨8956137453318548652906155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970758302212365768604103 8956137453318548652906155)
        ·
          refine ⟨13434206179977822979359233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8956137453318548652906155 13434206179977822979359233)
          ·
            refine ⟨10075654634983367234519425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13434206179977822979359233 10075654634983367234519425)
            ·
              refine ⟨7556740976237525425889569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10075654634983367234519425 7556740976237525425889569)
              ·
                refine ⟨5667555732178144069417177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7556740976237525425889569 5667555732178144069417177)
                ·
                  refine ⟨4250666799133608052062883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5667555732178144069417177 4250666799133608052062883)
                  ·
                    refine ⟨6376000198700412078094325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4250666799133608052062883 6376000198700412078094325)
                    ·
                      refine ⟨597750018628163632321343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6376000198700412078094325 597750018628163632321343)
                      ·
                        rfl

theorem cell23_1164114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1164114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164114 prefixEnd_1164114 := by exact prefixLift 1164114
  have htrace : WordTrace (prefixWord ++ tailWord_1164114) baseStart_1164114 baseEnd_1164114 := by
    simpa [prefixWord, tailWord_1164114, baseEnd_1164114] using wordTrace_append hprefix tailTrace_1164114
  have hstable : (prefixWord ++ tailWord_1164114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164114).length < 2 ^ (prefixWord ++ tailWord_1164114).sum := by decide
  have hdescent : baseEnd_1164114 < baseStart_1164114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164137 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_1164137 : Nat := 118140960795 + 1164137 * 2 ^ 59
def prefixEnd_1164137 : Nat := 4983230072969 + 3 ^ 40 * 1164137 * 2
def baseEnd_1164137 : Nat := 597761828683217042333737

theorem tailTrace_1164137 : CollatzResearch.WordTrace tailWord_1164137 prefixEnd_1164137 597761828683217042333737 := by
  unfold tailWord_1164137
  simp only [CollatzResearch.WordTrace]
  refine ⟨42459564583537942615938665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28306376389025295077292443 42459564583537942615938665)
  ·
    refine ⟨31844673437653456961953999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42459564583537942615938665 31844673437653456961953999)
    ·
      refine ⟨47767010156480185442930999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31844673437653456961953999 47767010156480185442930999)
      ·
        refine ⟨71650515234720278164396499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47767010156480185442930999 71650515234720278164396499)
        ·
          refine ⟨107475772852080417246594749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71650515234720278164396499 107475772852080417246594749)
          ·
            refine ⟨40303414819530156467473031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107475772852080417246594749 40303414819530156467473031)
            ·
              refine ⟨60455122229295234701209547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40303414819530156467473031 60455122229295234701209547)
              ·
                refine ⟨90682683343942852051814321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60455122229295234701209547 90682683343942852051814321)
                ·
                  refine ⟨68012012507957139038860741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90682683343942852051814321 68012012507957139038860741)
                  ·
                    refine ⟨12752252345241963569786389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68012012507957139038860741 12752252345241963569786389)
                    ·
                      refine ⟨597761828683217042333737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12752252345241963569786389 597761828683217042333737)
                      ·
                        rfl

theorem cell23_1164137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_1164137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164137 prefixEnd_1164137 := by exact prefixLift 1164137
  have htrace : WordTrace (prefixWord ++ tailWord_1164137) baseStart_1164137 baseEnd_1164137 := by
    simpa [prefixWord, tailWord_1164137, baseEnd_1164137] using wordTrace_append hprefix tailTrace_1164137
  have hstable : (prefixWord ++ tailWord_1164137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164137).length < 2 ^ (prefixWord ++ tailWord_1164137).sum := by decide
  have hdescent : baseEnd_1164137 < baseStart_1164137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164144 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_1164144 : Nat := 118140960795 + 1164144 * 2 ^ 59
def prefixEnd_1164144 : Nat := 4983230072969 + 3 ^ 40 * 1164144 * 2
def baseEnd_1164144 : Nat := 597765423047798514946205

theorem tailTrace_1164144 : CollatzResearch.WordTrace tailWord_1164144 prefixEnd_1164144 597765423047798514946205 := by
  unfold tailWord_1164144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229909947256291405721743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28306546596341721874295657 21229909947256291405721743)
  ·
    refine ⟨31844864920884437108582615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21229909947256291405721743 31844864920884437108582615)
    ·
      refine ⟨47767297381326655662873923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31844864920884437108582615 47767297381326655662873923)
      ·
        refine ⟨71650946071989983494310885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47767297381326655662873923 71650946071989983494310885)
        ·
          refine ⟨13434552388498121905183291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71650946071989983494310885 13434552388498121905183291)
          ·
            refine ⟨20151828582747182857774937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13434552388498121905183291 20151828582747182857774937)
            ·
              refine ⟨15113871437060387143331203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20151828582747182857774937 15113871437060387143331203)
              ·
                refine ⟨22670807155590580714996805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15113871437060387143331203 22670807155590580714996805)
                ·
                  refine ⟨4250776341673233884061901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22670807155590580714996805 4250776341673233884061901)
                  ·
                    refine ⟨1594041128127462706523213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4250776341673233884061901 1594041128127462706523213)
                    ·
                      refine ⟨597765423047798514946205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594041128127462706523213 597765423047798514946205)
                      ·
                        rfl

theorem cell23_1164144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_1164144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164144 prefixEnd_1164144 := by exact prefixLift 1164144
  have htrace : WordTrace (prefixWord ++ tailWord_1164144) baseStart_1164144 baseEnd_1164144 := by
    simpa [prefixWord, tailWord_1164144, baseEnd_1164144] using wordTrace_append hprefix tailTrace_1164144
  have hstable : (prefixWord ++ tailWord_1164144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164144).length < 2 ^ (prefixWord ++ tailWord_1164144).sum := by decide
  have hdescent : baseEnd_1164144 < baseStart_1164144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164164 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1164164 : Nat := 118140960795 + 1164164 * 2 ^ 59
def prefixEnd_1164164 : Nat := 4983230072969 + 3 ^ 40 * 1164164 * 2
def baseEnd_1164164 : Nat := 199258564220296145565371

theorem tailTrace_1164164 : CollatzResearch.WordTrace tailWord_1164164 prefixEnd_1164164 199258564220296145565371 := by
  unfold tailWord_1164164
  simp only [CollatzResearch.WordTrace]
  refine ⟨21230274677220063113585773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28307032902960084151447697 21230274677220063113585773)
  ·
    refine ⟨7961353003957523667594665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21230274677220063113585773 7961353003957523667594665)
    ·
      refine ⟨5971014752968142750695999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7961353003957523667594665 5971014752968142750695999)
      ·
        refine ⟨8956522129452214126043999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971014752968142750695999 8956522129452214126043999)
        ·
          refine ⟨13434783194178321189065999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8956522129452214126043999 13434783194178321189065999)
          ·
            refine ⟨20152174791267481783598999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13434783194178321189065999 20152174791267481783598999)
            ·
              refine ⟨30228262186901222675398499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20152174791267481783598999 30228262186901222675398499)
              ·
                refine ⟨45342393280351834013097749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30228262186901222675398499 45342393280351834013097749)
                ·
                  refine ⟨2125424685016492219363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45342393280351834013097749 2125424685016492219363957)
                  ·
                    refine ⟨199258564220296145565371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2125424685016492219363957 199258564220296145565371)
                    ·
                      rfl

theorem cell23_1164164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1164164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164164 prefixEnd_1164164 := by exact prefixLift 1164164
  have htrace : WordTrace (prefixWord ++ tailWord_1164164) baseStart_1164164 baseEnd_1164164 := by
    simpa [prefixWord, tailWord_1164164, baseEnd_1164164] using wordTrace_append hprefix tailTrace_1164164
  have hstable : (prefixWord ++ tailWord_1164164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164164).length < 2 ^ (prefixWord ++ tailWord_1164164).sum := by decide
  have hdescent : baseEnd_1164164 < baseStart_1164164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164181 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1164181 : Nat := 118140960795 + 1164181 * 2 ^ 59
def prefixEnd_1164181 : Nat := 4983230072969 + 3 ^ 40 * 1164181 * 2
def baseEnd_1164181 : Nat := 199261473944004956727845

theorem tailTrace_1164181 : CollatzResearch.WordTrace tailWord_1164181 prefixEnd_1164181 199261473944004956727845 := by
  unfold tailWord_1164181
  simp only [CollatzResearch.WordTrace]
  refine ⟨42461169395378538130540397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28307446263585692087026931 42461169395378538130540397)
  ·
    refine ⟨15922938523266951798952649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42461169395378538130540397 15922938523266951798952649)
    ·
      refine ⟨11942203892450213849214487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15922938523266951798952649 11942203892450213849214487)
      ·
        refine ⟨17913305838675320773821731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11942203892450213849214487 17913305838675320773821731)
        ·
          refine ⟨26869958758012981160732597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17913305838675320773821731 26869958758012981160732597)
          ·
            refine ⟨2519058633563716983818681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26869958758012981160732597 2519058633563716983818681)
            ·
              refine ⟨1889293975172787737864011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519058633563716983818681 1889293975172787737864011)
              ·
                refine ⟨2833940962759181606796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889293975172787737864011 2833940962759181606796017)
                ·
                  refine ⟨2125455722069386205097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2833940962759181606796017 2125455722069386205097013)
                  ·
                    refine ⟨199261473944004956727845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2125455722069386205097013 199261473944004956727845)
                    ·
                      rfl

theorem cell23_1164181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1164181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164181 prefixEnd_1164181 := by exact prefixLift 1164181
  have htrace : WordTrace (prefixWord ++ tailWord_1164181) baseStart_1164181 baseEnd_1164181 := by
    simpa [prefixWord, tailWord_1164181, baseEnd_1164181] using wordTrace_append hprefix tailTrace_1164181
  have hstable : (prefixWord ++ tailWord_1164181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164181).length < 2 ^ (prefixWord ++ tailWord_1164181).sum := by decide
  have hdescent : baseEnd_1164181 < baseStart_1164181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164201 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 2, 4, 2]
def baseStart_1164201 : Nat := 118140960795 + 1164201 * 2 ^ 59
def prefixEnd_1164201 : Nat := 4983230072969 + 3 ^ 40 * 1164201 * 2
def baseEnd_1164201 : Nat := 597794691445104791933443

theorem tailTrace_1164201 : CollatzResearch.WordTrace tailWord_1164201 prefixEnd_1164201 597794691445104791933443 := by
  unfold tailWord_1164201
  simp only [CollatzResearch.WordTrace]
  refine ⟨42461898855306081546268457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28307932570204054364178971 42461898855306081546268457)
  ·
    refine ⟨31846424141479561159701343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42461898855306081546268457 31846424141479561159701343)
    ·
      refine ⟨47769636212219341739552015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31846424141479561159701343 47769636212219341739552015)
      ·
        refine ⟨71654454318329012609328023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47769636212219341739552015 71654454318329012609328023)
        ·
          refine ⟨107481681477493518913992035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71654454318329012609328023 107481681477493518913992035)
          ·
            refine ⟨161222522216240278370988053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107481681477493518913992035 161222522216240278370988053)
            ·
              refine ⟨7557305728886263048640065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161222522216240278370988053 7557305728886263048640065)
              ·
                refine ⟨5667979296664697286480049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7557305728886263048640065 5667979296664697286480049)
                ·
                  refine ⟨4250984472498522964860037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5667979296664697286480049 4250984472498522964860037)
                  ·
                    refine ⟨797059588593473055911257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250984472498522964860037 797059588593473055911257)
                    ·
                      refine ⟨597794691445104791933443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797059588593473055911257 597794691445104791933443)
                      ·
                        rfl

theorem cell23_1164201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4, 2].length) (baseStart_1164201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164201 prefixEnd_1164201 := by exact prefixLift 1164201
  have htrace : WordTrace (prefixWord ++ tailWord_1164201) baseStart_1164201 baseEnd_1164201 := by
    simpa [prefixWord, tailWord_1164201, baseEnd_1164201] using wordTrace_append hprefix tailTrace_1164201
  have hstable : (prefixWord ++ tailWord_1164201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164201).length < 2 ^ (prefixWord ++ tailWord_1164201).sum := by decide
  have hdescent : baseEnd_1164201 < baseStart_1164201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164238 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_1164238 : Nat := 118140960795 + 1164238 * 2 ^ 59
def prefixEnd_1164238 : Nat := 4983230072969 + 3 ^ 40 * 1164238 * 2
def baseEnd_1164238 : Nat := 597813690229321147170773

theorem tailTrace_1164238 : CollatzResearch.WordTrace tailWord_1164238 prefixEnd_1164238 597813690229321147170773 := by
  unfold tailWord_1164238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307906044521504608170671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28308832237448024576910245 5307906044521504608170671)
  ·
    refine ⟨7961859066782256912256007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5307906044521504608170671 7961859066782256912256007)
    ·
      refine ⟨11942788600173385368384011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7961859066782256912256007 11942788600173385368384011)
      ·
        refine ⟨17914182900260078052576017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11942788600173385368384011 17914182900260078052576017)
        ·
          refine ⟨13435637175195058539432013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17914182900260078052576017 13435637175195058539432013)
          ·
            refine ⟨5038363940698146952287005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13435637175195058539432013 5038363940698146952287005)
            ·
              refine ⟨1889386477761805107107627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038363940698146952287005 1889386477761805107107627)
              ·
                refine ⟨2834079716642707660661441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889386477761805107107627 2834079716642707660661441)
                ·
                  refine ⟨2125559787482030745496081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834079716642707660661441 2125559787482030745496081)
                  ·
                    refine ⟨1594169840611523059122061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2125559787482030745496081 1594169840611523059122061)
                    ·
                      refine ⟨597813690229321147170773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594169840611523059122061 597813690229321147170773)
                      ·
                        rfl

theorem cell23_1164238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_1164238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164238 prefixEnd_1164238 := by exact prefixLift 1164238
  have htrace : WordTrace (prefixWord ++ tailWord_1164238) baseStart_1164238 baseEnd_1164238 := by
    simpa [prefixWord, tailWord_1164238, baseEnd_1164238] using wordTrace_append hprefix tailTrace_1164238
  have hstable : (prefixWord ++ tailWord_1164238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164238).length < 2 ^ (prefixWord ++ tailWord_1164238).sum := by decide
  have hdescent : baseEnd_1164238 < baseStart_1164238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164258 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1164258 : Nat := 118140960795 + 1164258 * 2 ^ 59
def prefixEnd_1164258 : Nat := 4983230072969 + 3 ^ 40 * 1164258 * 2
def baseEnd_1164258 : Nat := 66424884426934563213409

theorem tailTrace_1164258 : CollatzResearch.WordTrace tailWord_1164258 prefixEnd_1164258 66424884426934563213409 := by
  unfold tailWord_1164258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615994454024895070273357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28309318544066386854062285 10615994454024895070273357)
  ·
    refine ⟨3980997920259335651352509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10615994454024895070273357 3980997920259335651352509)
    ·
      refine ⟨1492874220097250869257191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3980997920259335651352509 1492874220097250869257191)
      ·
        refine ⟨2239311330145876303885787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492874220097250869257191 2239311330145876303885787)
        ·
          refine ⟨3358966995218814455828681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239311330145876303885787 3358966995218814455828681)
          ·
            refine ⟨2519225246414110841871511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3358966995218814455828681 2519225246414110841871511)
            ·
              refine ⟨3778837869621166262807267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519225246414110841871511 3778837869621166262807267)
              ·
                refine ⟨5668256804431749394210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778837869621166262807267 5668256804431749394210901)
                ·
                  refine ⟨66424884426934563213409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5668256804431749394210901 66424884426934563213409)
                  ·
                    rfl

theorem cell23_1164258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1164258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164258 prefixEnd_1164258 := by exact prefixLift 1164258
  have htrace : WordTrace (prefixWord ++ tailWord_1164258) baseStart_1164258 baseEnd_1164258 := by
    simpa [prefixWord, tailWord_1164258, baseEnd_1164258] using wordTrace_append hprefix tailTrace_1164258
  have hstable : (prefixWord ++ tailWord_1164258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164258).length < 2 ^ (prefixWord ++ tailWord_1164258).sum := by decide
  have hdescent : baseEnd_1164258 < baseStart_1164258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164302 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1164302 : Nat := 118140960795 + 1164302 * 2 ^ 59
def prefixEnd_1164302 : Nat := 4983230072969 + 3 ^ 40 * 1164302 * 2
def baseEnd_1164302 : Nat := 597846552991208896770479

theorem tailTrace_1164302 : CollatzResearch.WordTrace tailWord_1164302 prefixEnd_1164302 597846552991208896770479 := by
  unfold tailWord_1164302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308197828492521974461895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28310388418626783863796773 5308197828492521974461895)
  ·
    refine ⟨7962296742738782961692843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5308197828492521974461895 7962296742738782961692843)
    ·
      refine ⟨11943445114108174442539265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7962296742738782961692843 11943445114108174442539265)
      ·
        refine ⟨8957583835581130831904449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11943445114108174442539265 8957583835581130831904449)
        ·
          refine ⟨6718187876685848123928337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8957583835581130831904449 6718187876685848123928337)
          ·
            refine ⟨5038640907514386092946253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6718187876685848123928337 5038640907514386092946253)
            ·
              refine ⟨1889490340317894784854845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038640907514386092946253 1889490340317894784854845)
              ·
                refine ⟨708558877619210544320567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889490340317894784854845 708558877619210544320567)
                ·
                  refine ⟨1062838316428815816480851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708558877619210544320567 1062838316428815816480851)
                  ·
                    refine ⟨1594257474643223724721277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1062838316428815816480851 1594257474643223724721277)
                    ·
                      refine ⟨597846552991208896770479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594257474643223724721277 597846552991208896770479)
                      ·
                        rfl

theorem cell23_1164302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1164302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164302 prefixEnd_1164302 := by exact prefixLift 1164302
  have htrace : WordTrace (prefixWord ++ tailWord_1164302) baseStart_1164302 baseEnd_1164302 := by
    simpa [prefixWord, tailWord_1164302, baseEnd_1164302] using wordTrace_append hprefix tailTrace_1164302
  have hstable : (prefixWord ++ tailWord_1164302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164302).length < 2 ^ (prefixWord ++ tailWord_1164302).sum := by decide
  have hdescent : baseEnd_1164302 < baseStart_1164302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_1164304 : Nat := 118140960795 + 1164304 * 2 ^ 59
def prefixEnd_1164304 : Nat := 4983230072969 + 3 ^ 40 * 1164304 * 2
def baseEnd_1164304 : Nat := 597847579952517888945469

theorem tailTrace_1164304 : CollatzResearch.WordTrace tailWord_1164304 prefixEnd_1164304 597847579952517888945469 := by
  unfold tailWord_1164304
  simp only [CollatzResearch.WordTrace]
  refine ⟨21232827786966465068633983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28310437049288620091511977 21232827786966465068633983)
  ·
    refine ⟨31849241680449697602950975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21232827786966465068633983 31849241680449697602950975)
    ·
      refine ⟨47773862520674546404426463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31849241680449697602950975 47773862520674546404426463)
      ·
        refine ⟨71660793781011819606639695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47773862520674546404426463 71660793781011819606639695)
        ·
          refine ⟨107491190671517729409959543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71660793781011819606639695 107491190671517729409959543)
          ·
            refine ⟨161236786007276594114939315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107491190671517729409959543 161236786007276594114939315)
            ·
              refine ⟨241855179010914891172408973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161236786007276594114939315 241855179010914891172408973)
              ·
                refine ⟨90695692129093084189653365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241855179010914891172408973 90695692129093084189653365)
                ·
                  refine ⟨8502721137102476642780003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90695692129093084189653365 8502721137102476642780003)
                  ·
                    refine ⟨12754081705653714964170005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8502721137102476642780003 12754081705653714964170005)
                    ·
                      refine ⟨597847579952517888945469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12754081705653714964170005 597847579952517888945469)
                      ·
                        rfl

theorem cell23_1164304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_1164304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164304 prefixEnd_1164304 := by exact prefixLift 1164304
  have htrace : WordTrace (prefixWord ++ tailWord_1164304) baseStart_1164304 baseEnd_1164304 := by
    simpa [prefixWord, tailWord_1164304, baseEnd_1164304] using wordTrace_append hprefix tailTrace_1164304
  have hstable : (prefixWord ++ tailWord_1164304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164304).length < 2 ^ (prefixWord ++ tailWord_1164304).sum := by decide
  have hdescent : baseEnd_1164304 < baseStart_1164304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164321 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1164321 : Nat := 118140960795 + 1164321 * 2 ^ 59
def prefixEnd_1164321 : Nat := 4983230072969 + 3 ^ 40 * 1164321 * 2
def baseEnd_1164321 : Nat := 597856309123644322432891

theorem tailTrace_1164321 : CollatzResearch.WordTrace tailWord_1164321 prefixEnd_1164321 597856309123644322432891 := by
  unfold tailWord_1164321
  simp only [CollatzResearch.WordTrace]
  refine ⟨42466275614871342040636817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28310850409914228027091211 42466275614871342040636817)
  ·
    refine ⟨31849706711153506530477613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42466275614871342040636817 31849706711153506530477613)
    ·
      refine ⟨11943640016682564948929105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31849706711153506530477613 11943640016682564948929105)
      ·
        refine ⟨8957730012511923711696829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11943640016682564948929105 8957730012511923711696829)
        ·
          refine ⟨3359148754691971391886311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8957730012511923711696829 3359148754691971391886311)
          ·
            refine ⟨5038723132037957087829467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359148754691971391886311 5038723132037957087829467)
            ·
              refine ⟨7558084698056935631744201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038723132037957087829467 7558084698056935631744201)
              ·
                refine ⟨5668563523542701723808151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7558084698056935631744201 5668563523542701723808151)
                ·
                  refine ⟨8502845285314052585712227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668563523542701723808151 8502845285314052585712227)
                  ·
                    refine ⟨12754267927971078878568341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8502845285314052585712227 12754267927971078878568341)
                    ·
                      refine ⟨597856309123644322432891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12754267927971078878568341 597856309123644322432891)
                      ·
                        rfl

theorem cell23_1164321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1164321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164321 prefixEnd_1164321 := by exact prefixLift 1164321
  have htrace : WordTrace (prefixWord ++ tailWord_1164321) baseStart_1164321 baseEnd_1164321 := by
    simpa [prefixWord, tailWord_1164321, baseEnd_1164321] using wordTrace_append hprefix tailTrace_1164321
  have hstable : (prefixWord ++ tailWord_1164321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164321).length < 2 ^ (prefixWord ++ tailWord_1164321).sum := by decide
  have hdescent : baseEnd_1164321 < baseStart_1164321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164342 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1164342 : Nat := 118140960795 + 1164342 * 2 ^ 59
def prefixEnd_1164342 : Nat := 4983230072969 + 3 ^ 40 * 1164342 * 2
def baseEnd_1164342 : Nat := 597867092217388740270295

theorem tailTrace_1164342 : CollatzResearch.WordTrace tailWord_1164342 prefixEnd_1164342 597867092217388740270295 := by
  unfold tailWord_1164342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2654190096737203914196955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28311361031863508418100853 2654190096737203914196955)
  ·
    refine ⟨3981285145105805871295433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2654190096737203914196955 3981285145105805871295433)
    ·
      refine ⟨2985963858829354403471575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981285145105805871295433 2985963858829354403471575)
      ·
        refine ⟨4478945788244031605207363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985963858829354403471575 4478945788244031605207363)
        ·
          refine ⟨6718418682366047407811045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478945788244031605207363 6718418682366047407811045)
          ·
            refine ⟨1259703502943633888964571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6718418682366047407811045 1259703502943633888964571)
            ·
              refine ⟨1889555254415450833446857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259703502943633888964571 1889555254415450833446857)
              ·
                refine ⟨1417166440811588125085143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889555254415450833446857 1417166440811588125085143)
                ·
                  refine ⟨2125749661217382187627715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417166440811588125085143 2125749661217382187627715)
                  ·
                    refine ⟨3188624491826073281441573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125749661217382187627715 3188624491826073281441573)
                    ·
                      refine ⟨597867092217388740270295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3188624491826073281441573 597867092217388740270295)
                      ·
                        rfl

theorem cell23_1164342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1164342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164342 prefixEnd_1164342 := by exact prefixLift 1164342
  have htrace : WordTrace (prefixWord ++ tailWord_1164342) baseStart_1164342 baseEnd_1164342 := by
    simpa [prefixWord, tailWord_1164342, baseEnd_1164342] using wordTrace_append hprefix tailTrace_1164342
  have hstable : (prefixWord ++ tailWord_1164342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164342).length < 2 ^ (prefixWord ++ tailWord_1164342).sum := by decide
  have hdescent : baseEnd_1164342 < baseStart_1164342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164345 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1164345 : Nat := 118140960795 + 1164345 * 2 ^ 59
def prefixEnd_1164345 : Nat := 4983230072969 + 3 ^ 40 * 1164345 * 2
def baseEnd_1164345 : Nat := 597868632659352228532781

theorem tailTrace_1164345 : CollatzResearch.WordTrace tailWord_1164345 prefixEnd_1164345 597868632659352228532781 := by
  unfold tailWord_1164345
  simp only [CollatzResearch.WordTrace]
  refine ⟨42467150966784394139510489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28311433977856262759673659 42467150966784394139510489)
  ·
    refine ⟨31850363225088295604632867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42467150966784394139510489 31850363225088295604632867)
    ·
      refine ⟨47775544837632443406949301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31850363225088295604632867 47775544837632443406949301)
      ·
        refine ⟨4478957328528041569401497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47775544837632443406949301 4478957328528041569401497)
        ·
          refine ⟨3359217996396031177051123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4478957328528041569401497 3359217996396031177051123)
          ·
            refine ⟨5038826994594046765576685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359217996396031177051123 5038826994594046765576685)
            ·
              refine ⟨1889560122972767537091257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038826994594046765576685 1889560122972767537091257)
              ·
                refine ⟨1417170092229575652818443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889560122972767537091257 1417170092229575652818443)
                ·
                  refine ⟨2125755138344363479227665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417170092229575652818443 2125755138344363479227665)
                  ·
                    refine ⟨1594316353758272609420749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2125755138344363479227665 1594316353758272609420749)
                    ·
                      refine ⟨597868632659352228532781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594316353758272609420749 597868632659352228532781)
                      ·
                        rfl

theorem cell23_1164345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1164345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164345 prefixEnd_1164345 := by exact prefixLift 1164345
  have htrace : WordTrace (prefixWord ++ tailWord_1164345) baseStart_1164345 baseEnd_1164345 := by
    simpa [prefixWord, tailWord_1164345, baseEnd_1164345] using wordTrace_append hprefix tailTrace_1164345
  have hstable : (prefixWord ++ tailWord_1164345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164345).length < 2 ^ (prefixWord ++ tailWord_1164345).sum := by decide
  have hdescent : baseEnd_1164345 < baseStart_1164345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164382 : List Nat := [4, 4, 1, 1, 1, 3, 1, 8]
def baseStart_1164382 : Nat := 118140960795 + 1164382 * 2 ^ 59
def prefixEnd_1164382 : Nat := 4983230072969 + 3 ^ 40 * 1164382 * 2
def baseEnd_1164382 : Nat := 22143986349761799398893

theorem tailTrace_1164382 : CollatzResearch.WordTrace tailWord_1164382 prefixEnd_1164382 22143986349761799398893 := by
  unfold tailWord_1164382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308562558456293682325925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28312333645100232972404933 5308562558456293682325925)
  ·
    refine ⟨995355479710555065436111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5308562558456293682325925 995355479710555065436111)
    ·
      refine ⟨1493033219565832598154167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995355479710555065436111 1493033219565832598154167)
      ·
        refine ⟨2239549829348748897231251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493033219565832598154167 2239549829348748897231251)
        ·
          refine ⟨3359324744023123345846877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239549829348748897231251 3359324744023123345846877)
          ·
            refine ⟨1259746779008671254692579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3359324744023123345846877 1259746779008671254692579)
            ·
              refine ⟨1889620168513006882038869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259746779008671254692579 1889620168513006882038869)
              ·
                refine ⟨22143986349761799398893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1889620168513006882038869 22143986349761799398893)
                ·
                  rfl

theorem cell23_1164382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_1164382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164382 prefixEnd_1164382 := by exact prefixLift 1164382
  have htrace : WordTrace (prefixWord ++ tailWord_1164382) baseStart_1164382 baseEnd_1164382 := by
    simpa [prefixWord, tailWord_1164382, baseEnd_1164382] using wordTrace_append hprefix tailTrace_1164382
  have hstable : (prefixWord ++ tailWord_1164382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164382).length < 2 ^ (prefixWord ++ tailWord_1164382).sum := by decide
  have hdescent : baseEnd_1164382 < baseStart_1164382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164391 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1164391 : Nat := 118140960795 + 1164391 * 2 ^ 59
def prefixEnd_1164391 : Nat := 4983230072969 + 3 ^ 40 * 1164391 * 2
def baseEnd_1164391 : Nat := 199297417589819682852523

theorem tailTrace_1164391 : CollatzResearch.WordTrace tailWord_1164391 prefixEnd_1164391 199297417589819682852523 := by
  unfold tailWord_1164391
  simp only [CollatzResearch.WordTrace]
  refine ⟨42468828724617743995685027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28312552483078495997123351 42468828724617743995685027)
  ·
    refine ⟨63703243086926615993527541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42468828724617743995685027 63703243086926615993527541)
    ·
      refine ⟨5972179039399370249393207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63703243086926615993527541 5972179039399370249393207)
      ·
        refine ⟨8958268559099055374089811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5972179039399370249393207 8958268559099055374089811)
        ·
          refine ⟨13437402838648583061134717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8958268559099055374089811 13437402838648583061134717)
          ·
            refine ⟨5039026064493218647925519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13437402838648583061134717 5039026064493218647925519)
            ·
              refine ⟨7558539096739827971888279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039026064493218647925519 7558539096739827971888279)
              ·
                refine ⟨11337808645109741957832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7558539096739827971888279 11337808645109741957832419)
                ·
                  refine ⟨17006712967664612936748629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11337808645109741957832419 17006712967664612936748629)
                  ·
                    refine ⟨199297417589819682852523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17006712967664612936748629 199297417589819682852523)
                    ·
                      rfl

theorem cell23_1164391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1164391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164391 prefixEnd_1164391 := by exact prefixLift 1164391
  have htrace : WordTrace (prefixWord ++ tailWord_1164391) baseStart_1164391 baseEnd_1164391 := by
    simpa [prefixWord, tailWord_1164391, baseEnd_1164391] using wordTrace_append hprefix tailTrace_1164391
  have hstable : (prefixWord ++ tailWord_1164391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164391).length < 2 ^ (prefixWord ++ tailWord_1164391).sum := by decide
  have hdescent : baseEnd_1164391 < baseStart_1164391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164392 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1164392 : Nat := 118140960795 + 1164392 * 2 ^ 59
def prefixEnd_1164392 : Nat := 4983230072969 + 3 ^ 40 * 1164392 * 2
def baseEnd_1164392 : Nat := 597892766250113544645065

theorem tailTrace_1164392 : CollatzResearch.WordTrace tailWord_1164392 prefixEnd_1164392 597892766250113544645065 := by
  unfold tailWord_1164392
  simp only [CollatzResearch.WordTrace]
  refine ⟨21234432598807060583235715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28312576798409414110980953 21234432598807060583235715)
  ·
    refine ⟨31851648898210590874853573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21234432598807060583235715 31851648898210590874853573)
    ·
      refine ⟨5972184168414485789035045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31851648898210590874853573 5972184168414485789035045)
      ·
        refine ⟨1119784531577716085444071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5972184168414485789035045 1119784531577716085444071)
        ·
          refine ⟨1679676797366574128166107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119784531577716085444071 1679676797366574128166107)
          ·
            refine ⟨2519515196049861192249161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679676797366574128166107 2519515196049861192249161)
            ·
              refine ⟨1889636397037395894186871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519515196049861192249161 1889636397037395894186871)
              ·
                refine ⟨2834454595556093841280307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889636397037395894186871 2834454595556093841280307)
                ·
                  refine ⟨4251681893334140761920461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834454595556093841280307 4251681893334140761920461)
                  ·
                    refine ⟨1594380710000302785720173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4251681893334140761920461 1594380710000302785720173)
                    ·
                      refine ⟨597892766250113544645065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594380710000302785720173 597892766250113544645065)
                      ·
                        rfl

theorem cell23_1164392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1164392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164392 prefixEnd_1164392 := by exact prefixLift 1164392
  have htrace : WordTrace (prefixWord ++ tailWord_1164392) baseStart_1164392 baseEnd_1164392 := by
    simpa [prefixWord, tailWord_1164392, baseEnd_1164392] using wordTrace_append hprefix tailTrace_1164392
  have hstable : (prefixWord ++ tailWord_1164392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164392).length < 2 ^ (prefixWord ++ tailWord_1164392).sum := by decide
  have hdescent : baseEnd_1164392 < baseStart_1164392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164401 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_1164401 : Nat := 118140960795 + 1164401 * 2 ^ 59
def prefixEnd_1164401 : Nat := 4983230072969 + 3 ^ 40 * 1164401 * 2
def baseEnd_1164401 : Nat := 597897387576004009432523

theorem tailTrace_1164401 : CollatzResearch.WordTrace tailWord_1164401 prefixEnd_1164401 597897387576004009432523 := by
  unfold tailWord_1164401
  simp only [CollatzResearch.WordTrace]
  refine ⟨42469193454581515703549057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28312795636387677135699371 42469193454581515703549057)
  ·
    refine ⟨31851895090936136777661793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42469193454581515703549057 31851895090936136777661793)
    ·
      refine ⟨23888921318202102583246345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31851895090936136777661793 23888921318202102583246345)
      ·
        refine ⟨17916690988651576937434759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23888921318202102583246345 17916690988651576937434759)
        ·
          refine ⟨26875036482977365406152139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17916690988651576937434759 26875036482977365406152139)
          ·
            refine ⟨40312554724466048109228209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26875036482977365406152139 40312554724466048109228209)
            ·
              refine ⟨30234416043349536081921157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40312554724466048109228209 30234416043349536081921157)
              ·
                refine ⟨5668953008128038015360217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30234416043349536081921157 5668953008128038015360217)
                ·
                  refine ⟨4251714756096028511520163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668953008128038015360217 4251714756096028511520163)
                  ·
                    refine ⟨6377572134144042767280245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4251714756096028511520163 6377572134144042767280245)
                    ·
                      refine ⟨597897387576004009432523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6377572134144042767280245 597897387576004009432523)
                      ·
                        rfl

theorem cell23_1164401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_1164401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164401 prefixEnd_1164401 := by exact prefixLift 1164401
  have htrace : WordTrace (prefixWord ++ tailWord_1164401) baseStart_1164401 baseEnd_1164401 := by
    simpa [prefixWord, tailWord_1164401, baseEnd_1164401] using wordTrace_append hprefix tailTrace_1164401
  have hstable : (prefixWord ++ tailWord_1164401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164401).length < 2 ^ (prefixWord ++ tailWord_1164401).sum := by decide
  have hdescent : baseEnd_1164401 < baseStart_1164401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164448 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1164448 : Nat := 118140960795 + 1164448 * 2 ^ 59
def prefixEnd_1164448 : Nat := 4983230072969 + 3 ^ 40 * 1164448 * 2
def baseEnd_1164448 : Nat := 597921521166765325544807

theorem tailTrace_1164448 : CollatzResearch.WordTrace tailWord_1164448 prefixEnd_1164448 597921521166765325544807 := by
  unfold tailWord_1164448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21235453842705621365254999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28313938456940828487006665 21235453842705621365254999)
  ·
    refine ⟨31853180764058432047882499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21235453842705621365254999 31853180764058432047882499)
    ·
      refine ⟨47779771146087648071823749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31853180764058432047882499 47779771146087648071823749)
      ·
        refine ⟨8958707089891434013466953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47779771146087648071823749 8958707089891434013466953)
        ·
          refine ⟨6719030317418575510100215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8958707089891434013466953 6719030317418575510100215)
          ·
            refine ⟨10078545476127863265150323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719030317418575510100215 10078545476127863265150323)
            ·
              refine ⟨15117818214191794897725485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078545476127863265150323 15117818214191794897725485)
              ·
                refine ⟨5669181830321923086647057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15117818214191794897725485 5669181830321923086647057)
                ·
                  refine ⟨4251886372741442314985293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669181830321923086647057 4251886372741442314985293)
                  ·
                    refine ⟨1594457389778040868119485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4251886372741442314985293 1594457389778040868119485)
                    ·
                      refine ⟨597921521166765325544807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594457389778040868119485 597921521166765325544807)
                      ·
                        rfl

theorem cell23_1164448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1164448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164448 prefixEnd_1164448 := by exact prefixLift 1164448
  have htrace : WordTrace (prefixWord ++ tailWord_1164448) baseStart_1164448 baseEnd_1164448 := by
    simpa [prefixWord, tailWord_1164448, baseEnd_1164448] using wordTrace_append hprefix tailTrace_1164448
  have hstable : (prefixWord ++ tailWord_1164448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164448).length < 2 ^ (prefixWord ++ tailWord_1164448).sum := by decide
  have hdescent : baseEnd_1164448 < baseStart_1164448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164449 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1164449 : Nat := 118140960795 + 1164449 * 2 ^ 59
def prefixEnd_1164449 : Nat := 4983230072969 + 3 ^ 40 * 1164449 * 2
def baseEnd_1164449 : Nat := 597922034647419821632303

theorem tailTrace_1164449 : CollatzResearch.WordTrace tailWord_1164449 prefixEnd_1164449 597922034647419821632303 := by
  unfold tailWord_1164449
  simp only [CollatzResearch.WordTrace]
  refine ⟨42470944158407619901296401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28313962772271746600864267 42470944158407619901296401)
  ·
    refine ⟨31853208118805714925972301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42470944158407619901296401 31853208118805714925972301)
    ·
      refine ⟨11944953044552143097239613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31853208118805714925972301 11944953044552143097239613)
      ·
        refine ⟨4479357391707053661464855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11944953044552143097239613 4479357391707053661464855)
        ·
          refine ⟨6719036087560580492197283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479357391707053661464855 6719036087560580492197283)
          ·
            refine ⟨10078554131340870738295925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719036087560580492197283 10078554131340870738295925)
            ·
              refine ⟨944864449813206631715243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10078554131340870738295925 944864449813206631715243)
              ·
                refine ⟨1417296674719809947572865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944864449813206631715243 1417296674719809947572865)
                ·
                  refine ⟨1062972506039857460679649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417296674719809947572865 1062972506039857460679649)
                  ·
                    refine ⟨797229379529893095509737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1062972506039857460679649 797229379529893095509737)
                    ·
                      refine ⟨597922034647419821632303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797229379529893095509737 597922034647419821632303)
                      ·
                        rfl

theorem cell23_1164449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1164449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164449 prefixEnd_1164449 := by exact prefixLift 1164449
  have htrace : WordTrace (prefixWord ++ tailWord_1164449) baseStart_1164449 baseEnd_1164449 := by
    simpa [prefixWord, tailWord_1164449, baseEnd_1164449] using wordTrace_append hprefix tailTrace_1164449
  have hstable : (prefixWord ++ tailWord_1164449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164449).length < 2 ^ (prefixWord ++ tailWord_1164449).sum := by decide
  have hdescent : baseEnd_1164449 < baseStart_1164449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164488 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1164488 : Nat := 118140960795 + 1164488 * 2 ^ 59
def prefixEnd_1164488 : Nat := 4983230072969 + 3 ^ 40 * 1164488 * 2
def baseEnd_1164488 : Nat := 597942060392945169044623

theorem tailTrace_1164488 : CollatzResearch.WordTrace tailWord_1164488 prefixEnd_1164488 597942060392945169044623 := by
  unfold tailWord_1164488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21236183302633164780983059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28314911070177553041310745 21236183302633164780983059)
  ·
    refine ⟨31854274953949747171474589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21236183302633164780983059 31854274953949747171474589)
    ·
      refine ⟨11945353107731155189302971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31854274953949747171474589 11945353107731155189302971)
      ·
        refine ⟨17918029661596732783954457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11945353107731155189302971 17918029661596732783954457)
        ·
          refine ⟨13438522246197549587965843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17918029661596732783954457 13438522246197549587965843)
          ·
            refine ⟨20157783369296324381948765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13438522246197549587965843 20157783369296324381948765)
            ·
              refine ⟨7559168763486121643230787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20157783369296324381948765 7559168763486121643230787)
              ·
                refine ⟨11338753145229182464846181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7559168763486121643230787 11338753145229182464846181)
                ·
                  refine ⟨2126016214730471712158659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11338753145229182464846181 2126016214730471712158659)
                  ·
                    refine ⟨3189024322095707568237989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126016214730471712158659 3189024322095707568237989)
                    ·
                      refine ⟨597942060392945169044623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3189024322095707568237989 597942060392945169044623)
                      ·
                        rfl

theorem cell23_1164488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1164488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164488 prefixEnd_1164488 := by exact prefixLift 1164488
  have htrace : WordTrace (prefixWord ++ tailWord_1164488) baseStart_1164488 baseEnd_1164488 := by
    simpa [prefixWord, tailWord_1164488, baseEnd_1164488] using wordTrace_append hprefix tailTrace_1164488
  have hstable : (prefixWord ++ tailWord_1164488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164488).length < 2 ^ (prefixWord ++ tailWord_1164488).sum := by decide
  have hdescent : baseEnd_1164488 < baseStart_1164488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164491 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_1164491 : Nat := 118140960795 + 1164491 * 2 ^ 59
def prefixEnd_1164491 : Nat := 4983230072969 + 3 ^ 40 * 1164491 * 2
def baseEnd_1164491 : Nat := 597943600834908657307109

theorem tailTrace_1164491 : CollatzResearch.WordTrace tailWord_1164491 prefixEnd_1164491 597943600834908657307109 := by
  unfold tailWord_1164491
  simp only [CollatzResearch.WordTrace]
  refine ⟨42472476024255461074325327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28314984016170307382883551 42472476024255461074325327)
  ·
    refine ⟨63708714036383191611487991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42472476024255461074325327 63708714036383191611487991)
    ·
      refine ⟨95563071054574787417231987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63708714036383191611487991 95563071054574787417231987)
      ·
        refine ⟨143344606581862181125847981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95563071054574787417231987 143344606581862181125847981)
        ·
          refine ⟨53754227468198317922192993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143344606581862181125847981 53754227468198317922192993)
          ·
            refine ⟨40315670601148738441644745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53754227468198317922192993 40315670601148738441644745)
            ·
              refine ⟨30236752950861553831233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40315670601148738441644745 30236752950861553831233559)
              ·
                refine ⟨45355129426292330746850339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30236752950861553831233559 45355129426292330746850339)
                ·
                  refine ⟨68032694139438496120275509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45355129426292330746850339 68032694139438496120275509)
                  ·
                    refine ⟨6378065075572359011275829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68032694139438496120275509 6378065075572359011275829)
                    ·
                      refine ⟨597943600834908657307109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6378065075572359011275829 597943600834908657307109)
                      ·
                        rfl

theorem cell23_1164491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_1164491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164491 prefixEnd_1164491 := by exact prefixLift 1164491
  have htrace : WordTrace (prefixWord ++ tailWord_1164491) baseStart_1164491 baseEnd_1164491 := by
    simpa [prefixWord, tailWord_1164491, baseEnd_1164491] using wordTrace_append hprefix tailTrace_1164491
  have hstable : (prefixWord ++ tailWord_1164491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164491).length < 2 ^ (prefixWord ++ tailWord_1164491).sum := by decide
  have hdescent : baseEnd_1164491 < baseStart_1164491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164500 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1164500 : Nat := 118140960795 + 1164500 * 2 ^ 59
def prefixEnd_1164500 : Nat := 4983230072969 + 3 ^ 40 * 1164500 * 2
def baseEnd_1164500 : Nat := 597948222160799122094569

theorem tailTrace_1164500 : CollatzResearch.WordTrace tailWord_1164500 prefixEnd_1164500 597948222160799122094569 := by
  unfold tailWord_1164500
  simp only [CollatzResearch.WordTrace]
  refine ⟨21236402140611427805701477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28315202854148570407601969 21236402140611427805701477)
  ·
    refine ⟨3981825401364642713569027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21236402140611427805701477 3981825401364642713569027)
    ·
      refine ⟨5972738102046964070353541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3981825401364642713569027 5972738102046964070353541)
      ·
        refine ⟨1119888394133805763191289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5972738102046964070353541 1119888394133805763191289)
        ·
          refine ⟨839916295600354322393467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119888394133805763191289 839916295600354322393467)
          ·
            refine ⟨1259874443400531483590201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839916295600354322393467 1259874443400531483590201)
            ·
              refine ⟨944905832550398612692651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259874443400531483590201 944905832550398612692651)
              ·
                refine ⟨1417358748825597919038977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944905832550398612692651 1417358748825597919038977)
                ·
                  refine ⟨1063019061619198439279233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417358748825597919038977 1063019061619198439279233)
                  ·
                    refine ⟨797264296214398829459425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1063019061619198439279233 797264296214398829459425)
                    ·
                      refine ⟨597948222160799122094569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797264296214398829459425 597948222160799122094569)
                      ·
                        rfl

theorem cell23_1164500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1164500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164500 prefixEnd_1164500 := by exact prefixLift 1164500
  have htrace : WordTrace (prefixWord ++ tailWord_1164500) baseStart_1164500 baseEnd_1164500 := by
    simpa [prefixWord, tailWord_1164500, baseEnd_1164500] using wordTrace_append hprefix tailTrace_1164500
  have hstable : (prefixWord ++ tailWord_1164500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164500).length < 2 ^ (prefixWord ++ tailWord_1164500).sum := by decide
  have hdescent : baseEnd_1164500 < baseStart_1164500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164521 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_1164521 : Nat := 118140960795 + 1164521 * 2 ^ 59
def prefixEnd_1164521 : Nat := 4983230072969 + 3 ^ 40 * 1164521 * 2
def baseEnd_1164521 : Nat := 597959005254543539931971

theorem tailTrace_1164521 : CollatzResearch.WordTrace tailWord_1164521 prefixEnd_1164521 597959005254543539931971 := by
  unfold tailWord_1164521
  simp only [CollatzResearch.WordTrace]
  refine ⟨42473570214146776197917417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28315713476097850798611611 42473570214146776197917417)
  ·
    refine ⟨31855177660610082148438063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42473570214146776197917417 31855177660610082148438063)
    ·
      refine ⟨47782766490915123222657095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31855177660610082148438063 47782766490915123222657095)
      ·
        refine ⟨71674149736372684833985643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47782766490915123222657095 71674149736372684833985643)
        ·
          refine ⟨107511224604559027250978465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71674149736372684833985643 107511224604559027250978465)
          ·
            refine ⟨80633418453419270438233849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107511224604559027250978465 80633418453419270438233849)
            ·
              refine ⟨60475063840064452828675387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80633418453419270438233849 60475063840064452828675387)
              ·
                refine ⟨90712595760096679243013081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60475063840064452828675387 90712595760096679243013081)
                ·
                  refine ⟨68034446820072509432259811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90712595760096679243013081 68034446820072509432259811)
                  ·
                    refine ⟨102051670230108764148389717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68034446820072509432259811 102051670230108764148389717)
                    ·
                      refine ⟨597959005254543539931971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 102051670230108764148389717 597959005254543539931971)
                      ·
                        rfl

theorem cell23_1164521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_1164521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164521 prefixEnd_1164521 := by exact prefixLift 1164521
  have htrace : WordTrace (prefixWord ++ tailWord_1164521) baseStart_1164521 baseEnd_1164521 := by
    simpa [prefixWord, tailWord_1164521, baseEnd_1164521] using wordTrace_append hprefix tailTrace_1164521
  have hstable : (prefixWord ++ tailWord_1164521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164521).length < 2 ^ (prefixWord ++ tailWord_1164521).sum := by decide
  have hdescent : baseEnd_1164521 < baseStart_1164521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164542 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1164542 : Nat := 118140960795 + 1164542 * 2 ^ 59
def prefixEnd_1164542 : Nat := 4983230072969 + 3 ^ 40 * 1164542 * 2
def baseEnd_1164542 : Nat := 597969788348287957769375

theorem tailTrace_1164542 : CollatzResearch.WordTrace tailWord_1164542 prefixEnd_1164542 597969788348287957769375 := by
  unfold tailWord_1164542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5309292018383837098053985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28316224098047131189621253 5309292018383837098053985)
  ·
    refine ⟨3981969013787877823540489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5309292018383837098053985 3981969013787877823540489)
    ·
      refine ⟨2986476760340908367655367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981969013787877823540489 2986476760340908367655367)
      ·
        refine ⟨4479715140511362551483051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986476760340908367655367 4479715140511362551483051)
        ·
          refine ⟨6719572710767043827224577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479715140511362551483051 6719572710767043827224577)
          ·
            refine ⟨5039679533075282870418433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6719572710767043827224577 5039679533075282870418433)
            ·
              refine ⟨3779759649806462152813825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5039679533075282870418433 3779759649806462152813825)
              ·
                refine ⟨2834819737354846614610369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779759649806462152813825 2834819737354846614610369)
                ·
                  refine ⟨2126114803016134960957777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834819737354846614610369 2126114803016134960957777)
                  ·
                    refine ⟨1594586102262101220718333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126114803016134960957777 1594586102262101220718333)
                    ·
                      refine ⟨597969788348287957769375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594586102262101220718333 597969788348287957769375)
                      ·
                        rfl

theorem cell23_1164542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1164542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164542 prefixEnd_1164542 := by exact prefixLift 1164542
  have htrace : WordTrace (prefixWord ++ tailWord_1164542) baseStart_1164542 baseEnd_1164542 := by
    simpa [prefixWord, tailWord_1164542, baseEnd_1164542] using wordTrace_append hprefix tailTrace_1164542
  have hstable : (prefixWord ++ tailWord_1164542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164542).length < 2 ^ (prefixWord ++ tailWord_1164542).sum := by decide
  have hdescent : baseEnd_1164542 < baseStart_1164542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164545 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 6]
def baseStart_1164545 : Nat := 118140960795 + 1164545 * 2 ^ 59
def prefixEnd_1164545 : Nat := 4983230072969 + 3 ^ 40 * 1164545 * 2
def baseEnd_1164545 : Nat := 66441258754472382892429

theorem tailTrace_1164545 : CollatzResearch.WordTrace tailWord_1164545 prefixEnd_1164545 66441258754472382892429 := by
  unfold tailWord_1164545
  simp only [CollatzResearch.WordTrace]
  refine ⟨42474445566059828296791089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28316297044039885531194059 42474445566059828296791089)
  ·
    refine ⟨31855834174544871222593317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42474445566059828296791089 31855834174544871222593317)
    ·
      refine ⟨5972968907727163354236247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31855834174544871222593317 5972968907727163354236247)
      ·
        refine ⟨8959453361590745031354371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5972968907727163354236247 8959453361590745031354371)
        ·
          refine ⟨13439180042386117547031557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959453361590745031354371 13439180042386117547031557)
          ·
            refine ⟨2519846257947397040068417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13439180042386117547031557 2519846257947397040068417)
            ·
              refine ⟨1889884693460547780051313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519846257947397040068417 1889884693460547780051313)
              ·
                refine ⟨1417413520095410835038485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889884693460547780051313 1417413520095410835038485)
                ·
                  refine ⟨66441258754472382892429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1417413520095410835038485 66441258754472382892429)
                  ·
                    rfl

theorem cell23_1164545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_1164545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164545 prefixEnd_1164545 := by exact prefixLift 1164545
  have htrace : WordTrace (prefixWord ++ tailWord_1164545) baseStart_1164545 baseEnd_1164545 := by
    simpa [prefixWord, tailWord_1164545, baseEnd_1164545] using wordTrace_append hprefix tailTrace_1164545
  have hstable : (prefixWord ++ tailWord_1164545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164545).length < 2 ^ (prefixWord ++ tailWord_1164545).sum := by decide
  have hdescent : baseEnd_1164545 < baseStart_1164545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164565 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_1164565 : Nat := 118140960795 + 1164565 * 2 ^ 59
def prefixEnd_1164565 : Nat := 4983230072969 + 3 ^ 40 * 1164565 * 2
def baseEnd_1164565 : Nat := 597981598403341367781769

theorem tailTrace_1164565 : CollatzResearch.WordTrace tailWord_1164565 prefixEnd_1164565 597981598403341367781769 := by
  unfold tailWord_1164565
  simp only [CollatzResearch.WordTrace]
  refine ⟨42475175025987371712519149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28316783350658247808346099 42475175025987371712519149)
  ·
    refine ⟨15928190634745264392194681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42475175025987371712519149 15928190634745264392194681)
    ·
      refine ⟨11946142976058948294146011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15928190634745264392194681 11946142976058948294146011)
      ·
        refine ⟨17919214464088422441219017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11946142976058948294146011 17919214464088422441219017)
        ·
          refine ⟨13439410848066316830914263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17919214464088422441219017 13439410848066316830914263)
          ·
            refine ⟨20159116272099475246371395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13439410848066316830914263 20159116272099475246371395)
            ·
              refine ⟨30238674408149212869557093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20159116272099475246371395 30238674408149212869557093)
              ·
                refine ⟨5669751451527977413041955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30238674408149212869557093 5669751451527977413041955)
                ·
                  refine ⟨8504627177291966119562933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669751451527977413041955 8504627177291966119562933)
                  ·
                    refine ⟨797308797871121823709025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8504627177291966119562933 797308797871121823709025)
                    ·
                      refine ⟨597981598403341367781769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797308797871121823709025 597981598403341367781769)
                      ·
                        rfl

theorem cell23_1164565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_1164565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164565 prefixEnd_1164565 := by exact prefixLift 1164565
  have htrace : WordTrace (prefixWord ++ tailWord_1164565) baseStart_1164565 baseEnd_1164565 := by
    simpa [prefixWord, tailWord_1164565, baseEnd_1164565] using wordTrace_append hprefix tailTrace_1164565
  have hstable : (prefixWord ++ tailWord_1164565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164565).length < 2 ^ (prefixWord ++ tailWord_1164565).sum := by decide
  have hdescent : baseEnd_1164565 < baseStart_1164565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164608 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1164608 : Nat := 118140960795 + 1164608 * 2 ^ 59
def prefixEnd_1164608 : Nat := 4983230072969 + 3 ^ 40 * 1164608 * 2
def baseEnd_1164608 : Nat := 598003678071484699544071

theorem tailTrace_1164608 : CollatzResearch.WordTrace tailWord_1164608 prefixEnd_1164608 598003678071484699544071 := by
  unfold tailWord_1164608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21238371682415795028167239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28317828909887726704222985 21238371682415795028167239)
  ·
    refine ⟨31857557523623692542250859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21238371682415795028167239 31857557523623692542250859)
    ·
      refine ⟨47786336285435538813376289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31857557523623692542250859 47786336285435538813376289)
      ·
        refine ⟨35839752214076654110032217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47786336285435538813376289 35839752214076654110032217)
        ·
          refine ⟨26879814160557490582524163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35839752214076654110032217 26879814160557490582524163)
          ·
            refine ⟨40319721240836235873786245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26879814160557490582524163 40319721240836235873786245)
            ·
              refine ⟨7559947732656794226334921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40319721240836235873786245 7559947732656794226334921)
              ·
                refine ⟨5669960799492595669751191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7559947732656794226334921 5669960799492595669751191)
                ·
                  refine ⟨8504941199238893504626787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669960799492595669751191 8504941199238893504626787)
                  ·
                    refine ⟨12757411798858340256940181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8504941199238893504626787 12757411798858340256940181)
                    ·
                      refine ⟨598003678071484699544071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12757411798858340256940181 598003678071484699544071)
                      ·
                        rfl

theorem cell23_1164608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1164608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164608 prefixEnd_1164608 := by exact prefixLift 1164608
  have htrace : WordTrace (prefixWord ++ tailWord_1164608) baseStart_1164608 baseEnd_1164608 := by
    simpa [prefixWord, tailWord_1164608, baseEnd_1164608] using wordTrace_append hprefix tailTrace_1164608
  have hstable : (prefixWord ++ tailWord_1164608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164608).length < 2 ^ (prefixWord ++ tailWord_1164608).sum := by decide
  have hdescent : baseEnd_1164608 < baseStart_1164608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164615 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1164615 : Nat := 118140960795 + 1164615 * 2 ^ 59
def prefixEnd_1164615 : Nat := 4983230072969 + 3 ^ 40 * 1164615 * 2
def baseEnd_1164615 : Nat := 598007272436066172156539

theorem tailTrace_1164615 : CollatzResearch.WordTrace tailWord_1164615 prefixEnd_1164615 598007272436066172156539 := by
  unfold tailWord_1164615
  simp only [CollatzResearch.WordTrace]
  refine ⟨42476998675806230251839299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28317999117204153501226199 42476998675806230251839299)
  ·
    refine ⟨63715498013709345377758949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42476998675806230251839299 63715498013709345377758949)
    ·
      refine ⟨11946655877570502258329803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63715498013709345377758949 11946655877570502258329803)
      ·
        refine ⟨17919983816355753387494705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11946655877570502258329803 17919983816355753387494705)
        ·
          refine ⟨13439987862266815040621029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17919983816355753387494705 13439987862266815040621029)
          ·
            refine ⟨2519997724175027820116443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13439987862266815040621029 2519997724175027820116443)
            ·
              refine ⟨3779996586262541730174665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519997724175027820116443 3779996586262541730174665)
              ·
                refine ⟨2834997439696906297630999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779996586262541730174665 2834997439696906297630999)
                ·
                  refine ⟨4252496159545359446446499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834997439696906297630999 4252496159545359446446499)
                  ·
                    refine ⟨6378744239318039169669749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252496159545359446446499 6378744239318039169669749)
                    ·
                      refine ⟨598007272436066172156539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6378744239318039169669749 598007272436066172156539)
                      ·
                        rfl

theorem cell23_1164615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1164615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164615 prefixEnd_1164615 := by exact prefixLift 1164615
  have htrace : WordTrace (prefixWord ++ tailWord_1164615) baseStart_1164615 baseEnd_1164615 := by
    simpa [prefixWord, tailWord_1164615, baseEnd_1164615] using wordTrace_append hprefix tailTrace_1164615
  have hstable : (prefixWord ++ tailWord_1164615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164615).length < 2 ^ (prefixWord ++ tailWord_1164615).sum := by decide
  have hdescent : baseEnd_1164615 < baseStart_1164615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164629 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_1164629 : Nat := 118140960795 + 1164629 * 2 ^ 59
def prefixEnd_1164629 : Nat := 4983230072969 + 3 ^ 40 * 1164629 * 2
def baseEnd_1164629 : Nat := 598014461165229117381475

theorem tailTrace_1164629 : CollatzResearch.WordTrace tailWord_1164629 prefixEnd_1164629 598014461165229117381475 := by
  unfold tailWord_1164629
  simp only [CollatzResearch.WordTrace]
  refine ⟨42477509297755510642848941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28318339531837007095232627 42477509297755510642848941)
  ·
    refine ⟨15929065986658316491068353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42477509297755510642848941 15929065986658316491068353)
    ·
      refine ⟨11946799489993737368301265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15929065986658316491068353 11946799489993737368301265)
      ·
        refine ⟨8960099617495303026225949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11946799489993737368301265 8960099617495303026225949)
        ·
          refine ⟨3360037356560738634834731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8960099617495303026225949 3360037356560738634834731)
          ·
            refine ⟨5040056034841107952252097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360037356560738634834731 5040056034841107952252097)
            ·
              refine ⟨3780042026130830964189073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040056034841107952252097 3780042026130830964189073)
              ·
                refine ⟨2835031519598123223141805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780042026130830964189073 2835031519598123223141805)
                ·
                  refine ⟨1063136819849296208678177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2835031519598123223141805 1063136819849296208678177)
                  ·
                    refine ⟨797352614886972156508633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1063136819849296208678177 797352614886972156508633)
                    ·
                      refine ⟨598014461165229117381475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797352614886972156508633 598014461165229117381475)
                      ·
                        rfl

theorem cell23_1164629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_1164629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164629 prefixEnd_1164629 := by exact prefixLift 1164629
  have htrace : WordTrace (prefixWord ++ tailWord_1164629) baseStart_1164629 baseEnd_1164629 := by
    simpa [prefixWord, tailWord_1164629, baseEnd_1164629] using wordTrace_append hprefix tailTrace_1164629
  have hstable : (prefixWord ++ tailWord_1164629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164629).length < 2 ^ (prefixWord ++ tailWord_1164629).sum := by decide
  have hdescent : baseEnd_1164629 < baseStart_1164629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164632 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1164632 : Nat := 118140960795 + 1164632 * 2 ^ 59
def prefixEnd_1164632 : Nat := 4983230072969 + 3 ^ 40 * 1164632 * 2
def baseEnd_1164632 : Nat := 598016001607192605643961

theorem tailTrace_1164632 : CollatzResearch.WordTrace tailWord_1164632 prefixEnd_1164632 598016001607192605643961 := by
  unfold tailWord_1164632
  simp only [CollatzResearch.WordTrace]
  refine ⟨21238809358372321077604075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28318412477829761436805433 21238809358372321077604075)
  ·
    refine ⟨31858214037558481616406113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21238809358372321077604075 31858214037558481616406113)
    ·
      refine ⟨23893660528168861212304585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31858214037558481616406113 23893660528168861212304585)
      ·
        refine ⟨17920245396126645909228439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23893660528168861212304585 17920245396126645909228439)
        ·
          refine ⟨26880368094189968863842659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17920245396126645909228439 26880368094189968863842659)
          ·
            refine ⟨40320552141284953295763989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26880368094189968863842659 40320552141284953295763989)
            ·
              refine ⟨1890025881622732185738937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40320552141284953295763989 1890025881622732185738937)
              ·
                refine ⟨1417519411217049139304203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890025881622732185738937 1417519411217049139304203)
                ·
                  refine ⟨2126279116825573708956305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417519411217049139304203 2126279116825573708956305)
                  ·
                    refine ⟨1594709337619180281717229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126279116825573708956305 1594709337619180281717229)
                    ·
                      refine ⟨598016001607192605643961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594709337619180281717229 598016001607192605643961)
                      ·
                        rfl

theorem cell23_1164632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1164632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164632 prefixEnd_1164632 := by exact prefixLift 1164632
  have htrace : WordTrace (prefixWord ++ tailWord_1164632) baseStart_1164632 baseEnd_1164632 := by
    simpa [prefixWord, tailWord_1164632, baseEnd_1164632] using wordTrace_append hprefix tailTrace_1164632
  have hstable : (prefixWord ++ tailWord_1164632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164632).length < 2 ^ (prefixWord ++ tailWord_1164632).sum := by decide
  have hdescent : baseEnd_1164632 < baseStart_1164632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164645 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1164645 : Nat := 118140960795 + 1164645 * 2 ^ 59
def prefixEnd_1164645 : Nat := 4983230072969 + 3 ^ 40 * 1164645 * 2
def baseEnd_1164645 : Nat := 598022676855701054781401

theorem tailTrace_1164645 : CollatzResearch.WordTrace tailWord_1164645 prefixEnd_1164645 598022676855701054781401 := by
  unfold tailWord_1164645
  simp only [CollatzResearch.WordTrace]
  refine ⟨42478092865697545375431389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28318728577131696916954259 42478092865697545375431389)
  ·
    refine ⟨15929284824636579515786771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42478092865697545375431389 15929284824636579515786771)
    ·
      refine ⟨23893927236954869273680157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15929284824636579515786771 23893927236954869273680157)
      ·
        refine ⟨8960222713858075977630059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23893927236954869273680157 8960222713858075977630059)
        ·
          refine ⟨13440334070787113966445089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8960222713858075977630059 13440334070787113966445089)
          ·
            refine ⟨10080250553090335474833817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13440334070787113966445089 10080250553090335474833817)
            ·
              refine ⟨7560187914817751606125363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10080250553090335474833817 7560187914817751606125363)
              ·
                refine ⟨11340281872226627409188045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7560187914817751606125363 11340281872226627409188045)
                ·
                  refine ⟨4252605702084985278445517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11340281872226627409188045 4252605702084985278445517)
                  ·
                    refine ⟨1594727138281869479417069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4252605702084985278445517 1594727138281869479417069)
                    ·
                      refine ⟨598022676855701054781401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594727138281869479417069 598022676855701054781401)
                      ·
                        rfl

theorem cell23_1164645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1164645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164645 prefixEnd_1164645 := by exact prefixLift 1164645
  have htrace : WordTrace (prefixWord ++ tailWord_1164645) baseStart_1164645 baseEnd_1164645 := by
    simpa [prefixWord, tailWord_1164645, baseEnd_1164645] using wordTrace_append hprefix tailTrace_1164645
  have hstable : (prefixWord ++ tailWord_1164645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164645).length < 2 ^ (prefixWord ++ tailWord_1164645).sum := by decide
  have hdescent : baseEnd_1164645 < baseStart_1164645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164673 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1164673 : Nat := 118140960795 + 1164673 * 2 ^ 59
def prefixEnd_1164673 : Nat := 4983230072969 + 3 ^ 40 * 1164673 * 2
def baseEnd_1164673 : Nat := 199345684771342315077091

theorem tailTrace_1164673 : CollatzResearch.WordTrace tailWord_1164673 prefixEnd_1164673 199345684771342315077091 := by
  unfold tailWord_1164673
  simp only [CollatzResearch.WordTrace]
  refine ⟨42479114109596106157450673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28319409406397404104967115 42479114109596106157450673)
  ·
    refine ⟨31859335582197079618088005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42479114109596106157450673 31859335582197079618088005)
    ·
      refine ⟨5973625421661952428391501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31859335582197079618088005 5973625421661952428391501)
      ·
        refine ⟨2240109533123232160646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5973625421661952428391501 2240109533123232160646813)
        ·
          refine ⟨840041074921212060242555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2240109533123232160646813 840041074921212060242555)
          ·
            refine ⟨1260061612381818090363833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840041074921212060242555 1260061612381818090363833)
            ·
              refine ⟨945046209286363567772875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260061612381818090363833 945046209286363567772875)
              ·
                refine ⟨1417569313929545351659313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945046209286363567772875 1417569313929545351659313)
                ·
                  refine ⟨1063176985447159013744485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417569313929545351659313 1063176985447159013744485)
                  ·
                    refine ⟨199345684771342315077091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1063176985447159013744485 199345684771342315077091)
                    ·
                      rfl

theorem cell23_1164673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1164673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164673 prefixEnd_1164673 := by exact prefixLift 1164673
  have htrace : WordTrace (prefixWord ++ tailWord_1164673) baseStart_1164673 baseEnd_1164673 := by
    simpa [prefixWord, tailWord_1164673, baseEnd_1164673] using wordTrace_append hprefix tailTrace_1164673
  have hstable : (prefixWord ++ tailWord_1164673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164673).length < 2 ^ (prefixWord ++ tailWord_1164673).sum := by decide
  have hdescent : baseEnd_1164673 < baseStart_1164673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164679 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1164679 : Nat := 118140960795 + 1164679 * 2 ^ 59
def prefixEnd_1164679 : Nat := 4983230072969 + 3 ^ 40 * 1164679 * 2
def baseEnd_1164679 : Nat := 598040135197953921756245

theorem tailTrace_1164679 : CollatzResearch.WordTrace tailWord_1164679 prefixEnd_1164679 598040135197953921756245 := by
  unfold tailWord_1164679
  simp only [CollatzResearch.WordTrace]
  refine ⟨42479332947574369182169091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28319555298382912788112727 42479332947574369182169091)
  ·
    refine ⟨63718999421361553773253637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42479332947574369182169091 63718999421361553773253637)
    ·
      refine ⟨11947312391505291332485057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63718999421361553773253637 11947312391505291332485057)
      ·
        refine ⟨8960484293628968499363793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11947312391505291332485057 8960484293628968499363793)
        ·
          refine ⟨6720363220221726374522845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8960484293628968499363793 6720363220221726374522845)
          ·
            refine ⟨2520136207583147390446067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6720363220221726374522845 2520136207583147390446067)
            ·
              refine ⟨3780204311374721085669101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520136207583147390446067 3780204311374721085669101)
              ·
                refine ⟨1417576616765520407125913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3780204311374721085669101 1417576616765520407125913)
                ·
                  refine ⟨1063182462574140305344435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417576616765520407125913 1063182462574140305344435)
                  ·
                    refine ⟨1594773693861210458016653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1063182462574140305344435 1594773693861210458016653)
                    ·
                      refine ⟨598040135197953921756245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594773693861210458016653 598040135197953921756245)
                      ·
                        rfl

theorem cell23_1164679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1164679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164679 prefixEnd_1164679 := by exact prefixLift 1164679
  have htrace : WordTrace (prefixWord ++ tailWord_1164679) baseStart_1164679 baseEnd_1164679 := by
    simpa [prefixWord, tailWord_1164679, baseEnd_1164679] using wordTrace_append hprefix tailTrace_1164679
  have hstable : (prefixWord ++ tailWord_1164679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164679).length < 2 ^ (prefixWord ++ tailWord_1164679).sum := by decide
  have hdescent : baseEnd_1164679 < baseStart_1164679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164805 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_1164805 : Nat := 118140960795 + 1164805 * 2 ^ 59
def prefixEnd_1164805 : Nat := 4983230072969 + 3 ^ 40 * 1164805 * 2
def baseEnd_1164805 : Nat := 598104833760420428780665

theorem tailTrace_1164805 : CollatzResearch.WordTrace tailWord_1164805 prefixEnd_1164805 598104833760420428780665 := by
  unfold tailWord_1164805
  simp only [CollatzResearch.WordTrace]
  refine ⟨42483928545117892701255869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28322619030078595134170579 42483928545117892701255869)
  ·
    refine ⟨15931473204419209762970951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42483928545117892701255869 15931473204419209762970951)
    ·
      refine ⟨23897209806628814644456427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15931473204419209762970951 23897209806628814644456427)
      ·
        refine ⟨35845814709943221966684641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23897209806628814644456427 35845814709943221966684641)
        ·
          refine ⟨26884361032457416475013481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35845814709943221966684641 26884361032457416475013481)
          ·
            refine ⟨20163270774343062356260111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26884361032457416475013481 20163270774343062356260111)
            ·
              refine ⟨30244906161514593534390167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20163270774343062356260111 30244906161514593534390167)
              ·
                refine ⟨45367359242271890301585251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30244906161514593534390167 45367359242271890301585251)
                ·
                  refine ⟨68051038863407835452377877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45367359242271890301585251 68051038863407835452377877)
                  ·
                    refine ⟨3189892446722242286830213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68051038863407835452377877 3189892446722242286830213)
                    ·
                      refine ⟨598104833760420428780665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3189892446722242286830213 598104833760420428780665)
                      ·
                        rfl

theorem cell23_1164805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_1164805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164805 prefixEnd_1164805 := by exact prefixLift 1164805
  have htrace : WordTrace (prefixWord ++ tailWord_1164805) baseStart_1164805 baseEnd_1164805 := by
    simpa [prefixWord, tailWord_1164805, baseEnd_1164805] using wordTrace_append hprefix tailTrace_1164805
  have hstable : (prefixWord ++ tailWord_1164805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164805).length < 2 ^ (prefixWord ++ tailWord_1164805).sum := by decide
  have hdescent : baseEnd_1164805 < baseStart_1164805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164829 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1164829 : Nat := 118140960795 + 1164829 * 2 ^ 59
def prefixEnd_1164829 : Nat := 4983230072969 + 3 ^ 40 * 1164829 * 2
def baseEnd_1164829 : Nat := 598117157296128334880555

theorem tailTrace_1164829 : CollatzResearch.WordTrace tailWord_1164829 prefixEnd_1164829 598117157296128334880555 := by
  unfold tailWord_1164829
  simp only [CollatzResearch.WordTrace]
  refine ⟨42484803897030944800129541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28323202598020629866753027 42484803897030944800129541)
  ·
    refine ⟨7965900730693302150024289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42484803897030944800129541 7965900730693302150024289)
    ·
      refine ⟨5974425548019976612518217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7965900730693302150024289 5974425548019976612518217)
      ·
        refine ⟨4480819161014982459388663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5974425548019976612518217 4480819161014982459388663)
        ·
          refine ⟨6721228741522473689082995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480819161014982459388663 6721228741522473689082995)
          ·
            refine ⟨10081843112283710533624493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721228741522473689082995 10081843112283710533624493)
            ·
              refine ⟨3780691167106391450109185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10081843112283710533624493 3780691167106391450109185)
              ·
                refine ⟨2835518375329793587581889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780691167106391450109185 2835518375329793587581889)
                ·
                  refine ⟨2126638781497345190686417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835518375329793587581889 2126638781497345190686417)
                  ·
                    refine ⟨1594979086123008893014813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126638781497345190686417 1594979086123008893014813)
                    ·
                      refine ⟨598117157296128334880555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1594979086123008893014813 598117157296128334880555)
                      ·
                        rfl

theorem cell23_1164829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1164829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164829 prefixEnd_1164829 := by exact prefixLift 1164829
  have htrace : WordTrace (prefixWord ++ tailWord_1164829) baseStart_1164829 baseEnd_1164829 := by
    simpa [prefixWord, tailWord_1164829, baseEnd_1164829] using wordTrace_append hprefix tailTrace_1164829
  have hstable : (prefixWord ++ tailWord_1164829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164829).length < 2 ^ (prefixWord ++ tailWord_1164829).sum := by decide
  have hdescent : baseEnd_1164829 < baseStart_1164829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164832 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 8]
def baseStart_1164832 : Nat := 118140960795 + 1164832 * 2 ^ 59
def prefixEnd_1164832 : Nat := 4983230072969 + 3 ^ 40 * 1164832 * 2
def baseEnd_1164832 : Nat := 66457633082010202571449

theorem tailTrace_1164832 : CollatzResearch.WordTrace tailWord_1164832 prefixEnd_1164832 66457633082010202571449 := by
  unfold tailWord_1164832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21242456658010038156244375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28323275544013384208325833 21242456658010038156244375)
  ·
    refine ⟨31863684987015057234366563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21242456658010038156244375 31863684987015057234366563)
    ·
      refine ⟨47795527480522585851549845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31863684987015057234366563 47795527480522585851549845)
      ·
        refine ⟨2240415350649496211791399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47795527480522585851549845 2240415350649496211791399)
        ·
          refine ⟨3360623025974244317687099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240415350649496211791399 3360623025974244317687099)
          ·
            refine ⟨5040934538961366476530649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360623025974244317687099 5040934538961366476530649)
            ·
              refine ⟨3780700904221024857397987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040934538961366476530649 3780700904221024857397987)
              ·
                refine ⟨5671051356331537286096981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780700904221024857397987 5671051356331537286096981)
                ·
                  refine ⟨66457633082010202571449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5671051356331537286096981 66457633082010202571449)
                  ·
                    rfl

theorem cell23_1164832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_1164832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164832 prefixEnd_1164832 := by exact prefixLift 1164832
  have htrace : WordTrace (prefixWord ++ tailWord_1164832) baseStart_1164832 baseEnd_1164832 := by
    simpa [prefixWord, tailWord_1164832, baseEnd_1164832] using wordTrace_append hprefix tailTrace_1164832
  have hstable : (prefixWord ++ tailWord_1164832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164832).length < 2 ^ (prefixWord ++ tailWord_1164832).sum := by decide
  have hdescent : baseEnd_1164832 < baseStart_1164832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164919 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_1164919 : Nat := 118140960795 + 1164919 * 2 ^ 59
def prefixEnd_1164919 : Nat := 4983230072969 + 3 ^ 40 * 1164919 * 2
def baseEnd_1164919 : Nat := 598163370555032982755141

theorem tailTrace_1164919 : CollatzResearch.WordTrace tailWord_1164919 prefixEnd_1164919 598163370555032982755141 := by
  unfold tailWord_1164919
  simp only [CollatzResearch.WordTrace]
  refine ⟨42488086466704890170905811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28325390977803260113937207 42488086466704890170905811)
  ·
    refine ⟨63732129700057335256358717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42488086466704890170905811 63732129700057335256358717)
    ·
      refine ⟨23899548637521500721134519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63732129700057335256358717 23899548637521500721134519)
      ·
        refine ⟨35849322956282251081701779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23899548637521500721134519 35849322956282251081701779)
        ·
          refine ⟨53773984434423376622552669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35849322956282251081701779 53773984434423376622552669)
          ·
            refine ⟨20165244162908766233457251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53773984434423376622552669 20165244162908766233457251)
            ·
              refine ⟨30247866244363149350185877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20165244162908766233457251 30247866244363149350185877)
              ·
                refine ⟨1417868730204522625789963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30247866244363149350185877 1417868730204522625789963)
                ·
                  refine ⟨2126803095306783938684945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417868730204522625789963 2126803095306783938684945)
                  ·
                    refine ⟨1595102321480087954013709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126803095306783938684945 1595102321480087954013709)
                    ·
                      refine ⟨598163370555032982755141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595102321480087954013709 598163370555032982755141)
                      ·
                        rfl

theorem cell23_1164919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_1164919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164919 prefixEnd_1164919 := by exact prefixLift 1164919
  have htrace : WordTrace (prefixWord ++ tailWord_1164919) baseStart_1164919 baseEnd_1164919 := by
    simpa [prefixWord, tailWord_1164919, baseEnd_1164919] using wordTrace_append hprefix tailTrace_1164919
  have hstable : (prefixWord ++ tailWord_1164919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164919).length < 2 ^ (prefixWord ++ tailWord_1164919).sum := by decide
  have hdescent : baseEnd_1164919 < baseStart_1164919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164929 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1164929 : Nat := 118140960795 + 1164929 * 2 ^ 59
def prefixEnd_1164929 : Nat := 4983230072969 + 3 ^ 40 * 1164929 * 2
def baseEnd_1164929 : Nat := 598168505361577943630095

theorem tailTrace_1164929 : CollatzResearch.WordTrace tailWord_1164929 prefixEnd_1164929 598168505361577943630095 := by
  unfold tailWord_1164929
  simp only [CollatzResearch.WordTrace]
  refine ⟨42488451196668661878769841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28325634131112441252513227 42488451196668661878769841)
  ·
    refine ⟨31866338397501496409077381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42488451196668661878769841 31866338397501496409077381)
    ·
      refine ⟨5974938449531530576702009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31866338397501496409077381 5974938449531530576702009)
      ·
        refine ⟨4481203837148647932526507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5974938449531530576702009 4481203837148647932526507)
        ·
          refine ⟨6721805755722971898789761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481203837148647932526507 6721805755722971898789761)
          ·
            refine ⟨5041354316792228924092321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721805755722971898789761 5041354316792228924092321)
            ·
              refine ⟨3781015737594171693069241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5041354316792228924092321 3781015737594171693069241)
              ·
                refine ⟨2835761803195628769801931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3781015737594171693069241 2835761803195628769801931)
                ·
                  refine ⟨4253642704793443154702897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835761803195628769801931 4253642704793443154702897)
                  ·
                    refine ⟨3190232028595082366027173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253642704793443154702897 3190232028595082366027173)
                    ·
                      refine ⟨598168505361577943630095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3190232028595082366027173 598168505361577943630095)
                      ·
                        rfl

theorem cell23_1164929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1164929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164929 prefixEnd_1164929 := by exact prefixLift 1164929
  have htrace : WordTrace (prefixWord ++ tailWord_1164929) baseStart_1164929 baseEnd_1164929 := by
    simpa [prefixWord, tailWord_1164929, baseEnd_1164929] using wordTrace_append hprefix tailTrace_1164929
  have hstable : (prefixWord ++ tailWord_1164929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164929).length < 2 ^ (prefixWord ++ tailWord_1164929).sum := by decide
  have hdescent : baseEnd_1164929 < baseStart_1164929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164976 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2]
def baseStart_1164976 : Nat := 118140960795 + 1164976 * 2 ^ 59
def prefixEnd_1164976 : Nat := 4983230072969 + 3 ^ 40 * 1164976 * 2
def baseEnd_1164976 : Nat := 598192638952339259742379

theorem tailTrace_1164976 : CollatzResearch.WordTrace tailWord_1164976 prefixEnd_1164976 598192638952339259742379 := by
  unfold tailWord_1164976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245082713749194452865391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28326776951665592603820521 21245082713749194452865391)
  ·
    refine ⟨31867624070623791679298087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21245082713749194452865391 31867624070623791679298087)
    ·
      refine ⟨47801436105935687518947131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31867624070623791679298087 47801436105935687518947131)
      ·
        refine ⟨71702154158903531278420697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47801436105935687518947131 71702154158903531278420697)
        ·
          refine ⟨53776615619177648458815523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71702154158903531278420697 53776615619177648458815523)
          ·
            refine ⟨80664923428766472688223285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53776615619177648458815523 80664923428766472688223285)
            ·
              refine ⟨7562336571446856814520933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80664923428766472688223285 7562336571446856814520933)
              ·
                refine ⟨1417938107146285652722675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7562336571446856814520933 1417938107146285652722675)
                ·
                  refine ⟨2126907160719428479084013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417938107146285652722675 2126907160719428479084013)
                  ·
                    refine ⟨797590185269785679656505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126907160719428479084013 797590185269785679656505)
                    ·
                      refine ⟨598192638952339259742379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797590185269785679656505 598192638952339259742379)
                      ·
                        rfl

theorem cell23_1164976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2].length) (baseStart_1164976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1164976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1164976 prefixEnd_1164976 := by exact prefixLift 1164976
  have htrace : WordTrace (prefixWord ++ tailWord_1164976) baseStart_1164976 baseEnd_1164976 := by
    simpa [prefixWord, tailWord_1164976, baseEnd_1164976] using wordTrace_append hprefix tailTrace_1164976
  have hstable : (prefixWord ++ tailWord_1164976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164976).length < 2 ^ (prefixWord ++ tailWord_1164976).sum := by decide
  have hdescent : baseEnd_1164976 < baseStart_1164976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165023 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 2, 2, 2]
def baseStart_1165023 : Nat := 118140960795 + 1165023 * 2 ^ 59
def prefixEnd_1165023 : Nat := 4983230072969 + 3 ^ 40 * 1165023 * 2
def baseEnd_1165023 : Nat := 598216772543100575854663

theorem tailTrace_1165023 : CollatzResearch.WordTrace tailWord_1165023 prefixEnd_1165023 598216772543100575854663 := by
  unfold tailWord_1165023
  simp only [CollatzResearch.WordTrace]
  refine ⟨42491879658328115932691723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28327919772218743955127815 42491879658328115932691723)
  ·
    refine ⟨63737819487492173899037585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42491879658328115932691723 63737819487492173899037585)
    ·
      refine ⟨47803364615619130424278189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63737819487492173899037585 47803364615619130424278189)
      ·
        refine ⟨17926261730857173909104321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47803364615619130424278189 17926261730857173909104321)
        ·
          refine ⟨13444696298142880431828241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17926261730857173909104321 13444696298142880431828241)
          ·
            refine ⟨10083522223607160323871181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13444696298142880431828241 10083522223607160323871181)
            ·
              refine ⟨3781320833852685121451693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10083522223607160323871181 3781320833852685121451693)
              ·
                refine ⟨1417995312694756920544385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3781320833852685121451693 1417995312694756920544385)
                ·
                  refine ⟨1063496484521067690408289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417995312694756920544385 1063496484521067690408289)
                  ·
                    refine ⟨797622363390800767806217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1063496484521067690408289 797622363390800767806217)
                    ·
                      refine ⟨598216772543100575854663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797622363390800767806217 598216772543100575854663)
                      ·
                        rfl

theorem cell23_1165023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_1165023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165023 prefixEnd_1165023 := by exact prefixLift 1165023
  have htrace : WordTrace (prefixWord ++ tailWord_1165023) baseStart_1165023 baseEnd_1165023 := by
    simpa [prefixWord, tailWord_1165023, baseEnd_1165023] using wordTrace_append hprefix tailTrace_1165023
  have hstable : (prefixWord ++ tailWord_1165023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165023).length < 2 ^ (prefixWord ++ tailWord_1165023).sum := by decide
  have hdescent : baseEnd_1165023 < baseStart_1165023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165027 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1165027 : Nat := 118140960795 + 1165027 * 2 ^ 59
def prefixEnd_1165027 : Nat := 4983230072969 + 3 ^ 40 * 1165027 * 2
def baseEnd_1165027 : Nat := 598218826465718560204645

theorem tailTrace_1165027 : CollatzResearch.WordTrace tailWord_1165027 prefixEnd_1165027 598218826465718560204645 := by
  unfold tailWord_1165027
  simp only [CollatzResearch.WordTrace]
  refine ⟨42492025550313624615837335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28328017033542416410558223 42492025550313624615837335)
  ·
    refine ⟨63738038325470436923756003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42492025550313624615837335 63738038325470436923756003)
    ·
      refine ⟨95607057488205655385634005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63738038325470436923756003 95607057488205655385634005)
      ·
        refine ⟨2240790409879820048100797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 95607057488205655385634005 2240790409879820048100797)
        ·
          refine ⟨840296403704932518037799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2240790409879820048100797 840296403704932518037799)
          ·
            refine ⟨1260444605557398777056699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840296403704932518037799 1260444605557398777056699)
            ·
              refine ⟨1890666908336098165585049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260444605557398777056699 1890666908336098165585049)
              ·
                refine ⟨1418000181252073624188787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890666908336098165585049 1418000181252073624188787)
                ·
                  refine ⟨2127000271878110436283181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418000181252073624188787 2127000271878110436283181)
                  ·
                    refine ⟨797625101954291413606193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127000271878110436283181 797625101954291413606193)
                    ·
                      refine ⟨598218826465718560204645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797625101954291413606193 598218826465718560204645)
                      ·
                        rfl

theorem cell23_1165027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1165027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165027 prefixEnd_1165027 := by exact prefixLift 1165027
  have htrace : WordTrace (prefixWord ++ tailWord_1165027) baseStart_1165027 baseEnd_1165027 := by
    simpa [prefixWord, tailWord_1165027, baseEnd_1165027] using wordTrace_append hprefix tailTrace_1165027
  have hstable : (prefixWord ++ tailWord_1165027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165027).length < 2 ^ (prefixWord ++ tailWord_1165027).sum := by decide
  have hdescent : baseEnd_1165027 < baseStart_1165027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165044 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1165044 : Nat := 118140960795 + 1165044 * 2 ^ 59
def prefixEnd_1165044 : Nat := 4983230072969 + 3 ^ 40 * 1165044 * 2
def baseEnd_1165044 : Nat := 598227555636844993692067

theorem tailTrace_1165044 : CollatzResearch.WordTrace tailWord_1165044 prefixEnd_1165044 598227555636844993692067 := by
  unfold tailWord_1165044
  simp only [CollatzResearch.WordTrace]
  refine ⟨21246322795626018259603093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28328430394168024346137457 21246322795626018259603093)
  ·
    refine ⟨995921381044969605918895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21246322795626018259603093 995921381044969605918895)
    ·
      refine ⟨1493882071567454408878343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995921381044969605918895 1493882071567454408878343)
      ·
        refine ⟨2240823107351181613317515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493882071567454408878343 2240823107351181613317515)
        ·
          refine ⟨3361234661026772419976273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240823107351181613317515 3361234661026772419976273)
          ·
            refine ⟨2520925995770079314982205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3361234661026772419976273 2520925995770079314982205)
            ·
              refine ⟨945347248413779743118327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520925995770079314982205 945347248413779743118327)
              ·
                refine ⟨1418020872620669614677491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945347248413779743118327 1418020872620669614677491)
                ·
                  refine ⟨2127031308931004422016237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418020872620669614677491 2127031308931004422016237)
                  ·
                    refine ⟨797636740849126658256089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127031308931004422016237 797636740849126658256089)
                    ·
                      refine ⟨598227555636844993692067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797636740849126658256089 598227555636844993692067)
                      ·
                        rfl

theorem cell23_1165044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1165044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165044 prefixEnd_1165044 := by exact prefixLift 1165044
  have htrace : WordTrace (prefixWord ++ tailWord_1165044) baseStart_1165044 baseEnd_1165044 := by
    simpa [prefixWord, tailWord_1165044, baseEnd_1165044] using wordTrace_append hprefix tailTrace_1165044
  have hstable : (prefixWord ++ tailWord_1165044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165044).length < 2 ^ (prefixWord ++ tailWord_1165044).sum := by decide
  have hdescent : baseEnd_1165044 < baseStart_1165044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165059 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 2, 5]
def baseStart_1165059 : Nat := 118140960795 + 1165059 * 2 ^ 59
def prefixEnd_1165059 : Nat := 4983230072969 + 3 ^ 40 * 1165059 * 2
def baseEnd_1165059 : Nat := 199411752615554145001499

theorem tailTrace_1165059 : CollatzResearch.WordTrace tailWord_1165059 prefixEnd_1165059 199411752615554145001499 := by
  unfold tailWord_1165059
  simp only [CollatzResearch.WordTrace]
  refine ⟨42493192686197694081002231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28328795124131796054001487 42493192686197694081002231)
  ·
    refine ⟨63739789029296541121503347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42493192686197694081002231 63739789029296541121503347)
    ·
      refine ⟨95609683543944811682255021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63739789029296541121503347 95609683543944811682255021)
      ·
        refine ⟨35853631328979304380845633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95609683543944811682255021 35853631328979304380845633)
        ·
          refine ⟨26890223496734478285634225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35853631328979304380845633 26890223496734478285634225)
          ·
            refine ⟨20167667622550858714225669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26890223496734478285634225 20167667622550858714225669)
            ·
              refine ⟨3781437679228286008917313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20167667622550858714225669 3781437679228286008917313)
              ·
                refine ⟨2836078259421214506687985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3781437679228286008917313 2836078259421214506687985)
                ·
                  refine ⟨2127058694565910880015989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836078259421214506687985 2127058694565910880015989)
                  ·
                    refine ⟨199411752615554145001499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2127058694565910880015989 199411752615554145001499)
                    ·
                      rfl

theorem cell23_1165059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 5].length) (baseStart_1165059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165059 prefixEnd_1165059 := by exact prefixLift 1165059
  have htrace : WordTrace (prefixWord ++ tailWord_1165059) baseStart_1165059 baseEnd_1165059 := by
    simpa [prefixWord, tailWord_1165059, baseEnd_1165059] using wordTrace_append hprefix tailTrace_1165059
  have hstable : (prefixWord ++ tailWord_1165059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165059).length < 2 ^ (prefixWord ++ tailWord_1165059).sum := by decide
  have hdescent : baseEnd_1165059 < baseStart_1165059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165063 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 5]
def baseStart_1165063 : Nat := 118140960795 + 1165063 * 2 ^ 59
def prefixEnd_1165063 : Nat := 4983230072969 + 3 ^ 40 * 1165063 * 2
def baseEnd_1165063 : Nat := 66470812418808935483831

theorem tailTrace_1165063 : CollatzResearch.WordTrace tailWord_1165063 prefixEnd_1165063 66470812418808935483831 := by
  unfold tailWord_1165063
  simp only [CollatzResearch.WordTrace]
  refine ⟨42493338578183202764147843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28328892385455468509431895 42493338578183202764147843)
  ·
    refine ⟨63740007867274804146221765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42493338578183202764147843 63740007867274804146221765)
    ·
      refine ⟨11951251475114025777416581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63740007867274804146221765 11951251475114025777416581)
      ·
        refine ⟨2240859651583879833265609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11951251475114025777416581 2240859651583879833265609)
        ·
          refine ⟨1680644738687909874949207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2240859651583879833265609 1680644738687909874949207)
          ·
            refine ⟨2520967108031864812423811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680644738687909874949207 2520967108031864812423811)
            ·
              refine ⟨3781450662047797218635717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520967108031864812423811 3781450662047797218635717)
              ·
                refine ⟨709021999133961978494197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3781450662047797218635717 709021999133961978494197)
                ·
                  refine ⟨66470812418808935483831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 709021999133961978494197 66470812418808935483831)
                  ·
                    rfl

theorem cell23_1165063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 5].length) (baseStart_1165063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165063 prefixEnd_1165063 := by exact prefixLift 1165063
  have htrace : WordTrace (prefixWord ++ tailWord_1165063) baseStart_1165063 baseEnd_1165063 := by
    simpa [prefixWord, tailWord_1165063, baseEnd_1165063] using wordTrace_append hprefix tailTrace_1165063
  have hstable : (prefixWord ++ tailWord_1165063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165063).length < 2 ^ (prefixWord ++ tailWord_1165063).sum := by decide
  have hdescent : baseEnd_1165063 < baseStart_1165063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165066 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_1165066 : Nat := 118140960795 + 1165066 * 2 ^ 59
def prefixEnd_1165066 : Nat := 4983230072969 + 3 ^ 40 * 1165066 * 2
def baseEnd_1165066 : Nat := 598238852211243907616965

theorem tailTrace_1165066 : CollatzResearch.WordTrace tailWord_1165066 prefixEnd_1165066 598238852211243907616965 := by
  unfold tailWord_1165066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10623361999293083569126763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28328965331448222851004701 10623361999293083569126763)
  ·
    refine ⟨15935042998939625353690145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10623361999293083569126763 15935042998939625353690145)
    ·
      refine ⟨11951282249204719015267609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15935042998939625353690145 11951282249204719015267609)
      ·
        refine ⟨8963461686903539261450707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11951282249204719015267609 8963461686903539261450707)
        ·
          refine ⟨13445192530355308892176061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8963461686903539261450707 13445192530355308892176061)
          ·
            refine ⟨5041947198883240834566023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13445192530355308892176061 5041947198883240834566023)
            ·
              refine ⟨7562920798324861251849035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041947198883240834566023 7562920798324861251849035)
              ·
                refine ⟨11344381197487291877773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7562920798324861251849035 11344381197487291877773553)
                ·
                  refine ⟨8508285898115468908330165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11344381197487291877773553 8508285898115468908330165)
                  ·
                    refine ⟨797651802948325210155953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508285898115468908330165 797651802948325210155953)
                    ·
                      refine ⟨598238852211243907616965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797651802948325210155953 598238852211243907616965)
                      ·
                        rfl

theorem cell23_1165066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_1165066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165066 prefixEnd_1165066 := by exact prefixLift 1165066
  have htrace : WordTrace (prefixWord ++ tailWord_1165066) baseStart_1165066 baseEnd_1165066 := by
    simpa [prefixWord, tailWord_1165066, baseEnd_1165066] using wordTrace_append hprefix tailTrace_1165066
  have hstable : (prefixWord ++ tailWord_1165066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165066).length < 2 ^ (prefixWord ++ tailWord_1165066).sum := by decide
  have hdescent : baseEnd_1165066 < baseStart_1165066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165096 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1165096 : Nat := 118140960795 + 1165096 * 2 ^ 59
def prefixEnd_1165096 : Nat := 4983230072969 + 3 ^ 40 * 1165096 * 2
def baseEnd_1165096 : Nat := 598254256630878790241827

theorem tailTrace_1165096 : CollatzResearch.WordTrace tailWord_1165096 prefixEnd_1165096 598254256630878790241827 := by
  unfold tailWord_1165096
  simp only [CollatzResearch.WordTrace]
  refine ⟨21247271093531824700049571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28329694791375766266732761 21247271093531824700049571)
  ·
    refine ⟨31870906640297737050074357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21247271093531824700049571 31870906640297737050074357)
    ·
      refine ⟨2987897497527912848444471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31870906640297737050074357 2987897497527912848444471)
      ·
        refine ⟨4481846246291869272666707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987897497527912848444471 4481846246291869272666707)
        ·
          refine ⟨6722769369437803909000061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481846246291869272666707 6722769369437803909000061)
          ·
            refine ⟨2521038513539176465875023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6722769369437803909000061 2521038513539176465875023)
            ·
              refine ⟨3781557770308764698812535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521038513539176465875023 3781557770308764698812535)
              ·
                refine ⟨5672336655463147048218803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781557770308764698812535 5672336655463147048218803)
                ·
                  refine ⟨8508504983194720572328205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672336655463147048218803 8508504983194720572328205)
                  ·
                    refine ⟨3190689368698020214623077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8508504983194720572328205 3190689368698020214623077)
                    ·
                      refine ⟨598254256630878790241827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3190689368698020214623077 598254256630878790241827)
                      ·
                        rfl

theorem cell23_1165096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1165096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165096 prefixEnd_1165096 := by exact prefixLift 1165096
  have htrace : WordTrace (prefixWord ++ tailWord_1165096) baseStart_1165096 baseEnd_1165096 := by
    simpa [prefixWord, tailWord_1165096, baseEnd_1165096] using wordTrace_append hprefix tailTrace_1165096
  have hstable : (prefixWord ++ tailWord_1165096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165096).length < 2 ^ (prefixWord ++ tailWord_1165096).sum := by decide
  have hdescent : baseEnd_1165096 < baseStart_1165096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165116 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_1165116 : Nat := 118140960795 + 1165116 * 2 ^ 59
def prefixEnd_1165116 : Nat := 4983230072969 + 3 ^ 40 * 1165116 * 2
def baseEnd_1165116 : Nat := 598264526243968711991735

theorem tailTrace_1165116 : CollatzResearch.WordTrace tailWord_1165116 prefixEnd_1165116 598264526243968711991735 := by
  unfold tailWord_1165116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21247635823495596407913601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28330181097994128543884801 21247635823495596407913601)
  ·
    refine ⟨15935726867621697305935201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21247635823495596407913601 15935726867621697305935201)
    ·
      refine ⟨11951795150716272979451401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15935726867621697305935201 11951795150716272979451401)
      ·
        refine ⟨8963846363037204734588551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11951795150716272979451401 8963846363037204734588551)
        ·
          refine ⟨13445769544555807101882827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8963846363037204734588551 13445769544555807101882827)
          ·
            refine ⟨20168654316833710652824241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13445769544555807101882827 20168654316833710652824241)
            ·
              refine ⟨15126490737625282989618181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20168654316833710652824241 15126490737625282989618181)
              ·
                refine ⟨2836217013304740560553409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15126490737625282989618181 2836217013304740560553409)
                ·
                  refine ⟨2127162759978555420415057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836217013304740560553409 2127162759978555420415057)
                  ·
                    refine ⟨1595372069983916565311293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127162759978555420415057 1595372069983916565311293)
                    ·
                      refine ⟨598264526243968711991735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595372069983916565311293 598264526243968711991735)
                      ·
                        rfl

theorem cell23_1165116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_1165116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165116 prefixEnd_1165116 := by exact prefixLift 1165116
  have htrace : WordTrace (prefixWord ++ tailWord_1165116) baseStart_1165116 baseEnd_1165116 := by
    simpa [prefixWord, tailWord_1165116, baseEnd_1165116] using wordTrace_append hprefix tailTrace_1165116
  have hstable : (prefixWord ++ tailWord_1165116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165116).length < 2 ^ (prefixWord ++ tailWord_1165116).sum := by decide
  have hdescent : baseEnd_1165116 < baseStart_1165116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165123 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 1, 4]
def baseStart_1165123 : Nat := 118140960795 + 1165123 * 2 ^ 59
def prefixEnd_1165123 : Nat := 4983230072969 + 3 ^ 40 * 1165123 * 2
def baseEnd_1165123 : Nat := 199422706869516728201401

theorem tailTrace_1165123 : CollatzResearch.WordTrace tailWord_1165123 prefixEnd_1165123 199422706869516728201401 := by
  unfold tailWord_1165123
  simp only [CollatzResearch.WordTrace]
  refine ⟨42495526957965833011332023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28330351305310555340888015 42495526957965833011332023)
  ·
    refine ⟨63743290436948749516998035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42495526957965833011332023 63743290436948749516998035)
    ·
      refine ⟨95614935655423124275497053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63743290436948749516998035 95614935655423124275497053)
      ·
        refine ⟨35855600870783671603311395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95614935655423124275497053 35855600870783671603311395)
        ·
          refine ⟨53783401306175507404967093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35855600870783671603311395 53783401306175507404967093)
          ·
            refine ⟨5042193872453953819215665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53783401306175507404967093 5042193872453953819215665)
            ·
              refine ⟨3781645404340465364411749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5042193872453953819215665 3781645404340465364411749)
              ·
                refine ⟨709058513313837255827203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3781645404340465364411749 709058513313837255827203)
                ·
                  refine ⟨1063587769970755883740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709058513313837255827203 1063587769970755883740805)
                  ·
                    refine ⟨199422706869516728201401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1063587769970755883740805 199422706869516728201401)
                    ·
                      rfl

theorem cell23_1165123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 4].length) (baseStart_1165123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165123 prefixEnd_1165123 := by exact prefixLift 1165123
  have htrace : WordTrace (prefixWord ++ tailWord_1165123) baseStart_1165123 baseEnd_1165123 := by
    simpa [prefixWord, tailWord_1165123, baseEnd_1165123] using wordTrace_append hprefix tailTrace_1165123
  have hstable : (prefixWord ++ tailWord_1165123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165123).length < 2 ^ (prefixWord ++ tailWord_1165123).sum := by decide
  have hdescent : baseEnd_1165123 < baseStart_1165123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165133 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1165133 : Nat := 118140960795 + 1165133 * 2 ^ 59
def prefixEnd_1165133 : Nat := 4983230072969 + 3 ^ 40 * 1165133 * 2
def baseEnd_1165133 : Nat := 598273255415095145479157

theorem tailTrace_1165133 : CollatzResearch.WordTrace tailWord_1165133 prefixEnd_1165133 598273255415095145479157 := by
  unfold tailWord_1165133
  simp only [CollatzResearch.WordTrace]
  refine ⟨42495891687929604719196053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28330594458619736479464035 42495891687929604719196053)
  ·
    refine ⟨1991994922871700221212315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42495891687929604719196053 1991994922871700221212315)
    ·
      refine ⟨2987992384307550331818473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991994922871700221212315 2987992384307550331818473)
      ·
        refine ⟨2240994288230662748863855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2987992384307550331818473 2240994288230662748863855)
        ·
          refine ⟨3361491432345994123295783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240994288230662748863855 3361491432345994123295783)
          ·
            refine ⟨5042237148518991184943675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361491432345994123295783 5042237148518991184943675)
            ·
              refine ⟨7563355722778486777415513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042237148518991184943675 7563355722778486777415513)
              ·
                refine ⟨5672516792083865083061635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7563355722778486777415513 5672516792083865083061635)
                ·
                  refine ⟨8508775188125797624592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672516792083865083061635 8508775188125797624592453)
                  ·
                    refine ⟨1595395347773587054611085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8508775188125797624592453 1595395347773587054611085)
                    ·
                      refine ⟨598273255415095145479157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595395347773587054611085 598273255415095145479157)
                      ·
                        rfl

theorem cell23_1165133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1165133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165133 prefixEnd_1165133 := by exact prefixLift 1165133
  have htrace : WordTrace (prefixWord ++ tailWord_1165133) baseStart_1165133 baseEnd_1165133 := by
    simpa [prefixWord, tailWord_1165133, baseEnd_1165133] using wordTrace_append hprefix tailTrace_1165133
  have hstable : (prefixWord ++ tailWord_1165133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165133).length < 2 ^ (prefixWord ++ tailWord_1165133).sum := by decide
  have hdescent : baseEnd_1165133 < baseStart_1165133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165174 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1165174 : Nat := 118140960795 + 1165174 * 2 ^ 59
def prefixEnd_1165174 : Nat := 4983230072969 + 3 ^ 40 * 1165174 * 2
def baseEnd_1165174 : Nat := 199431436040643161688823

theorem tailTrace_1165174 : CollatzResearch.WordTrace tailWord_1165174 prefixEnd_1165174 199431436040643161688823 := by
  unfold tailWord_1165174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656086692548816795089911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28331591387187379147625717 2656086692548816795089911)
  ·
    refine ⟨3984130038823225192634867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656086692548816795089911 3984130038823225192634867)
    ·
      refine ⟨5976195058234837788952301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984130038823225192634867 5976195058234837788952301)
      ·
        refine ⟨2241073146838064170857113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5976195058234837788952301 2241073146838064170857113)
        ·
          refine ⟨1680804860128548128142835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241073146838064170857113 1680804860128548128142835)
          ·
            refine ⟨2521207290192822192214253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680804860128548128142835 2521207290192822192214253)
            ·
              refine ⟨945452733822308322080345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2521207290192822192214253 945452733822308322080345)
              ·
                refine ⟨709089550366731241560259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945452733822308322080345 709089550366731241560259)
                ·
                  refine ⟨1063634325550096862340389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709089550366731241560259 1063634325550096862340389)
                  ·
                    refine ⟨199431436040643161688823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1063634325550096862340389 199431436040643161688823)
                    ·
                      rfl

theorem cell23_1165174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1165174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165174 prefixEnd_1165174 := by exact prefixLift 1165174
  have htrace : WordTrace (prefixWord ++ tailWord_1165174) baseStart_1165174 baseEnd_1165174 := by
    simpa [prefixWord, tailWord_1165174, baseEnd_1165174] using wordTrace_append hprefix tailTrace_1165174
  have hstable : (prefixWord ++ tailWord_1165174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165174).length < 2 ^ (prefixWord ++ tailWord_1165174).sum := by decide
  have hdescent : baseEnd_1165174 < baseStart_1165174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165209 : List Nat := [1, 2, 1, 2, 1, 3, 4, 9]
def baseStart_1165209 : Nat := 118140960795 + 1165209 * 2 ^ 59
def prefixEnd_1165209 : Nat := 4983230072969 + 3 ^ 40 * 1165209 * 2
def baseEnd_1165209 : Nat := 22159714072030994375141

theorem tailTrace_1165209 : CollatzResearch.WordTrace tailWord_1165209 prefixEnd_1165209 22159714072030994375141 := by
  unfold tailWord_1165209
  simp only [CollatzResearch.WordTrace]
  refine ⟨42498663635654269698962681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28332442423769513132641787 42498663635654269698962681)
  ·
    refine ⟨31873997726740702274222011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42498663635654269698962681 31873997726740702274222011)
    ·
      refine ⟨47810996590111053411333017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31873997726740702274222011 47810996590111053411333017)
      ·
        refine ⟨35858247442583290058499763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47810996590111053411333017 35858247442583290058499763)
        ·
          refine ⟨53787371163874935087749645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35858247442583290058499763 53787371163874935087749645)
          ·
            refine ⟨20170264186453100657906117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53787371163874935087749645 20170264186453100657906117)
            ·
              refine ⟨3781924534959956373357397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20170264186453100657906117 3781924534959956373357397)
              ·
                refine ⟨22159714072030994375141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3781924534959956373357397 22159714072030994375141)
                ·
                  rfl

theorem cell23_1165209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 9].length) (baseStart_1165209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165209 prefixEnd_1165209 := by exact prefixLift 1165209
  have htrace : WordTrace (prefixWord ++ tailWord_1165209) baseStart_1165209 baseEnd_1165209 := by
    simpa [prefixWord, tailWord_1165209, baseEnd_1165209] using wordTrace_append hprefix tailTrace_1165209
  have hstable : (prefixWord ++ tailWord_1165209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165209).length < 2 ^ (prefixWord ++ tailWord_1165209).sum := by decide
  have hdescent : baseEnd_1165209 < baseStart_1165209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165220 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_1165220 : Nat := 118140960795 + 1165220 * 2 ^ 59
def prefixEnd_1165220 : Nat := 4983230072969 + 3 ^ 40 * 1165220 * 2
def baseEnd_1165220 : Nat := 598317928232036305091257

theorem tailTrace_1165220 : CollatzResearch.WordTrace tailWord_1165220 prefixEnd_1165220 598317928232036305091257 := by
  unfold tailWord_1165220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249532419307209288806557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28332709892409612385075409 21249532419307209288806557)
  ·
    refine ⟨7968574657240203483302459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21249532419307209288806557 7968574657240203483302459)
    ·
      refine ⟨11952861985860305224953689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7968574657240203483302459 11952861985860305224953689)
      ·
        refine ⟨8964646489395228918715267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11952861985860305224953689 8964646489395228918715267)
        ·
          refine ⟨13446969734092843378072901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8964646489395228918715267 13446969734092843378072901)
          ·
            refine ⟨2521306825142408133388669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13446969734092843378072901 2521306825142408133388669)
            ·
              refine ⟨945490059428403050020751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2521306825142408133388669 945490059428403050020751)
              ·
                refine ⟨1418235089142604575031127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945490059428403050020751 1418235089142604575031127)
                ·
                  refine ⟨2127352633713906862546691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418235089142604575031127 2127352633713906862546691)
                  ·
                    refine ⟨3191028950570860293820037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2127352633713906862546691 3191028950570860293820037)
                    ·
                      refine ⟨598317928232036305091257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3191028950570860293820037 598317928232036305091257)
                      ·
                        rfl

theorem cell23_1165220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_1165220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165220 prefixEnd_1165220 := by exact prefixLift 1165220
  have htrace : WordTrace (prefixWord ++ tailWord_1165220) baseStart_1165220 baseEnd_1165220 := by
    simpa [prefixWord, tailWord_1165220, baseEnd_1165220] using wordTrace_append hprefix tailTrace_1165220
  have hstable : (prefixWord ++ tailWord_1165220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165220).length < 2 ^ (prefixWord ++ tailWord_1165220).sum := by decide
  have hdescent : baseEnd_1165220 < baseStart_1165220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165223 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1165223 : Nat := 118140960795 + 1165223 * 2 ^ 59
def prefixEnd_1165223 : Nat := 4983230072969 + 3 ^ 40 * 1165223 * 2
def baseEnd_1165223 : Nat := 598319468673999793353743

theorem tailTrace_1165223 : CollatzResearch.WordTrace tailWord_1165223 prefixEnd_1165223 598319468673999793353743 := by
  unfold tailWord_1165223
  simp only [CollatzResearch.WordTrace]
  refine ⟨42499174257603550089972323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28332782838402366726648215 42499174257603550089972323)
  ·
    refine ⟨63748761386405325134958485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42499174257603550089972323 63748761386405325134958485)
    ·
      refine ⟨2988223189987749615701179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63748761386405325134958485 2988223189987749615701179)
      ·
        refine ⟨4482334784981624423551769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988223189987749615701179 4482334784981624423551769)
        ·
          refine ⟨3361751088736218317663827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482334784981624423551769 3361751088736218317663827)
          ·
            refine ⟨5042626633104327476495741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361751088736218317663827 5042626633104327476495741)
            ·
              refine ⟨1890984987414122803685903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5042626633104327476495741 1890984987414122803685903)
              ·
                refine ⟨2836477481121184205528855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890984987414122803685903 2836477481121184205528855)
                ·
                  refine ⟨4254716221681776308293283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836477481121184205528855 4254716221681776308293283)
                  ·
                    refine ⟨6382074332522664462439925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254716221681776308293283 6382074332522664462439925)
                    ·
                      refine ⟨598319468673999793353743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6382074332522664462439925 598319468673999793353743)
                      ·
                        rfl

theorem cell23_1165223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1165223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165223 prefixEnd_1165223 := by exact prefixLift 1165223
  have htrace : WordTrace (prefixWord ++ tailWord_1165223) baseStart_1165223 baseEnd_1165223 := by
    simpa [prefixWord, tailWord_1165223, baseEnd_1165223] using wordTrace_append hprefix tailTrace_1165223
  have hstable : (prefixWord ++ tailWord_1165223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165223).length < 2 ^ (prefixWord ++ tailWord_1165223).sum := by decide
  have hdescent : baseEnd_1165223 < baseStart_1165223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165263 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 3, 3, 2]
def baseStart_1165263 : Nat := 118140960795 + 1165263 * 2 ^ 59
def prefixEnd_1165263 : Nat := 4983230072969 + 3 ^ 40 * 1165263 * 2
def baseEnd_1165263 : Nat := 598340007900179636853559

theorem tailTrace_1165263 : CollatzResearch.WordTrace tailWord_1165263 prefixEnd_1165263 598340007900179636853559 := by
  unfold tailWord_1165263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42500633177458636921428443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28333755451639091280952295 42500633177458636921428443)
  ·
    refine ⟨63750949766187955382142665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42500633177458636921428443 63750949766187955382142665)
    ·
      refine ⟨47813212324640966536606999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63750949766187955382142665 47813212324640966536606999)
      ·
        refine ⟨71719818486961449804910499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47813212324640966536606999 71719818486961449804910499)
        ·
          refine ⟨107579727730442174707365749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71719818486961449804910499 107579727730442174707365749)
          ·
            refine ⟨10085599474728953878815539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107579727730442174707365749 10085599474728953878815539)
            ·
              refine ⟨15128399212093430818223309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10085599474728953878815539 15128399212093430818223309)
              ·
                refine ⟨5673149704535036556833741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15128399212093430818223309 5673149704535036556833741)
                ·
                  refine ⟨2127431139200638708812653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5673149704535036556833741 2127431139200638708812653)
                  ·
                    refine ⟨797786677200239515804745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127431139200638708812653 797786677200239515804745)
                    ·
                      refine ⟨598340007900179636853559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797786677200239515804745 598340007900179636853559)
                      ·
                        rfl

theorem cell23_1165263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3, 2].length) (baseStart_1165263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165263 prefixEnd_1165263 := by exact prefixLift 1165263
  have htrace : WordTrace (prefixWord ++ tailWord_1165263) baseStart_1165263 baseEnd_1165263 := by
    simpa [prefixWord, tailWord_1165263, baseEnd_1165263] using wordTrace_append hprefix tailTrace_1165263
  have hstable : (prefixWord ++ tailWord_1165263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165263).length < 2 ^ (prefixWord ++ tailWord_1165263).sum := by decide
  have hdescent : baseEnd_1165263 < baseStart_1165263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165274 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_1165274 : Nat := 118140960795 + 1165274 * 2 ^ 59
def prefixEnd_1165274 : Nat := 4983230072969 + 3 ^ 40 * 1165274 * 2
def baseEnd_1165274 : Nat := 598345656187379093816009

theorem tailTrace_1165274 : CollatzResearch.WordTrace tailWord_1165274 prefixEnd_1165274 598345656187379093816009 := by
  unfold tailWord_1165274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10625258595104696450019719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28334022920279190533385917 10625258595104696450019719)
  ·
    refine ⟨15937887892657044675029579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10625258595104696450019719 15937887892657044675029579)
    ·
      refine ⟨23906831838985567012544369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15937887892657044675029579 23906831838985567012544369)
      ·
        refine ⟨17930123879239175259408277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23906831838985567012544369 17930123879239175259408277)
        ·
          refine ⟨840474556839336340284763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17930123879239175259408277 840474556839336340284763)
          ·
            refine ⟨1260711835259004510427145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840474556839336340284763 1260711835259004510427145)
            ·
              refine ⟨945533876444253382820359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260711835259004510427145 945533876444253382820359)
              ·
                refine ⟨1418300814666380074230539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945533876444253382820359 1418300814666380074230539)
                ·
                  refine ⟨2127451221999570111345809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418300814666380074230539 2127451221999570111345809)
                  ·
                    refine ⟨1595588416499677583509357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127451221999570111345809 1595588416499677583509357)
                    ·
                      refine ⟨598345656187379093816009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595588416499677583509357 598345656187379093816009)
                      ·
                        rfl

theorem cell23_1165274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_1165274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165274 prefixEnd_1165274 := by exact prefixLift 1165274
  have htrace : WordTrace (prefixWord ++ tailWord_1165274) baseStart_1165274 baseEnd_1165274 := by
    simpa [prefixWord, tailWord_1165274, baseEnd_1165274] using wordTrace_append hprefix tailTrace_1165274
  have hstable : (prefixWord ++ tailWord_1165274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165274).length < 2 ^ (prefixWord ++ tailWord_1165274).sum := by decide
  have hdescent : baseEnd_1165274 < baseStart_1165274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165296 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_1165296 : Nat := 118140960795 + 1165296 * 2 ^ 59
def prefixEnd_1165296 : Nat := 4983230072969 + 3 ^ 40 * 1165296 * 2
def baseEnd_1165296 : Nat := 598356952761778007740907

theorem tailTrace_1165296 : CollatzResearch.WordTrace tailWord_1165296 prefixEnd_1165296 598356952761778007740907 := by
  unfold tailWord_1165296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21250918393169541778689871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28334557857559389038253161 21250918393169541778689871)
  ·
    refine ⟨31876377589754312668034807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21250918393169541778689871 31876377589754312668034807)
    ·
      refine ⟨47814566384631469002052211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31876377589754312668034807 47814566384631469002052211)
      ·
        refine ⟨71721849576947203503078317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47814566384631469002052211 71721849576947203503078317)
        ·
          refine ⟨26895693591355201313654369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71721849576947203503078317 26895693591355201313654369)
          ·
            refine ⟨20171770193516400985240777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26895693591355201313654369 20171770193516400985240777)
            ·
              refine ⟨15128827645137300738930583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20171770193516400985240777 15128827645137300738930583)
              ·
                refine ⟨22693241467705951108395875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15128827645137300738930583 22693241467705951108395875)
                ·
                  refine ⟨34039862201558926662593813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22693241467705951108395875 34039862201558926662593813)
                  ·
                    refine ⟨1595618540698074687309085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34039862201558926662593813 1595618540698074687309085)
                    ·
                      refine ⟨598356952761778007740907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595618540698074687309085 598356952761778007740907)
                      ·
                        rfl

theorem cell23_1165296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_1165296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165296 prefixEnd_1165296 := by exact prefixLift 1165296
  have htrace : WordTrace (prefixWord ++ tailWord_1165296) baseStart_1165296 baseEnd_1165296 := by
    simpa [prefixWord, tailWord_1165296, baseEnd_1165296] using wordTrace_append hprefix tailTrace_1165296
  have hstable : (prefixWord ++ tailWord_1165296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165296).length < 2 ^ (prefixWord ++ tailWord_1165296).sum := by decide
  have hdescent : baseEnd_1165296 < baseStart_1165296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165423 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 6]
def baseStart_1165423 : Nat := 118140960795 + 1165423 * 2 ^ 59
def prefixEnd_1165423 : Nat := 4983230072969 + 3 ^ 40 * 1165423 * 2
def baseEnd_1165423 : Nat := 66491351644988778983647

theorem tailTrace_1165423 : CollatzResearch.WordTrace tailWord_1165423 prefixEnd_1165423 66491351644988778983647 := by
  unfold tailWord_1165423
  simp only [CollatzResearch.WordTrace]
  refine ⟨42506468856878984247252923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28337645904585989498168615 42506468856878984247252923)
  ·
    refine ⟨63759703285318476370879385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42506468856878984247252923 63759703285318476370879385)
    ·
      refine ⟨47819777463988857278159539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63759703285318476370879385 47819777463988857278159539)
      ·
        refine ⟨71729666195983285917239309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47819777463988857278159539 71729666195983285917239309)
        ·
          refine ⟨26898624823493732218964741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71729666195983285917239309 26898624823493732218964741)
          ·
            refine ⟨5043492154405074791055889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26898624823493732218964741 5043492154405074791055889)
            ·
              refine ⟨3782619115803806093291917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043492154405074791055889 3782619115803806093291917)
              ·
                refine ⟨1418482168426427284984469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3782619115803806093291917 1418482168426427284984469)
                ·
                  refine ⟨66491351644988778983647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1418482168426427284984469 66491351644988778983647)
                  ·
                    rfl

theorem cell23_1165423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 6].length) (baseStart_1165423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165423 prefixEnd_1165423 := by exact prefixLift 1165423
  have htrace : WordTrace (prefixWord ++ tailWord_1165423) baseStart_1165423 baseEnd_1165423 := by
    simpa [prefixWord, tailWord_1165423, baseEnd_1165423] using wordTrace_append hprefix tailTrace_1165423
  have hstable : (prefixWord ++ tailWord_1165423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165423).length < 2 ^ (prefixWord ++ tailWord_1165423).sum := by decide
  have hdescent : baseEnd_1165423 < baseStart_1165423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165437 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_1165437 : Nat := 118140960795 + 1165437 * 2 ^ 59
def prefixEnd_1165437 : Nat := 4983230072969 + 3 ^ 40 * 1165437 * 2
def baseEnd_1165437 : Nat := 598429353534061956077759

theorem tailTrace_1165437 : CollatzResearch.WordTrace tailWord_1165437 prefixEnd_1165437 598429353534061956077759 := by
  unfold tailWord_1165437
  simp only [CollatzResearch.WordTrace]
  refine ⟨42506979478828264638262565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28337986319218843092175043 42506979478828264638262565)
  ·
    refine ⟨7970058652280299619674231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42506979478828264638262565 7970058652280299619674231)
    ·
      refine ⟨11955087978420449429511347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970058652280299619674231 11955087978420449429511347)
      ·
        refine ⟨17932631967630674144267021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955087978420449429511347 17932631967630674144267021)
        ·
          refine ⟨6724736987861502804100133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17932631967630674144267021 6724736987861502804100133)
          ·
            refine ⟨1260888185224031775768775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6724736987861502804100133 1260888185224031775768775)
            ·
              refine ⟨1891332277836047663653163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260888185224031775768775 1891332277836047663653163)
              ·
                refine ⟨2836998416754071495479745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891332277836047663653163 2836998416754071495479745)
                ·
                  refine ⟨2127748812565553621609809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836998416754071495479745 2127748812565553621609809)
                  ·
                    refine ⟨1595811609424165216207357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127748812565553621609809 1595811609424165216207357)
                    ·
                      refine ⟨598429353534061956077759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595811609424165216207357 598429353534061956077759)
                      ·
                        rfl

theorem cell23_1165437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_1165437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165437 prefixEnd_1165437 := by exact prefixLift 1165437
  have htrace : WordTrace (prefixWord ++ tailWord_1165437) baseStart_1165437 baseEnd_1165437 := by
    simpa [prefixWord, tailWord_1165437, baseEnd_1165437] using wordTrace_append hprefix tailTrace_1165437
  have hstable : (prefixWord ++ tailWord_1165437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165437).length < 2 ^ (prefixWord ++ tailWord_1165437).sum := by decide
  have hdescent : baseEnd_1165437 < baseStart_1165437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165467 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 1, 1, 3]
def baseStart_1165467 : Nat := 118140960795 + 1165467 * 2 ^ 59
def prefixEnd_1165467 : Nat := 4983230072969 + 3 ^ 40 * 1165467 * 2
def baseEnd_1165467 : Nat := 598444757953696838702621

theorem tailTrace_1165467 : CollatzResearch.WordTrace tailWord_1165467 prefixEnd_1165467 598444757953696838702621 := by
  unfold tailWord_1165467
  simp only [CollatzResearch.WordTrace]
  refine ⟨42508073668719579761854655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28338715779146386507903103 42508073668719579761854655)
  ·
    refine ⟨63762110503079369642781983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42508073668719579761854655 63762110503079369642781983)
    ·
      refine ⟨95643165754619054464172975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63762110503079369642781983 95643165754619054464172975)
      ·
        refine ⟨143464748631928581696259463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95643165754619054464172975 143464748631928581696259463)
        ·
          refine ⟨215197122947892872544389195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143464748631928581696259463 215197122947892872544389195)
          ·
            refine ⟨322795684421839308816583793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215197122947892872544389195 322795684421839308816583793)
            ·
              refine ⟨242096763316379481612437845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322795684421839308816583793 242096763316379481612437845)
              ·
                refine ⟨709267861278455512536439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 242096763316379481612437845 709267861278455512536439)
                ·
                  refine ⟨1063901791917683268804659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709267861278455512536439 1063901791917683268804659)
                  ·
                    refine ⟨1595852687876524903206989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1063901791917683268804659 1595852687876524903206989)
                    ·
                      refine ⟨598444757953696838702621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595852687876524903206989 598444757953696838702621)
                      ·
                        rfl

theorem cell23_1165467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 1, 3].length) (baseStart_1165467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165467 prefixEnd_1165467 := by exact prefixLift 1165467
  have htrace : WordTrace (prefixWord ++ tailWord_1165467) baseStart_1165467 baseEnd_1165467 := by
    simpa [prefixWord, tailWord_1165467, baseEnd_1165467] using wordTrace_append hprefix tailTrace_1165467
  have hstable : (prefixWord ++ tailWord_1165467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165467).length < 2 ^ (prefixWord ++ tailWord_1165467).sum := by decide
  have hdescent : baseEnd_1165467 < baseStart_1165467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165490 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_1165490 : Nat := 118140960795 + 1165490 * 2 ^ 59
def prefixEnd_1165490 : Nat := 4983230072969 + 3 ^ 40 * 1165490 * 2
def baseEnd_1165490 : Nat := 598456568008750248715015

theorem tailTrace_1165490 : CollatzResearch.WordTrace tailWord_1165490 prefixEnd_1165490 598456568008750248715015 := by
  unfold tailWord_1165490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627228136909063672485481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28339275031757503126627949 10627228136909063672485481)
  ·
    refine ⟨7970421102681797754364111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10627228136909063672485481 7970421102681797754364111)
    ·
      refine ⟨11955631654022696631546167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970421102681797754364111 11955631654022696631546167)
      ·
        refine ⟨17933447481034044947319251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955631654022696631546167 17933447481034044947319251)
        ·
          refine ⟨26900171221551067420978877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17933447481034044947319251 26900171221551067420978877)
          ·
            refine ⟨10087564208081650282867079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26900171221551067420978877 10087564208081650282867079)
            ·
              refine ⟨15131346312122475424300619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10087564208081650282867079 15131346312122475424300619)
              ·
                refine ⟨22697019468183713136450929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15131346312122475424300619 22697019468183713136450929)
                ·
                  refine ⟨17022764601137784852338197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22697019468183713136450929 17022764601137784852338197)
                  ·
                    refine ⟨797942090678333664953353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17022764601137784852338197 797942090678333664953353)
                    ·
                      refine ⟨598456568008750248715015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 797942090678333664953353 598456568008750248715015)
                      ·
                        rfl

theorem cell23_1165490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_1165490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165490 prefixEnd_1165490 := by exact prefixLift 1165490
  have htrace : WordTrace (prefixWord ++ tailWord_1165490) baseStart_1165490 baseEnd_1165490 := by
    simpa [prefixWord, tailWord_1165490, baseEnd_1165490] using wordTrace_append hprefix tailTrace_1165490
  have hstable : (prefixWord ++ tailWord_1165490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165490).length < 2 ^ (prefixWord ++ tailWord_1165490).sum := by decide
  have hdescent : baseEnd_1165490 < baseStart_1165490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165503 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_1165503 : Nat := 118140960795 + 1165503 * 2 ^ 59
def prefixEnd_1165503 : Nat := 4983230072969 + 3 ^ 40 * 1165503 * 2
def baseEnd_1165503 : Nat := 598463243257258697852455

theorem tailTrace_1165503 : CollatzResearch.WordTrace tailWord_1165503 prefixEnd_1165503 598463243257258697852455 := by
  unfold tailWord_1165503
  simp only [CollatzResearch.WordTrace]
  refine ⟨42509386696589157910165163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28339591131059438606776775 42509386696589157910165163)
  ·
    refine ⟨63764080044883736865247745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42509386696589157910165163 63764080044883736865247745)
    ·
      refine ⟨47823060033662802648935809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63764080044883736865247745 47823060033662802648935809)
      ·
        refine ⟨35867295025247101986701857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47823060033662802648935809 35867295025247101986701857)
        ·
          refine ⟨26900471268935326490026393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35867295025247101986701857 26900471268935326490026393)
          ·
            refine ⟨20175353451701494867519795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26900471268935326490026393 20175353451701494867519795)
            ·
              refine ⟨30263030177552242301279693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20175353451701494867519795 30263030177552242301279693)
              ·
                refine ⟨11348636316582090862979885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30263030177552242301279693 11348636316582090862979885)
                ·
                  refine ⟨4255738618718284073617457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11348636316582090862979885 4255738618718284073617457)
                  ·
                    refine ⟨3191803964038713055213093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4255738618718284073617457 3191803964038713055213093)
                    ·
                      refine ⟨598463243257258697852455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3191803964038713055213093 598463243257258697852455)
                      ·
                        rfl

theorem cell23_1165503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_1165503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165503 prefixEnd_1165503 := by exact prefixLift 1165503
  have htrace : WordTrace (prefixWord ++ tailWord_1165503) baseStart_1165503 baseEnd_1165503 := by
    simpa [prefixWord, tailWord_1165503, baseEnd_1165503] using wordTrace_append hprefix tailTrace_1165503
  have hstable : (prefixWord ++ tailWord_1165503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165503).length < 2 ^ (prefixWord ++ tailWord_1165503).sum := by decide
  have hdescent : baseEnd_1165503 < baseStart_1165503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165523 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3]
def baseStart_1165523 : Nat := 118140960795 + 1165523 * 2 ^ 59
def prefixEnd_1165523 : Nat := 4983230072969 + 3 ^ 40 * 1165523 * 2
def baseEnd_1165523 : Nat := 598473512870348619602363

theorem tailTrace_1165523 : CollatzResearch.WordTrace tailWord_1165523 prefixEnd_1165523 598473512870348619602363 := by
  unfold tailWord_1165523
  simp only [CollatzResearch.WordTrace]
  refine ⟨42510116156516701325893223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28340077437677800883928815 42510116156516701325893223)
  ·
    refine ⟨63765174234775051988839835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42510116156516701325893223 63765174234775051988839835)
    ·
      refine ⟨95647761352162577983259753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63765174234775051988839835 95647761352162577983259753)
      ·
        refine ⟨71735821014121933487444815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95647761352162577983259753 71735821014121933487444815)
        ·
          refine ⟨107603731521182900231167223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71735821014121933487444815 107603731521182900231167223)
          ·
            refine ⟨161405597281774350346750835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107603731521182900231167223 161405597281774350346750835)
            ·
              refine ⟨242108395922661525520126253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161405597281774350346750835 242108395922661525520126253)
              ·
                refine ⟨90790648470998072070047345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242108395922661525520126253 90790648470998072070047345)
                ·
                  refine ⟨68092986353248554052535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90790648470998072070047345 68092986353248554052535509)
                  ·
                    refine ⟨1595929367654262985606301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68092986353248554052535509 1595929367654262985606301)
                    ·
                      refine ⟨598473512870348619602363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595929367654262985606301 598473512870348619602363)
                      ·
                        rfl

theorem cell23_1165523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_1165523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165523 prefixEnd_1165523 := by exact prefixLift 1165523
  have htrace : WordTrace (prefixWord ++ tailWord_1165523) baseStart_1165523 baseEnd_1165523 := by
    simpa [prefixWord, tailWord_1165523, baseEnd_1165523] using wordTrace_append hprefix tailTrace_1165523
  have hstable : (prefixWord ++ tailWord_1165523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165523).length < 2 ^ (prefixWord ++ tailWord_1165523).sum := by decide
  have hdescent : baseEnd_1165523 < baseStart_1165523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165538 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1165538 : Nat := 118140960795 + 1165538 * 2 ^ 59
def prefixEnd_1165538 : Nat := 4983230072969 + 3 ^ 40 * 1165538 * 2
def baseEnd_1165538 : Nat := 199493738360055353638265

theorem tailTrace_1165538 : CollatzResearch.WordTrace tailWord_1165538 prefixEnd_1165538 199493738360055353638265 := by
  unfold tailWord_1165538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627665812865589721922317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28340442167641572591792845 10627665812865589721922317)
  ·
    refine ⟨3985374679824596145720869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10627665812865589721922317 3985374679824596145720869)
    ·
      refine ⟨747257752467111777322663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3985374679824596145720869 747257752467111777322663)
      ·
        refine ⟨1120886628700667665983995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747257752467111777322663 1120886628700667665983995)
        ·
          refine ⟨1681329943051001498975993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120886628700667665983995 1681329943051001498975993)
          ·
            refine ⟨1260997457288251124231995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1681329943051001498975993 1260997457288251124231995)
            ·
              refine ⟨1891496185932376686347993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260997457288251124231995 1891496185932376686347993)
              ·
                refine ⟨1418622139449282514760995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891496185932376686347993 1418622139449282514760995)
                ·
                  refine ⟨2127933209173923772141493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418622139449282514760995 2127933209173923772141493)
                  ·
                    refine ⟨199493738360055353638265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2127933209173923772141493 199493738360055353638265)
                    ·
                      rfl

theorem cell23_1165538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1165538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165538 prefixEnd_1165538 := by exact prefixLift 1165538
  have htrace : WordTrace (prefixWord ++ tailWord_1165538) baseStart_1165538 baseEnd_1165538 := by
    simpa [prefixWord, tailWord_1165538, baseEnd_1165538] using wordTrace_append hprefix tailTrace_1165538
  have hstable : (prefixWord ++ tailWord_1165538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165538).length < 2 ^ (prefixWord ++ tailWord_1165538).sum := by decide
  have hdescent : baseEnd_1165538 < baseStart_1165538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165540 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1165540 : Nat := 118140960795 + 1165540 * 2 ^ 59
def prefixEnd_1165540 : Nat := 4983230072969 + 3 ^ 40 * 1165540 * 2
def baseEnd_1165540 : Nat := 598482242041475053089785

theorem tailTrace_1165540 : CollatzResearch.WordTrace tailWord_1165540 prefixEnd_1165540 598482242041475053089785 := by
  unfold tailWord_1165540
  simp only [CollatzResearch.WordTrace]
  refine ⟨21255368098727556614631037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28340490798303408819508049 21255368098727556614631037)
  ·
    refine ⟨7970763037022833730486639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21255368098727556614631037 7970763037022833730486639)
    ·
      refine ⟨11956144555534250595729959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970763037022833730486639 11956144555534250595729959)
      ·
        refine ⟨17934216833301375893594939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11956144555534250595729959 17934216833301375893594939)
        ·
          refine ⟨26901325249952063840392409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17934216833301375893594939 26901325249952063840392409)
          ·
            refine ⟨20175993937464047880294307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26901325249952063840392409 20175993937464047880294307)
            ·
              refine ⟨30263990906196071820441461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20175993937464047880294307 30263990906196071820441461)
              ·
                refine ⟨2837249147455881733166387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30263990906196071820441461 2837249147455881733166387)
                ·
                  refine ⟨4255873721183822599749581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837249147455881733166387 4255873721183822599749581)
                  ·
                    refine ⟨1595952645443933474906093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4255873721183822599749581 1595952645443933474906093)
                    ·
                      refine ⟨598482242041475053089785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595952645443933474906093 598482242041475053089785)
                      ·
                        rfl

theorem cell23_1165540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1165540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165540 prefixEnd_1165540 := by exact prefixLift 1165540
  have htrace : WordTrace (prefixWord ++ tailWord_1165540) baseStart_1165540 baseEnd_1165540 := by
    simpa [prefixWord, tailWord_1165540, baseEnd_1165540] using wordTrace_append hprefix tailTrace_1165540
  have hstable : (prefixWord ++ tailWord_1165540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165540).length < 2 ^ (prefixWord ++ tailWord_1165540).sum := by decide
  have hdescent : baseEnd_1165540 < baseStart_1165540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165544 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1165544 : Nat := 118140960795 + 1165544 * 2 ^ 59
def prefixEnd_1165544 : Nat := 4983230072969 + 3 ^ 40 * 1165544 * 2
def baseEnd_1165544 : Nat := 598484295964093037439767

theorem tailTrace_1165544 : CollatzResearch.WordTrace tailWord_1165544 prefixEnd_1165544 598484295964093037439767 := by
  unfold tailWord_1165544
  simp only [CollatzResearch.WordTrace]
  refine ⟨21255441044720310956203843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28340588059627081274938457 21255441044720310956203843)
  ·
    refine ⟨31883161567080466434305765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21255441044720310956203843 31883161567080466434305765)
    ·
      refine ⟨5978092793827587456432331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31883161567080466434305765 5978092793827587456432331)
      ·
        refine ⟨8967139190741381184648497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978092793827587456432331 8967139190741381184648497)
        ·
          refine ⟨6725354393056035888486373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8967139190741381184648497 6725354393056035888486373)
          ·
            refine ⟨1261003948698006729091195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6725354393056035888486373 1261003948698006729091195)
            ·
              refine ⟨1891505923047010093636793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261003948698006729091195 1891505923047010093636793)
              ·
                refine ⟨1418629442285257570227595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891505923047010093636793 1418629442285257570227595)
                ·
                  refine ⟨2127944163427886355341393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418629442285257570227595 2127944163427886355341393)
                  ·
                    refine ⟨1595958122570914766506045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127944163427886355341393 1595958122570914766506045)
                    ·
                      refine ⟨598484295964093037439767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1595958122570914766506045 598484295964093037439767)
                      ·
                        rfl

theorem cell23_1165544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1165544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165544 prefixEnd_1165544 := by exact prefixLift 1165544
  have htrace : WordTrace (prefixWord ++ tailWord_1165544) baseStart_1165544 baseEnd_1165544 := by
    simpa [prefixWord, tailWord_1165544, baseEnd_1165544] using wordTrace_append hprefix tailTrace_1165544
  have hstable : (prefixWord ++ tailWord_1165544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165544).length < 2 ^ (prefixWord ++ tailWord_1165544).sum := by decide
  have hdescent : baseEnd_1165544 < baseStart_1165544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165553 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1165553 : Nat := 118140960795 + 1165553 * 2 ^ 59
def prefixEnd_1165553 : Nat := 4983230072969 + 3 ^ 40 * 1165553 * 2
def baseEnd_1165553 : Nat := 598488917289983502227225

theorem tailTrace_1165553 : CollatzResearch.WordTrace tailWord_1165553 prefixEnd_1165553 598488917289983502227225 := by
  unfold tailWord_1165553
  simp only [CollatzResearch.WordTrace]
  refine ⟨42511210346408016449485313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28340806897605344299656875 42511210346408016449485313)
  ·
    refine ⟨31883407759806012337113985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42511210346408016449485313 31883407759806012337113985)
    ·
      refine ⟨23912555819854509252835489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31883407759806012337113985 23912555819854509252835489)
      ·
        refine ⟨17934416864890881939626617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23912555819854509252835489 17934416864890881939626617)
        ·
          refine ⟨13450812648668161454719963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17934416864890881939626617 13450812648668161454719963)
          ·
            refine ⟨20176218973002242182079945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13450812648668161454719963 20176218973002242182079945)
            ·
              refine ⟨15132164229751681636559959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20176218973002242182079945 15132164229751681636559959)
              ·
                refine ⟨22698246344627522454839939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15132164229751681636559959 22698246344627522454839939)
                ·
                  refine ⟨34047369516941283682259909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22698246344627522454839939 34047369516941283682259909)
                  ·
                    refine ⟨6383881784426490690423733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34047369516941283682259909 6383881784426490690423733)
                    ·
                      refine ⟨598488917289983502227225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6383881784426490690423733 598488917289983502227225)
                      ·
                        rfl

theorem cell23_1165553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1165553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165553 prefixEnd_1165553 := by exact prefixLift 1165553
  have htrace : WordTrace (prefixWord ++ tailWord_1165553) baseStart_1165553 baseEnd_1165553 := by
    simpa [prefixWord, tailWord_1165553, baseEnd_1165553] using wordTrace_append hprefix tailTrace_1165553
  have hstable : (prefixWord ++ tailWord_1165553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165553).length < 2 ^ (prefixWord ++ tailWord_1165553).sum := by decide
  have hdescent : baseEnd_1165553 < baseStart_1165553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165563 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_1165563 : Nat := 118140960795 + 1165563 * 2 ^ 59
def prefixEnd_1165563 : Nat := 4983230072969 + 3 ^ 40 * 1165563 * 2
def baseEnd_1165563 : Nat := 598494052096528463102179

theorem tailTrace_1165563 : CollatzResearch.WordTrace tailWord_1165563 prefixEnd_1165563 598494052096528463102179 := by
  unfold tailWord_1165563
  simp only [CollatzResearch.WordTrace]
  refine ⟨42511575076371788157349343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28341050050914525438232895 42511575076371788157349343)
  ·
    refine ⟨63767362614557682236024015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42511575076371788157349343 63767362614557682236024015)
    ·
      refine ⟨95651043921836523354036023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63767362614557682236024015 95651043921836523354036023)
      ·
        refine ⟨143476565882754785031054035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95651043921836523354036023 143476565882754785031054035)
        ·
          refine ⟨215214848824132177546581053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143476565882754785031054035 215214848824132177546581053)
          ·
            refine ⟨80705568309049566579967895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215214848824132177546581053 80705568309049566579967895)
            ·
              refine ⟨121058352463574349869951843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80705568309049566579967895 121058352463574349869951843)
              ·
                refine ⟨181587528695361524804927765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121058352463574349869951843 181587528695361524804927765)
                ·
                  refine ⟨8511915407595071475230989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181587528695361524804927765 8511915407595071475230989)
                  ·
                    refine ⟨3191968277848151803211621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8511915407595071475230989 3191968277848151803211621)
                    ·
                      refine ⟨598494052096528463102179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3191968277848151803211621 598494052096528463102179)
                      ·
                        rfl

theorem cell23_1165563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_1165563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165563 prefixEnd_1165563 := by exact prefixLift 1165563
  have htrace : WordTrace (prefixWord ++ tailWord_1165563) baseStart_1165563 baseEnd_1165563 := by
    simpa [prefixWord, tailWord_1165563, baseEnd_1165563] using wordTrace_append hprefix tailTrace_1165563
  have hstable : (prefixWord ++ tailWord_1165563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165563).length < 2 ^ (prefixWord ++ tailWord_1165563).sum := by decide
  have hdescent : baseEnd_1165563 < baseStart_1165563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165583 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_1165583 : Nat := 118140960795 + 1165583 * 2 ^ 59
def prefixEnd_1165583 : Nat := 4983230072969 + 3 ^ 40 * 1165583 * 2
def baseEnd_1165583 : Nat := 598504321709618384852087

theorem tailTrace_1165583 : CollatzResearch.WordTrace tailWord_1165583 prefixEnd_1165583 598504321709618384852087 := by
  unfold tailWord_1165583
  simp only [CollatzResearch.WordTrace]
  refine ⟨42512304536299331573077403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28341536357532887715384935 42512304536299331573077403)
  ·
    refine ⟨63768456804448997359616105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42512304536299331573077403 63768456804448997359616105)
    ·
      refine ⟨47826342603336748019712079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63768456804448997359616105 47826342603336748019712079)
      ·
        refine ⟨71739513905005122029568119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47826342603336748019712079 71739513905005122029568119)
        ·
          refine ⟨107609270857507683044352179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71739513905005122029568119 107609270857507683044352179)
          ·
            refine ⟨161413906286261524566528269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107609270857507683044352179 161413906286261524566528269)
            ·
              refine ⟨60530214857348071712448101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161413906286261524566528269 60530214857348071712448101)
              ·
                refine ⟨11349415285752763446084019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60530214857348071712448101 11349415285752763446084019)
                ·
                  refine ⟨17024122928629145169126029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11349415285752763446084019 17024122928629145169126029)
                  ·
                    refine ⟨6384046098235929438422261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17024122928629145169126029 6384046098235929438422261)
                    ·
                      refine ⟨598504321709618384852087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6384046098235929438422261 598504321709618384852087)
                      ·
                        rfl

theorem cell23_1165583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_1165583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165583 prefixEnd_1165583 := by exact prefixLift 1165583
  have htrace : WordTrace (prefixWord ++ tailWord_1165583) baseStart_1165583 baseEnd_1165583 := by
    simpa [prefixWord, tailWord_1165583, baseEnd_1165583] using wordTrace_append hprefix tailTrace_1165583
  have hstable : (prefixWord ++ tailWord_1165583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165583).length < 2 ^ (prefixWord ++ tailWord_1165583).sum := by decide
  have hdescent : baseEnd_1165583 < baseStart_1165583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165618 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_1165618 : Nat := 118140960795 + 1165618 * 2 ^ 59
def prefixEnd_1165618 : Nat := 4983230072969 + 3 ^ 40 * 1165618 * 2
def baseEnd_1165618 : Nat := 598522293532525747914427

theorem tailTrace_1165618 : CollatzResearch.WordTrace tailWord_1165618 prefixEnd_1165618 598522293532525747914427 := by
  unfold tailWord_1165618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10628395272793133137650377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28342387394115021700401005 10628395272793133137650377)
  ·
    refine ⟨7971296454594849853237783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10628395272793133137650377 7971296454594849853237783)
    ·
      refine ⟨11956944681892274779856675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971296454594849853237783 11956944681892274779856675)
      ·
        refine ⟨17935417022838412169785013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11956944681892274779856675 17935417022838412169785013)
        ·
          refine ⟨1681445345891101140917345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17935417022838412169785013 1681445345891101140917345)
          ·
            refine ⟨1261084009418325855688009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1681445345891101140917345 1261084009418325855688009)
            ·
              refine ⟨945813007063744391766007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261084009418325855688009 945813007063744391766007)
              ·
                refine ⟨1418719510595616587649011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945813007063744391766007 1418719510595616587649011)
                ·
                  refine ⟨2128079265893424881473517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418719510595616587649011 2128079265893424881473517)
                  ·
                    refine ⟨798029724710034330552569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128079265893424881473517 798029724710034330552569)
                    ·
                      refine ⟨598522293532525747914427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798029724710034330552569 598522293532525747914427)
                      ·
                        rfl

theorem cell23_1165618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_1165618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165618 prefixEnd_1165618 := by exact prefixLift 1165618
  have htrace : WordTrace (prefixWord ++ tailWord_1165618) baseStart_1165618 baseEnd_1165618 := by
    simpa [prefixWord, tailWord_1165618, baseEnd_1165618] using wordTrace_append hprefix tailTrace_1165618
  have hstable : (prefixWord ++ tailWord_1165618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165618).length < 2 ^ (prefixWord ++ tailWord_1165618).sum := by decide
  have hdescent : baseEnd_1165618 < baseStart_1165618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165650 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1165650 : Nat := 118140960795 + 1165650 * 2 ^ 59
def prefixEnd_1165650 : Nat := 4983230072969 + 3 ^ 40 * 1165650 * 2
def baseEnd_1165650 : Nat := 199512908304489874238093

theorem tailTrace_1165650 : CollatzResearch.WordTrace tailWord_1165650 prefixEnd_1165650 199512908304489874238093 := by
  unfold tailWord_1165650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10628687056764150503941601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28343165484704401343844269 10628687056764150503941601)
  ·
    refine ⟨7971515292573112877956201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10628687056764150503941601 7971515292573112877956201)
    ·
      refine ⟨5978636469429834658467151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7971515292573112877956201 5978636469429834658467151)
      ·
        refine ⟨8967954704144751987700727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978636469429834658467151 8967954704144751987700727)
        ·
          refine ⟨13451932056217127981551091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967954704144751987700727 13451932056217127981551091)
          ·
            refine ⟨20177898084325691972326637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13451932056217127981551091 20177898084325691972326637)
            ·
              refine ⟨7566711781622134489622489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20177898084325691972326637 7566711781622134489622489)
              ·
                refine ⟨5675033836216600867216867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7566711781622134489622489 5675033836216600867216867)
                ·
                  refine ⟨8512550754324901300825301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675033836216600867216867 8512550754324901300825301)
                  ·
                    refine ⟨199512908304489874238093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8512550754324901300825301 199512908304489874238093)
                    ·
                      rfl

theorem cell23_1165650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1165650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165650 prefixEnd_1165650 := by exact prefixLift 1165650
  have htrace : WordTrace (prefixWord ++ tailWord_1165650) baseStart_1165650 baseEnd_1165650 := by
    simpa [prefixWord, tailWord_1165650, baseEnd_1165650] using wordTrace_append hprefix tailTrace_1165650
  have hstable : (prefixWord ++ tailWord_1165650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165650).length < 2 ^ (prefixWord ++ tailWord_1165650).sum := by decide
  have hdescent : baseEnd_1165650 < baseStart_1165650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165687 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_1165687 : Nat := 118140960795 + 1165687 * 2 ^ 59
def prefixEnd_1165687 : Nat := 4983230072969 + 3 ^ 40 * 1165687 * 2
def baseEnd_1165687 : Nat := 598557723697685977951609

theorem tailTrace_1165687 : CollatzResearch.WordTrace tailWord_1165687 prefixEnd_1165687 598557723697685977951609 := by
  unfold tailWord_1165687
  simp only [CollatzResearch.WordTrace]
  refine ⟨42516097727922557334863315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28344065151948371556575543 42516097727922557334863315)
  ·
    refine ⟨63774146591883836002294973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42516097727922557334863315 63774146591883836002294973)
    ·
      refine ⟨23915304971956438500860615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63774146591883836002294973 23915304971956438500860615)
      ·
        refine ⟨35872957457934657751290923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23915304971956438500860615 35872957457934657751290923)
        ·
          refine ⟨53809436186901986626936385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35872957457934657751290923 53809436186901986626936385)
          ·
            refine ⟨40357077140176489970202289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53809436186901986626936385 40357077140176489970202289)
            ·
              refine ⟨30267807855132367477651717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40357077140176489970202289 30267807855132367477651717)
              ·
                refine ⟨5675213972837318902059697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30267807855132367477651717 5675213972837318902059697)
                ·
                  refine ⟨4256410479627989176544773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5675213972837318902059697 4256410479627989176544773)
                  ·
                    refine ⟨798076964930247970602145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256410479627989176544773 798076964930247970602145)
                    ·
                      refine ⟨598557723697685977951609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798076964930247970602145 598557723697685977951609)
                      ·
                        rfl

theorem cell23_1165687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_1165687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165687 prefixEnd_1165687 := by exact prefixLift 1165687
  have htrace : WordTrace (prefixWord ++ tailWord_1165687) baseStart_1165687 baseEnd_1165687 := by
    simpa [prefixWord, tailWord_1165687, baseEnd_1165687] using wordTrace_append hprefix tailTrace_1165687
  have hstable : (prefixWord ++ tailWord_1165687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165687).length < 2 ^ (prefixWord ++ tailWord_1165687).sum := by decide
  have hdescent : baseEnd_1165687 < baseStart_1165687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165747 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 5, 2]
def baseStart_1165747 : Nat := 118140960795 + 1165747 * 2 ^ 59
def prefixEnd_1165747 : Nat := 4983230072969 + 3 ^ 40 * 1165747 * 2
def baseEnd_1165747 : Nat := 598588532536955743201333

theorem tailTrace_1165747 : CollatzResearch.WordTrace tailWord_1165747 prefixEnd_1165747 598588532536955743201333 := by
  unfold tailWord_1165747
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518286107705187582047495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28345524071803458388031663 42518286107705187582047495)
  ·
    refine ⟨63777429161557781373071243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42518286107705187582047495 63777429161557781373071243)
    ·
      refine ⟨95666143742336672059606865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63777429161557781373071243 95666143742336672059606865)
      ·
        refine ⟨71749607806752504044705149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95666143742336672059606865 71749607806752504044705149)
        ·
          refine ⟨26906102927532189016764431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71749607806752504044705149 26906102927532189016764431)
          ·
            refine ⟨40359154391298283525146647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26906102927532189016764431 40359154391298283525146647)
            ·
              refine ⟨60538731586947425287719971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40359154391298283525146647 60538731586947425287719971)
              ·
                refine ⟨90808097380421137931579957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60538731586947425287719971 90808097380421137931579957)
                ·
                  refine ⟨8513259129414481681085621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90808097380421137931579957 8513259129414481681085621)
                  ·
                    refine ⟨798118043382607657601777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8513259129414481681085621 798118043382607657601777)
                    ·
                      refine ⟨598588532536955743201333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798118043382607657601777 598588532536955743201333)
                      ·
                        rfl

theorem cell23_1165747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5, 2].length) (baseStart_1165747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165747 prefixEnd_1165747 := by exact prefixLift 1165747
  have htrace : WordTrace (prefixWord ++ tailWord_1165747) baseStart_1165747 baseEnd_1165747 := by
    simpa [prefixWord, tailWord_1165747, baseEnd_1165747] using wordTrace_append hprefix tailTrace_1165747
  have hstable : (prefixWord ++ tailWord_1165747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165747).length < 2 ^ (prefixWord ++ tailWord_1165747).sum := by decide
  have hdescent : baseEnd_1165747 < baseStart_1165747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165757 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1165757 : Nat := 118140960795 + 1165757 * 2 ^ 59
def prefixEnd_1165757 : Nat := 4983230072969 + 3 ^ 40 * 1165757 * 2
def baseEnd_1165757 : Nat := 199531222447833568025429

theorem tailTrace_1165757 : CollatzResearch.WordTrace tailWord_1165757 prefixEnd_1165757 199531222447833568025429 := by
  unfold tailWord_1165757
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518650837668959289911525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28345767225112639526607683 42518650837668959289911525)
  ·
    refine ⟨7972247032062929866858411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42518650837668959289911525 7972247032062929866858411)
    ·
      refine ⟨11958370548094394800287617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972247032062929866858411 11958370548094394800287617)
      ·
        refine ⟨8968777911070796100215713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11958370548094394800287617 8968777911070796100215713)
        ·
          refine ⟨6726583433303097075161785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8968777911070796100215713 6726583433303097075161785)
          ·
            refine ⟨5044937574977322806371339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6726583433303097075161785 5044937574977322806371339)
            ·
              refine ⟨7567406362465984209557009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044937574977322806371339 7567406362465984209557009)
              ·
                refine ⟨5675554771849488157167757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567406362465984209557009 5675554771849488157167757)
                ·
                  refine ⟨2128333039443558058937909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5675554771849488157167757 2128333039443558058937909)
                  ·
                    refine ⟨199531222447833568025429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2128333039443558058937909 199531222447833568025429)
                    ·
                      rfl

theorem cell23_1165757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1165757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165757 prefixEnd_1165757 := by exact prefixLift 1165757
  have htrace : WordTrace (prefixWord ++ tailWord_1165757) baseStart_1165757 baseEnd_1165757 := by
    simpa [prefixWord, tailWord_1165757, baseEnd_1165757] using wordTrace_append hprefix tailTrace_1165757
  have hstable : (prefixWord ++ tailWord_1165757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165757).length < 2 ^ (prefixWord ++ tailWord_1165757).sum := by decide
  have hdescent : baseEnd_1165757 < baseStart_1165757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165781 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1165781 : Nat := 118140960795 + 1165781 * 2 ^ 59
def prefixEnd_1165781 : Nat := 4983230072969 + 3 ^ 40 * 1165781 * 2
def baseEnd_1165781 : Nat := 598605990879208610176177

theorem tailTrace_1165781 : CollatzResearch.WordTrace tailWord_1165781 prefixEnd_1165781 598605990879208610176177 := by
  unfold tailWord_1165781
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519526189582011388785197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28346350793054674259190131 42519526189582011388785197)
  ·
    refine ⟨15944822321093254270794449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42519526189582011388785197 15944822321093254270794449)
    ·
      refine ⟨11958616740819940703095837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15944822321093254270794449 11958616740819940703095837)
      ·
        refine ⟨4484481277807477763660939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11958616740819940703095837 4484481277807477763660939)
        ·
          refine ⟨6726721916711216645491409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484481277807477763660939 6726721916711216645491409)
          ·
            refine ⟨5045041437533412484118557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6726721916711216645491409 5045041437533412484118557)
            ·
              refine ⟨1891890539075029681544459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5045041437533412484118557 1891890539075029681544459)
              ·
                refine ⟨2837835808612544522316689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891890539075029681544459 2837835808612544522316689)
                ·
                  refine ⟨2128376856459408391737517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2837835808612544522316689 2128376856459408391737517)
                  ·
                    refine ⟨798141321172278146901569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128376856459408391737517 798141321172278146901569)
                    ·
                      refine ⟨598605990879208610176177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798141321172278146901569 598605990879208610176177)
                      ·
                        rfl

theorem cell23_1165781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1165781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165781 prefixEnd_1165781 := by exact prefixLift 1165781
  have htrace : WordTrace (prefixWord ++ tailWord_1165781) baseStart_1165781 baseEnd_1165781 := by
    simpa [prefixWord, tailWord_1165781, baseEnd_1165781] using wordTrace_append hprefix tailTrace_1165781
  have hstable : (prefixWord ++ tailWord_1165781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165781).length < 2 ^ (prefixWord ++ tailWord_1165781).sum := by decide
  have hdescent : baseEnd_1165781 < baseStart_1165781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165791 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 1, 5]
def baseStart_1165791 : Nat := 118140960795 + 1165791 * 2 ^ 59
def prefixEnd_1165791 : Nat := 4983230072969 + 3 ^ 40 * 1165791 * 2
def baseEnd_1165791 : Nat := 199537041895251190350377

theorem tailTrace_1165791 : CollatzResearch.WordTrace tailWord_1165791 prefixEnd_1165791 199537041895251190350377 := by
  unfold tailWord_1165791
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519890919545783096649227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28346593946363855397766151 42519890919545783096649227)
  ·
    refine ⟨63779836379318674644973841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42519890919545783096649227 63779836379318674644973841)
    ·
      refine ⟨47834877284489005983730381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63779836379318674644973841 47834877284489005983730381)
      ·
        refine ⟨17938078981683377243898893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47834877284489005983730381 17938078981683377243898893)
        ·
          refine ⟨6726779618131266466462085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17938078981683377243898893 6726779618131266466462085)
          ·
            refine ⟨1261271178399612462461641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6726779618131266466462085 1261271178399612462461641)
            ·
              refine ⟨945953383799709346846231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261271178399612462461641 945953383799709346846231)
              ·
                refine ⟨1418930075699564020269347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945953383799709346846231 1418930075699564020269347)
                ·
                  refine ⟨2128395113549346030404021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418930075699564020269347 2128395113549346030404021)
                  ·
                    refine ⟨199537041895251190350377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2128395113549346030404021 199537041895251190350377)
                    ·
                      rfl

theorem cell23_1165791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_1165791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165791 prefixEnd_1165791 := by exact prefixLift 1165791
  have htrace : WordTrace (prefixWord ++ tailWord_1165791) baseStart_1165791 baseEnd_1165791 := by
    simpa [prefixWord, tailWord_1165791, baseEnd_1165791] using wordTrace_append hprefix tailTrace_1165791
  have hstable : (prefixWord ++ tailWord_1165791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165791).length < 2 ^ (prefixWord ++ tailWord_1165791).sum := by decide
  have hdescent : baseEnd_1165791 < baseStart_1165791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165811 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 3, 2, 2]
def baseStart_1165811 : Nat := 118140960795 + 1165811 * 2 ^ 59
def prefixEnd_1165811 : Nat := 4983230072969 + 3 ^ 40 * 1165811 * 2
def baseEnd_1165811 : Nat := 598621395298843492801039

theorem tailTrace_1165811 : CollatzResearch.WordTrace tailWord_1165811 prefixEnd_1165811 598621395298843492801039 := by
  unfold tailWord_1165811
  simp only [CollatzResearch.WordTrace]
  refine ⟨42520620379473326512377287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28347080252982217674918191 42520620379473326512377287)
  ·
    refine ⟨63780930569209989768565931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42520620379473326512377287 63780930569209989768565931)
    ·
      refine ⟨95671395853814984652848897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63780930569209989768565931 95671395853814984652848897)
      ·
        refine ⟨71753546890361238489636673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95671395853814984652848897 71753546890361238489636673)
        ·
          refine ⟨53815160167770928867227505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71753546890361238489636673 53815160167770928867227505)
          ·
            refine ⟨40361370125828196650420629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53815160167770928867227505 40361370125828196650420629)
            ·
              refine ⟨1891939224648196717988467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40361370125828196650420629 1891939224648196717988467)
              ·
                refine ⟨2837908836972295076982701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891939224648196717988467 2837908836972295076982701)
                ·
                  refine ⟨1064215813864610653868513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2837908836972295076982701 1064215813864610653868513)
                  ·
                    refine ⟨798161860398457990401385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1064215813864610653868513 798161860398457990401385)
                    ·
                      refine ⟨598621395298843492801039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798161860398457990401385 598621395298843492801039)
                      ·
                        rfl

theorem cell23_1165811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2, 2].length) (baseStart_1165811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165811 prefixEnd_1165811 := by exact prefixLift 1165811
  have htrace : WordTrace (prefixWord ++ tailWord_1165811) baseStart_1165811 baseEnd_1165811 := by
    simpa [prefixWord, tailWord_1165811, baseEnd_1165811] using wordTrace_append hprefix tailTrace_1165811
  have hstable : (prefixWord ++ tailWord_1165811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165811).length < 2 ^ (prefixWord ++ tailWord_1165811).sum := by decide
  have hdescent : baseEnd_1165811 < baseStart_1165811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165814 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1165814 : Nat := 118140960795 + 1165814 * 2 ^ 59
def prefixEnd_1165814 : Nat := 4983230072969 + 3 ^ 40 * 1165814 * 2
def baseEnd_1165814 : Nat := 598622935740806981063525

theorem tailTrace_1165814 : CollatzResearch.WordTrace tailWord_1165814 prefixEnd_1165814 598622935740806981063525 := by
  unfold tailWord_1165814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657545612403903626546031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28347153198974972016490997 2657545612403903626546031)
  ·
    refine ⟨3986318418605855439819047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2657545612403903626546031 3986318418605855439819047)
    ·
      refine ⟨5979477627908783159728571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3986318418605855439819047 5979477627908783159728571)
      ·
        refine ⟨8969216441863174739592857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979477627908783159728571 8969216441863174739592857)
        ·
          refine ⟨6726912331397381054694643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969216441863174739592857 6726912331397381054694643)
          ·
            refine ⟨10090368497096071582041965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726912331397381054694643 10090368497096071582041965)
            ·
              refine ⟨3783888186411026843265737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10090368497096071582041965 3783888186411026843265737)
              ·
                refine ⟨2837916139808270132449303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3783888186411026843265737 2837916139808270132449303)
                ·
                  refine ⟨4256874209712405198673955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837916139808270132449303 4256874209712405198673955)
                  ·
                    refine ⟨6385311314568607798010933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256874209712405198673955 6385311314568607798010933)
                    ·
                      refine ⟨598622935740806981063525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6385311314568607798010933 598622935740806981063525)
                      ·
                        rfl

theorem cell23_1165814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1165814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165814 prefixEnd_1165814 := by exact prefixLift 1165814
  have htrace : WordTrace (prefixWord ++ tailWord_1165814) baseStart_1165814 baseEnd_1165814 := by
    simpa [prefixWord, tailWord_1165814, baseEnd_1165814] using wordTrace_append hprefix tailTrace_1165814
  have hstable : (prefixWord ++ tailWord_1165814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165814).length < 2 ^ (prefixWord ++ tailWord_1165814).sum := by decide
  have hdescent : baseEnd_1165814 < baseStart_1165814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165821 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_1165821 : Nat := 118140960795 + 1165821 * 2 ^ 59
def prefixEnd_1165821 : Nat := 4983230072969 + 3 ^ 40 * 1165821 * 2
def baseEnd_1165821 : Nat := 199542176701796151225331

theorem tailTrace_1165821 : CollatzResearch.WordTrace tailWord_1165821 prefixEnd_1165821 199542176701796151225331 := by
  unfold tailWord_1165821
  simp only [CollatzResearch.WordTrace]
  refine ⟨42520985109437098220241317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28347323406291398813494211 42520985109437098220241317)
  ·
    refine ⟨7972684708019455916295247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42520985109437098220241317 7972684708019455916295247)
    ·
      refine ⟨11959027062029183874442871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972684708019455916295247 11959027062029183874442871)
      ·
        refine ⟨17938540593043775811664307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11959027062029183874442871 17938540593043775811664307)
        ·
          refine ⟨26907810889565663717496461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17938540593043775811664307 26907810889565663717496461)
          ·
            refine ⟨10090429083587123894061173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26907810889565663717496461 10090429083587123894061173)
            ·
              refine ⟨945977726586292865068235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10090429083587123894061173 945977726586292865068235)
              ·
                refine ⟨1418966589879439297602353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945977726586292865068235 1418966589879439297602353)
                ·
                  refine ⟨1064224942409579473201765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1418966589879439297602353 1064224942409579473201765)
                  ·
                    refine ⟨199542176701796151225331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1064224942409579473201765 199542176701796151225331)
                    ·
                      rfl

theorem cell23_1165821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_1165821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165821 prefixEnd_1165821 := by exact prefixLift 1165821
  have htrace : WordTrace (prefixWord ++ tailWord_1165821) baseStart_1165821 baseEnd_1165821 := by
    simpa [prefixWord, tailWord_1165821, baseEnd_1165821] using wordTrace_append hprefix tailTrace_1165821
  have hstable : (prefixWord ++ tailWord_1165821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165821).length < 2 ^ (prefixWord ++ tailWord_1165821).sum := by decide
  have hdescent : baseEnd_1165821 < baseStart_1165821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165828 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1165828 : Nat := 118140960795 + 1165828 * 2 ^ 59
def prefixEnd_1165828 : Nat := 4983230072969 + 3 ^ 40 * 1165828 * 2
def baseEnd_1165828 : Nat := 598630124469969926288461

theorem tailTrace_1165828 : CollatzResearch.WordTrace tailWord_1165828 prefixEnd_1165828 598630124469969926288461 := by
  unfold tailWord_1165828
  simp only [CollatzResearch.WordTrace]
  refine ⟨21260620210205869207873069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28347493613607825610497425 21260620210205869207873069)
  ·
    refine ⟨7972732578827200952952401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21260620210205869207873069 7972732578827200952952401)
    ·
      refine ⟨5979549434120400714714301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7972732578827200952952401 5979549434120400714714301)
      ·
        refine ⟨2242331037795150268017863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5979549434120400714714301 2242331037795150268017863)
        ·
          refine ⟨3363496556692725402026795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242331037795150268017863 3363496556692725402026795)
          ·
            refine ⟨5045244835039088103040193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363496556692725402026795 5045244835039088103040193)
            ·
              refine ⟨3783933626279316077280145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5045244835039088103040193 3783933626279316077280145)
              ·
                refine ⟨2837950219709487057960109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3783933626279316077280145 2837950219709487057960109)
                ·
                  refine ⟨1064231332391057646735041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2837950219709487057960109 1064231332391057646735041)
                  ·
                    refine ⟨798173499293293235051281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1064231332391057646735041 798173499293293235051281)
                    ·
                      refine ⟨598630124469969926288461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798173499293293235051281 598630124469969926288461)
                      ·
                        rfl

theorem cell23_1165828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1165828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165828 prefixEnd_1165828 := by exact prefixLift 1165828
  have htrace : WordTrace (prefixWord ++ tailWord_1165828) baseStart_1165828 baseEnd_1165828 := by
    simpa [prefixWord, tailWord_1165828, baseEnd_1165828] using wordTrace_append hprefix tailTrace_1165828
  have hstable : (prefixWord ++ tailWord_1165828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165828).length < 2 ^ (prefixWord ++ tailWord_1165828).sum := by decide
  have hdescent : baseEnd_1165828 < baseStart_1165828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165857 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1165857 : Nat := 118140960795 + 1165857 * 2 ^ 59
def prefixEnd_1165857 : Nat := 4983230072969 + 3 ^ 40 * 1165857 * 2
def baseEnd_1165857 : Nat := 598645015408950312825827

theorem tailTrace_1165857 : CollatzResearch.WordTrace tailWord_1165857 prefixEnd_1165857 598645015408950312825827 := by
  unfold tailWord_1165857
  simp only [CollatzResearch.WordTrace]
  refine ⟨42522298137306676368551825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28348198758204450912367883 42522298137306676368551825)
  ·
    refine ⟨31891723602980007276413869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42522298137306676368551825 31891723602980007276413869)
    ·
      refine ⟨11959396351117502728655201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31891723602980007276413869 11959396351117502728655201)
      ·
        refine ⟨8969547263338127046491401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11959396351117502728655201 8969547263338127046491401)
        ·
          refine ⟨6727160447503595284868551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969547263338127046491401 6727160447503595284868551)
          ·
            refine ⟨10090740671255392927302827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727160447503595284868551 10090740671255392927302827)
            ·
              refine ⟨15136111006883089390954241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090740671255392927302827 15136111006883089390954241)
              ·
                refine ⟨11352083255162317043215681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15136111006883089390954241 11352083255162317043215681)
                ·
                  refine ⟨8514062441371737782411761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11352083255162317043215681 8514062441371737782411761)
                  ·
                    refine ⟨6385546831028803336808821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8514062441371737782411761 6385546831028803336808821)
                    ·
                      refine ⟨598645015408950312825827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6385546831028803336808821 598645015408950312825827)
                      ·
                        rfl

theorem cell23_1165857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1165857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165857 prefixEnd_1165857 := by exact prefixLift 1165857
  have htrace : WordTrace (prefixWord ++ tailWord_1165857) baseStart_1165857 baseEnd_1165857 := by
    simpa [prefixWord, tailWord_1165857, baseEnd_1165857] using wordTrace_append hprefix tailTrace_1165857
  have hstable : (prefixWord ++ tailWord_1165857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165857).length < 2 ^ (prefixWord ++ tailWord_1165857).sum := by decide
  have hdescent : baseEnd_1165857 < baseStart_1165857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165877 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1165877 : Nat := 118140960795 + 1165877 * 2 ^ 59
def prefixEnd_1165877 : Nat := 4983230072969 + 3 ^ 40 * 1165877 * 2
def baseEnd_1165877 : Nat := 199551761674013411525245

theorem tailTrace_1165877 : CollatzResearch.WordTrace tailWord_1165877 prefixEnd_1165877 199551761674013411525245 := by
  unfold tailWord_1165877
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523027597234219784279885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28348685064822813189519923 42523027597234219784279885)
  ·
    refine ⟨15946135348962832419104957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42523027597234219784279885 15946135348962832419104957)
    ·
      refine ⟨5979800755861062157164359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15946135348962832419104957 5979800755861062157164359)
      ·
        refine ⟨8969701133791593235746539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979800755861062157164359 8969701133791593235746539)
        ·
          refine ⟨13454551700687389853619809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8969701133791593235746539 13454551700687389853619809)
          ·
            refine ⟨10090913775515542390214857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13454551700687389853619809 10090913775515542390214857)
            ·
              refine ⟨7568185331636656792661143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10090913775515542390214857 7568185331636656792661143)
              ·
                refine ⟨11352277997454985188991715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568185331636656792661143 11352277997454985188991715)
                ·
                  refine ⟨17028416996182477783487573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11352277997454985188991715 17028416996182477783487573)
                  ·
                    refine ⟨199551761674013411525245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17028416996182477783487573 199551761674013411525245)
                    ·
                      rfl

theorem cell23_1165877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1165877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165877 prefixEnd_1165877 := by exact prefixLift 1165877
  have htrace : WordTrace (prefixWord ++ tailWord_1165877) baseStart_1165877 baseEnd_1165877 := by
    simpa [prefixWord, tailWord_1165877, baseEnd_1165877] using wordTrace_append hprefix tailTrace_1165877
  have hstable : (prefixWord ++ tailWord_1165877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165877).length < 2 ^ (prefixWord ++ tailWord_1165877).sum := by decide
  have hdescent : baseEnd_1165877 < baseStart_1165877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165887 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_1165887 : Nat := 118140960795 + 1165887 * 2 ^ 59
def prefixEnd_1165887 : Nat := 4983230072969 + 3 ^ 40 * 1165887 * 2
def baseEnd_1165887 : Nat := 598660419828585195450689

theorem tailTrace_1165887 : CollatzResearch.WordTrace tailWord_1165887 prefixEnd_1165887 598660419828585195450689 := by
  unfold tailWord_1165887
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523392327197991492143915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28348928218131994328095943 42523392327197991492143915)
  ·
    refine ⟨63785088490796987238215873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42523392327197991492143915 63785088490796987238215873)
    ·
      refine ⟨47838816368097740428661905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63785088490796987238215873 47838816368097740428661905)
      ·
        refine ⟨35879112276073305321496429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47838816368097740428661905 35879112276073305321496429)
        ·
          refine ⟨13454667103527489495561161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35879112276073305321496429 13454667103527489495561161)
          ·
            refine ⟨10091000327645617121670871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13454667103527489495561161 10091000327645617121670871)
            ·
              refine ⟨15136500491468425682506307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091000327645617121670871 15136500491468425682506307)
              ·
                refine ⟨22704750737202638523759461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15136500491468425682506307 22704750737202638523759461)
                ·
                  refine ⟨4257140763225494723204899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22704750737202638523759461 4257140763225494723204899)
                  ·
                    refine ⟨6385711144838242084807349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257140763225494723204899 6385711144838242084807349)
                    ·
                      refine ⟨598660419828585195450689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6385711144838242084807349 598660419828585195450689)
                      ·
                        rfl

theorem cell23_1165887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_1165887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165887 prefixEnd_1165887 := by exact prefixLift 1165887
  have htrace : WordTrace (prefixWord ++ tailWord_1165887) baseStart_1165887 baseEnd_1165887 := by
    simpa [prefixWord, tailWord_1165887, baseEnd_1165887] using wordTrace_append hprefix tailTrace_1165887
  have hstable : (prefixWord ++ tailWord_1165887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165887).length < 2 ^ (prefixWord ++ tailWord_1165887).sum := by decide
  have hdescent : baseEnd_1165887 < baseStart_1165887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165897 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_1165897 : Nat := 118140960795 + 1165897 * 2 ^ 59
def prefixEnd_1165897 : Nat := 4983230072969 + 3 ^ 40 * 1165897 * 2
def baseEnd_1165897 : Nat := 598665554635130156325643

theorem tailTrace_1165897 : CollatzResearch.WordTrace tailWord_1165897 prefixEnd_1165897 598665554635130156325643 := by
  unfold tailWord_1165897
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523757057161763200007945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28349171371441175466671963 42523757057161763200007945)
  ·
    refine ⟨31892817792871322400005959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42523757057161763200007945 31892817792871322400005959)
    ·
      refine ⟨47839226689306983600008939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31892817792871322400005959 47839226689306983600008939)
      ·
        refine ⟨71758840033960475400013409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47839226689306983600008939 71758840033960475400013409)
        ·
          refine ⟨53819130025470356550010057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71758840033960475400013409 53819130025470356550010057)
          ·
            refine ⟨40364347519102767412507543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53819130025470356550010057 40364347519102767412507543)
            ·
              refine ⟨60546521278654151118761315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40364347519102767412507543 60546521278654151118761315)
              ·
                refine ⟨90819781917981226678141973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60546521278654151118761315 90819781917981226678141973)
                ·
                  refine ⟨4257177277405370000537905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90819781917981226678141973 4257177277405370000537905)
                  ·
                    refine ⟨3192882958054027500403429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257177277405370000537905 3192882958054027500403429)
                    ·
                      refine ⟨598665554635130156325643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3192882958054027500403429 598665554635130156325643)
                      ·
                        rfl

theorem cell23_1165897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_1165897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165897 prefixEnd_1165897 := by exact prefixLift 1165897
  have htrace : WordTrace (prefixWord ++ tailWord_1165897) baseStart_1165897 baseEnd_1165897 := by
    simpa [prefixWord, tailWord_1165897, baseEnd_1165897] using wordTrace_append hprefix tailTrace_1165897
  have hstable : (prefixWord ++ tailWord_1165897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165897).length < 2 ^ (prefixWord ++ tailWord_1165897).sum := by decide
  have hdescent : baseEnd_1165897 < baseStart_1165897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165927 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1165927 : Nat := 118140960795 + 1165927 * 2 ^ 59
def prefixEnd_1165927 : Nat := 4983230072969 + 3 ^ 40 * 1165927 * 2
def baseEnd_1165927 : Nat := 598680959054765038950505

theorem tailTrace_1165927 : CollatzResearch.WordTrace tailWord_1165927 prefixEnd_1165927 598680959054765038950505 := by
  unfold tailWord_1165927
  simp only [CollatzResearch.WordTrace]
  refine ⟨42524851247053078323600035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28349900831368718882400023 42524851247053078323600035)
  ·
    refine ⟨63787276870579617485400053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42524851247053078323600035 63787276870579617485400053)
    ·
      refine ⟨5980057206616839139256255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63787276870579617485400053 5980057206616839139256255)
      ·
        refine ⟨8970085809925258708884383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980057206616839139256255 8970085809925258708884383)
        ·
          refine ⟨13455128714887888063326575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8970085809925258708884383 13455128714887888063326575)
          ·
            refine ⟨20182693072331832094989863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13455128714887888063326575 20182693072331832094989863)
            ·
              refine ⟨30274039608497748142484795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20182693072331832094989863 30274039608497748142484795)
              ·
                refine ⟨45411059412746622213727193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30274039608497748142484795 45411059412746622213727193)
                ·
                  refine ⟨34058294559559966660295395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45411059412746622213727193 34058294559559966660295395)
                  ·
                    refine ⟨51087441839339949990443093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34058294559559966660295395 51087441839339949990443093)
                    ·
                      refine ⟨598680959054765038950505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 51087441839339949990443093 598680959054765038950505)
                      ·
                        rfl

theorem cell23_1165927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1165927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165927 prefixEnd_1165927 := by exact prefixLift 1165927
  have htrace : WordTrace (prefixWord ++ tailWord_1165927) baseStart_1165927 baseEnd_1165927 := by
    simpa [prefixWord, tailWord_1165927, baseEnd_1165927] using wordTrace_append hprefix tailTrace_1165927
  have hstable : (prefixWord ++ tailWord_1165927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165927).length < 2 ^ (prefixWord ++ tailWord_1165927).sum := by decide
  have hdescent : baseEnd_1165927 < baseStart_1165927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165941 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 7]
def baseStart_1165941 : Nat := 118140960795 + 1165941 * 2 ^ 59
def prefixEnd_1165941 : Nat := 4983230072969 + 3 ^ 40 * 1165941 * 2
def baseEnd_1165941 : Nat := 66520905309325331575049

theorem tailTrace_1165941 : CollatzResearch.WordTrace tailWord_1165941 prefixEnd_1165941 66520905309325331575049 := by
  unfold tailWord_1165941
  simp only [CollatzResearch.WordTrace]
  refine ⟨42525361869002358714609677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28350241246001572476406451 42525361869002358714609677)
  ·
    refine ⟨15947010700875884517978629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42525361869002358714609677 15947010700875884517978629)
    ·
      refine ⟨2990064506414228347120993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15947010700875884517978629 2990064506414228347120993)
      ·
        refine ⟨2242548379810671260340745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2990064506414228347120993 2242548379810671260340745)
        ·
          refine ⟨1681911284858003445255559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2242548379810671260340745 1681911284858003445255559)
          ·
            refine ⟨2522866927287005167883339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681911284858003445255559 2522866927287005167883339)
            ·
              refine ⟨3784300390930507751825009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2522866927287005167883339 3784300390930507751825009)
              ·
                refine ⟨2838225293197880813868757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784300390930507751825009 2838225293197880813868757)
                ·
                  refine ⟨66520905309325331575049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2838225293197880813868757 66520905309325331575049)
                  ·
                    rfl

theorem cell23_1165941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_1165941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165941 prefixEnd_1165941 := by exact prefixLift 1165941
  have htrace : WordTrace (prefixWord ++ tailWord_1165941) baseStart_1165941 baseEnd_1165941 := by
    simpa [prefixWord, tailWord_1165941, baseEnd_1165941] using wordTrace_append hprefix tailTrace_1165941
  have hstable : (prefixWord ++ tailWord_1165941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165941).length < 2 ^ (prefixWord ++ tailWord_1165941).sum := by decide
  have hdescent : baseEnd_1165941 < baseStart_1165941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165947 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_1165947 : Nat := 118140960795 + 1165947 * 2 ^ 59
def prefixEnd_1165947 : Nat := 4983230072969 + 3 ^ 40 * 1165947 * 2
def baseEnd_1165947 : Nat := 598691228667854960700413

theorem tailTrace_1165947 : CollatzResearch.WordTrace tailWord_1165947 prefixEnd_1165947 598691228667854960700413 := by
  unfold tailWord_1165947
  simp only [CollatzResearch.WordTrace]
  refine ⟨42525580706980621739328095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28350387137987081159552063 42525580706980621739328095)
  ·
    refine ⟨63788371060470932608992143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42525580706980621739328095 63788371060470932608992143)
    ·
      refine ⟨95682556590706398913488215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63788371060470932608992143 95682556590706398913488215)
      ·
        refine ⟨143523834886059598370232323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95682556590706398913488215 143523834886059598370232323)
        ·
          refine ⟨215285752329089397555348485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143523834886059598370232323 215285752329089397555348485)
          ·
            refine ⟨40366078561704262041627841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215285752329089397555348485 40366078561704262041627841)
            ·
              refine ⟨30274558921278196531220881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40366078561704262041627841 30274558921278196531220881)
              ·
                refine ⟨22705919190958647398415661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30274558921278196531220881 22705919190958647398415661)
                ·
                  refine ⟨8514719696609492774405873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22705919190958647398415661 8514719696609492774405873)
                  ·
                    refine ⟨6386039772457119580804405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8514719696609492774405873 6386039772457119580804405)
                    ·
                      refine ⟨598691228667854960700413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6386039772457119580804405 598691228667854960700413)
                      ·
                        rfl

theorem cell23_1165947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_1165947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1165947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1165947 prefixEnd_1165947 := by exact prefixLift 1165947
  have htrace : WordTrace (prefixWord ++ tailWord_1165947) baseStart_1165947 baseEnd_1165947 := by
    simpa [prefixWord, tailWord_1165947, baseEnd_1165947] using wordTrace_append hprefix tailTrace_1165947
  have hstable : (prefixWord ++ tailWord_1165947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165947).length < 2 ^ (prefixWord ++ tailWord_1165947).sum := by decide
  have hdescent : baseEnd_1165947 < baseStart_1165947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166014 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_1166014 : Nat := 118140960795 + 1166014 * 2 ^ 59
def prefixEnd_1166014 : Nat := 4983230072969 + 3 ^ 40 * 1166014 * 2
def baseEnd_1166014 : Nat := 66525070207967355395845

theorem tailTrace_1166014 : CollatzResearch.WordTrace tailWord_1166014 prefixEnd_1166014 66525070207967355395845 := by
  unfold tailWord_1166014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316003049717236522752137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28352016265158594788011397 5316003049717236522752137)
  ·
    refine ⟨3987002287287927392064103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5316003049717236522752137 3987002287287927392064103)
    ·
      refine ⟨5980503430931891088096155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987002287287927392064103 5980503430931891088096155)
      ·
        refine ⟨8970755146397836632144233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980503430931891088096155 8970755146397836632144233)
        ·
          refine ⟨6728066359798377474108175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8970755146397836632144233 6728066359798377474108175)
          ·
            refine ⟨10092099539697566211162263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728066359798377474108175 10092099539697566211162263)
            ·
              refine ⟨15138149309546349316743395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10092099539697566211162263 15138149309546349316743395)
              ·
                refine ⟨22707223964319523975115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15138149309546349316743395 22707223964319523975115093)
                ·
                  refine ⟨66525070207967355395845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22707223964319523975115093 66525070207967355395845)
                  ·
                    rfl

theorem cell23_1166014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_1166014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166014 prefixEnd_1166014 := by exact prefixLift 1166014
  have htrace : WordTrace (prefixWord ++ tailWord_1166014) baseStart_1166014 baseEnd_1166014 := by
    simpa [prefixWord, tailWord_1166014, baseEnd_1166014] using wordTrace_append hprefix tailTrace_1166014
  have hstable : (prefixWord ++ tailWord_1166014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166014).length < 2 ^ (prefixWord ++ tailWord_1166014).sum := by decide
  have hdescent : baseEnd_1166014 < baseStart_1166014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166028 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1166028 : Nat := 118140960795 + 1166028 * 2 ^ 59
def prefixEnd_1166028 : Nat := 4983230072969 + 3 ^ 40 * 1166028 * 2
def baseEnd_1166028 : Nat := 598732820600869143787541

theorem tailTrace_1166028 : CollatzResearch.WordTrace tailWord_1166028 prefixEnd_1166028 598732820600869143787541 := by
  unfold tailWord_1166028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21264267509843586286513369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28352356679791448382017825 21264267509843586286513369)
  ·
    refine ⟨15948200632382689714885027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21264267509843586286513369 15948200632382689714885027)
    ·
      refine ⟨23922300948574034572327541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15948200632382689714885027 23922300948574034572327541)
      ·
        refine ⟨2242715713928815741155707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23922300948574034572327541 2242715713928815741155707)
        ·
          refine ⟨3364073570893223611733561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242715713928815741155707 3364073570893223611733561)
          ·
            refine ⟨2523055178169917708800171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364073570893223611733561 2523055178169917708800171)
            ·
              refine ⟨3784582767254876563200257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523055178169917708800171 3784582767254876563200257)
              ·
                refine ⟨2838437075441157422400193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784582767254876563200257 2838437075441157422400193)
                ·
                  refine ⟨2128827806580868066800145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838437075441157422400193 2128827806580868066800145)
                  ·
                    refine ⟨1596620854935651050100109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128827806580868066800145 1596620854935651050100109)
                    ·
                      refine ⟨598732820600869143787541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1596620854935651050100109 598732820600869143787541)
                      ·
                        rfl

theorem cell23_1166028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1166028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166028 prefixEnd_1166028 := by exact prefixLift 1166028
  have htrace : WordTrace (prefixWord ++ tailWord_1166028) baseStart_1166028 baseEnd_1166028 := by
    simpa [prefixWord, tailWord_1166028, baseEnd_1166028] using wordTrace_append hprefix tailTrace_1166028
  have hstable : (prefixWord ++ tailWord_1166028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166028).length < 2 ^ (prefixWord ++ tailWord_1166028).sum := by decide
  have hdescent : baseEnd_1166028 < baseStart_1166028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
