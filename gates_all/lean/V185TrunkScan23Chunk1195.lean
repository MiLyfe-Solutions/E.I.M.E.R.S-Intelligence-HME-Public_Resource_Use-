import V185TrunkScan23Chunk1194

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7080658 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_7080658 : Nat := 118140960795 + 7080658 * 2 ^ 59
def prefixEnd_7080658 : Nat := 4983230072969 + 3 ^ 40 * 7080658 * 2
def baseEnd_7080658 : Nat := 403975656011451458523517

theorem tailTrace_7080658 : CollatzResearch.WordTrace tailWord_7080658 prefixEnd_7080658 403975656011451458523517 := by
  unfold tailWord_7080658
  simp only [CollatzResearch.WordTrace]
  refine ⟨64563203395498205238950657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172168542387995213970535085 64563203395498205238950657)
  ·
    refine ⟨48422402546623653929212993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64563203395498205238950657 48422402546623653929212993)
    ·
      refine ⟨36316801909967740446909745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48422402546623653929212993 36316801909967740446909745)
      ·
        refine ⟨27237601432475805335182309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36316801909967740446909745 27237601432475805335182309)
        ·
          refine ⟨5107050268589213500346683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27237601432475805335182309 5107050268589213500346683)
          ·
            refine ⟨7660575402883820250520025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107050268589213500346683 7660575402883820250520025)
            ·
              refine ⟨5745431552162865187890019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7660575402883820250520025 5745431552162865187890019)
              ·
                refine ⟨8618147328244297781835029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745431552162865187890019 8618147328244297781835029)
                ·
                  refine ⟨403975656011451458523517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8618147328244297781835029 403975656011451458523517)
                  ·
                    rfl

theorem cell23_7080658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_7080658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080658 prefixEnd_7080658 := by exact prefixLift 7080658
  have htrace : WordTrace (prefixWord ++ tailWord_7080658) baseStart_7080658 baseEnd_7080658 := by
    simpa [prefixWord, tailWord_7080658, baseEnd_7080658] using wordTrace_append hprefix tailTrace_7080658
  have hstable : (prefixWord ++ tailWord_7080658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080658).length < 2 ^ (prefixWord ++ tailWord_7080658).sum := by decide
  have hdescent : baseEnd_7080658 < baseStart_7080658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080687 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_7080687 : Nat := 118140960795 + 7080687 * 2 ^ 59
def prefixEnd_7080687 : Nat := 4983230072969 + 3 ^ 40 * 7080687 * 2
def baseEnd_7080687 : Nat := 3635795795042043513249019

theorem tailTrace_7080687 : CollatzResearch.WordTrace tailWord_7080687 prefixEnd_7080687 3635795795042043513249019 := by
  unfold tailWord_7080687
  simp only [CollatzResearch.WordTrace]
  refine ⟨258253871298887758908608315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172169247532591839272405543 258253871298887758908608315)
  ·
    refine ⟨387380806948331638362912473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258253871298887758908608315 387380806948331638362912473)
    ·
      refine ⟨290535605211248728772184355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387380806948331638362912473 290535605211248728772184355)
      ·
        refine ⟨435803407816873093158276533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290535605211248728772184355 435803407816873093158276533)
        ·
          refine ⟨40856569482831852483588425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435803407816873093158276533 40856569482831852483588425)
          ·
            refine ⟨30642427112123889362691319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40856569482831852483588425 30642427112123889362691319)
            ·
              refine ⟨45963640668185834044036979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30642427112123889362691319 45963640668185834044036979)
              ·
                refine ⟨68945461002278751066055469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45963640668185834044036979 68945461002278751066055469)
                ·
                  refine ⟨25854547875854531649770801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68945461002278751066055469 25854547875854531649770801)
                  ·
                    refine ⟨19390910906890898737328101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25854547875854531649770801 19390910906890898737328101)
                    ·
                      refine ⟨3635795795042043513249019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19390910906890898737328101 3635795795042043513249019)
                      ·
                        rfl

theorem cell23_7080687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_7080687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080687 prefixEnd_7080687 := by exact prefixLift 7080687
  have htrace : WordTrace (prefixWord ++ tailWord_7080687) baseStart_7080687 baseEnd_7080687 := by
    simpa [prefixWord, tailWord_7080687, baseEnd_7080687] using wordTrace_append hprefix tailTrace_7080687
  have hstable : (prefixWord ++ tailWord_7080687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080687).length < 2 ^ (prefixWord ++ tailWord_7080687).sum := by decide
  have hdescent : baseEnd_7080687 < baseStart_7080687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080702 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_7080702 : Nat := 118140960795 + 7080702 * 2 ^ 59
def prefixEnd_7080702 : Nat := 4983230072969 + 3 ^ 40 * 7080702 * 2
def baseEnd_7080702 : Nat := 3635803497251860954561451

theorem tailTrace_7080702 : CollatzResearch.WordTrace tailWord_7080702 prefixEnd_7080702 3635803497251860954561451 := by
  unfold tailWord_7080702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281802299229177058800545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172169612262555610980269573 32281802299229177058800545)
  ·
    refine ⟨24211351724421882794100409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32281802299229177058800545 24211351724421882794100409)
    ·
      refine ⟨18158513793316412095575307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24211351724421882794100409 18158513793316412095575307)
      ·
        refine ⟨27237770689974618143362961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18158513793316412095575307 27237770689974618143362961)
        ·
          refine ⟨20428328017480963607522221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27237770689974618143362961 20428328017480963607522221)
          ·
            refine ⟨7660623006555361352820833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20428328017480963607522221 7660623006555361352820833)
            ·
              refine ⟨5745467254916521014615625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7660623006555361352820833 5745467254916521014615625)
              ·
                refine ⟨4309100441187390760961719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745467254916521014615625 4309100441187390760961719)
                ·
                  refine ⟨6463650661781086141442579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309100441187390760961719 6463650661781086141442579)
                  ·
                    refine ⟨9695475992671629212163869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463650661781086141442579 9695475992671629212163869)
                    ·
                      refine ⟨3635803497251860954561451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695475992671629212163869 3635803497251860954561451)
                      ·
                        rfl

theorem cell23_7080702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_7080702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080702 prefixEnd_7080702 := by exact prefixLift 7080702
  have htrace : WordTrace (prefixWord ++ tailWord_7080702) baseStart_7080702 baseEnd_7080702 := by
    simpa [prefixWord, tailWord_7080702, baseEnd_7080702] using wordTrace_append hprefix tailTrace_7080702
  have hstable : (prefixWord ++ tailWord_7080702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080702).length < 2 ^ (prefixWord ++ tailWord_7080702).sum := by decide
  have hdescent : baseEnd_7080702 < baseStart_7080702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080707 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3]
def baseStart_7080707 : Nat := 118140960795 + 7080707 * 2 ^ 59
def prefixEnd_7080707 : Nat := 4983230072969 + 3 ^ 40 * 7080707 * 2
def baseEnd_7080707 : Nat := 3635806064655133434998927

theorem tailTrace_7080707 : CollatzResearch.WordTrace tailWord_7080707 prefixEnd_7080707 3635806064655133434998927 := by
  unfold tailWord_7080707
  simp only [CollatzResearch.WordTrace]
  refine ⟨258254600758815302324336375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172169733839210201549557583 258254600758815302324336375)
  ·
    refine ⟨387381901138222953486504563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258254600758815302324336375 387381901138222953486504563)
    ·
      refine ⟨581072851707334430229756845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387381901138222953486504563 581072851707334430229756845)
      ·
        refine ⟨217902319390250411336158817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581072851707334430229756845 217902319390250411336158817)
        ·
          refine ⟨163426739542687808502119113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217902319390250411336158817 163426739542687808502119113)
          ·
            refine ⟨122570054657015856376589335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163426739542687808502119113 122570054657015856376589335)
            ·
              refine ⟨183855081985523784564884003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122570054657015856376589335 183855081985523784564884003)
              ·
                refine ⟨275782622978285676847326005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183855081985523784564884003 275782622978285676847326005)
                ·
                  refine ⟨25854620904214282204436813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275782622978285676847326005 25854620904214282204436813)
                  ·
                    refine ⟨9695482839080355826663805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25854620904214282204436813 9695482839080355826663805)
                    ·
                      refine ⟨3635806064655133434998927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695482839080355826663805 3635806064655133434998927)
                      ·
                        rfl

theorem cell23_7080707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_7080707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080707 prefixEnd_7080707 := by exact prefixLift 7080707
  have htrace : WordTrace (prefixWord ++ tailWord_7080707) baseStart_7080707 baseEnd_7080707 := by
    simpa [prefixWord, tailWord_7080707, baseEnd_7080707] using wordTrace_append hprefix tailTrace_7080707
  have hstable : (prefixWord ++ tailWord_7080707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080707).length < 2 ^ (prefixWord ++ tailWord_7080707).sum := by decide
  have hdescent : baseEnd_7080707 < baseStart_7080707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080737 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7080737 : Nat := 118140960795 + 7080737 * 2 ^ 59
def prefixEnd_7080737 : Nat := 4983230072969 + 3 ^ 40 * 7080737 * 2
def baseEnd_7080737 : Nat := 3635821469074768317623789

theorem tailTrace_7080737 : CollatzResearch.WordTrace tailWord_7080737 prefixEnd_7080737 3635821469074768317623789 := by
  unfold tailWord_7080737
  simp only [CollatzResearch.WordTrace]
  refine ⟨258255694948706617447928465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172170463299137744965285643 258255694948706617447928465)
  ·
    refine ⟨193691771211529963085946349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258255694948706617447928465 193691771211529963085946349)
    ·
      refine ⟨72634414204323736157229881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193691771211529963085946349 72634414204323736157229881)
      ·
        refine ⟨54475810653242802117922411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72634414204323736157229881 54475810653242802117922411)
        ·
          refine ⟨81713715979864203176883617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54475810653242802117922411 81713715979864203176883617)
          ·
            refine ⟨61285286984898152382662713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81713715979864203176883617 61285286984898152382662713)
            ·
              refine ⟨45963965238673614286997035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61285286984898152382662713 45963965238673614286997035)
              ·
                refine ⟨68945947858010421430495553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45963965238673614286997035 68945947858010421430495553)
                ·
                  refine ⟨51709460893507816072871665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68945947858010421430495553 51709460893507816072871665)
                  ·
                    refine ⟨38782095670130862054653749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51709460893507816072871665 38782095670130862054653749)
                    ·
                      refine ⟨3635821469074768317623789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38782095670130862054653749 3635821469074768317623789)
                      ·
                        rfl

theorem cell23_7080737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7080737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080737 prefixEnd_7080737 := by exact prefixLift 7080737
  have htrace : WordTrace (prefixWord ++ tailWord_7080737) baseStart_7080737 baseEnd_7080737 := by
    simpa [prefixWord, tailWord_7080737, baseEnd_7080737] using wordTrace_append hprefix tailTrace_7080737
  have hstable : (prefixWord ++ tailWord_7080737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080737).length < 2 ^ (prefixWord ++ tailWord_7080737).sum := by decide
  have hdescent : baseEnd_7080737 < baseStart_7080737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080821 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 7]
def baseStart_7080821 : Nat := 118140960795 + 7080821 * 2 ^ 59
def prefixEnd_7080821 : Nat := 4983230072969 + 3 ^ 40 * 7080821 * 2
def baseEnd_7080821 : Nat := 403984955716638443219267

theorem tailTrace_7080821 : CollatzResearch.WordTrace tailWord_7080821 prefixEnd_7080821 403984955716638443219267 := by
  unfold tailWord_7080821
  simp only [CollatzResearch.WordTrace]
  refine ⟨258258758680402299793986317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172172505786934866529324211 258258758680402299793986317)
  ·
    refine ⟨96847034505150862422744869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258258758680402299793986317 96847034505150862422744869)
    ·
      refine ⟨18158818969715786704264663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96847034505150862422744869 18158818969715786704264663)
      ·
        refine ⟨27238228454573680056396995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18158818969715786704264663 27238228454573680056396995)
        ·
          refine ⟨40857342681860520084595493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27238228454573680056396995 40857342681860520084595493)
          ·
            refine ⟨7660751752848847515861655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40857342681860520084595493 7660751752848847515861655)
            ·
              refine ⟨11491127629273271273792483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660751752848847515861655 11491127629273271273792483)
              ·
                refine ⟨17236691443909906910688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491127629273271273792483 17236691443909906910688725)
                ·
                  refine ⟨403984955716638443219267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17236691443909906910688725 403984955716638443219267)
                  ·
                    rfl

theorem cell23_7080821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_7080821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080821 prefixEnd_7080821 := by exact prefixLift 7080821
  have htrace : WordTrace (prefixWord ++ tailWord_7080821) baseStart_7080821 baseEnd_7080821 := by
    simpa [prefixWord, tailWord_7080821, baseEnd_7080821] using wordTrace_append hprefix tailTrace_7080821
  have hstable : (prefixWord ++ tailWord_7080821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080821).length < 2 ^ (prefixWord ++ tailWord_7080821).sum := by decide
  have hdescent : baseEnd_7080821 < baseStart_7080821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080827 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_7080827 : Nat := 118140960795 + 7080827 * 2 ^ 59
def prefixEnd_7080827 : Nat := 4983230072969 + 3 ^ 40 * 7080827 * 2
def baseEnd_7080827 : Nat := 3635867682333672965498375

theorem tailTrace_7080827 : CollatzResearch.WordTrace tailWord_7080827 prefixEnd_7080827 3635867682333672965498375 := by
  unfold tailWord_7080827
  simp only [CollatzResearch.WordTrace]
  refine ⟨258258977518380562818704735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172172651678920375212469823 258258977518380562818704735)
  ·
    refine ⟨387388466277570844228057103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258258977518380562818704735 387388466277570844228057103)
    ·
      refine ⟨581082699416356266342085655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387388466277570844228057103 581082699416356266342085655)
      ·
        refine ⟨871624049124534399513128483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581082699416356266342085655 871624049124534399513128483)
        ·
          refine ⟨1307436073686801599269692725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871624049124534399513128483 1307436073686801599269692725)
          ·
            refine ⟨122572131908137649931533693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1307436073686801599269692725 122572131908137649931533693)
            ·
              refine ⟨45964549465551618724325135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122572131908137649931533693 45964549465551618724325135)
              ·
                refine ⟨68946824198327428086487703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45964549465551618724325135 68946824198327428086487703)
                ·
                  refine ⟨103420236297491142129731555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68946824198327428086487703 103420236297491142129731555)
                  ·
                    refine ⟨155130354446236713194597333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103420236297491142129731555 155130354446236713194597333)
                    ·
                      refine ⟨3635867682333672965498375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155130354446236713194597333 3635867682333672965498375)
                      ·
                        rfl

theorem cell23_7080827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_7080827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080827 prefixEnd_7080827 := by exact prefixLift 7080827
  have htrace : WordTrace (prefixWord ++ tailWord_7080827) baseStart_7080827 baseEnd_7080827 := by
    simpa [prefixWord, tailWord_7080827, baseEnd_7080827] using wordTrace_append hprefix tailTrace_7080827
  have hstable : (prefixWord ++ tailWord_7080827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080827).length < 2 ^ (prefixWord ++ tailWord_7080827).sum := by decide
  have hdescent : baseEnd_7080827 < baseStart_7080827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080902 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7080902 : Nat := 118140960795 + 7080902 * 2 ^ 59
def prefixEnd_7080902 : Nat := 4983230072969 + 3 ^ 40 * 7080902 * 2
def baseEnd_7080902 : Nat := 1211968731127586724020177

theorem tailTrace_7080902 : CollatzResearch.WordTrace tailWord_7080902 prefixEnd_7080902 1211968731127586724020177 := by
  unfold tailWord_7080902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070678531034651582115155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172174475328739233751789973 8070678531034651582115155)
  ·
    refine ⟨12106017796551977373172733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8070678531034651582115155 12106017796551977373172733)
    ·
      refine ⟨4539756673706991514939775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12106017796551977373172733 4539756673706991514939775)
      ·
        refine ⟨6809635010560487272409663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539756673706991514939775 6809635010560487272409663)
        ·
          refine ⟨10214452515840730908614495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809635010560487272409663 10214452515840730908614495)
          ·
            refine ⟨15321678773761096362921743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214452515840730908614495 15321678773761096362921743)
            ·
              refine ⟨22982518160641644544382615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15321678773761096362921743 22982518160641644544382615)
              ·
                refine ⟨34473777240962466816573923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22982518160641644544382615 34473777240962466816573923)
                ·
                  refine ⟨51710665861443700224860885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34473777240962466816573923 51710665861443700224860885)
                  ·
                    refine ⟨1211968731127586724020177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51710665861443700224860885 1211968731127586724020177)
                    ·
                      rfl

theorem cell23_7080902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7080902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080902 prefixEnd_7080902 := by exact prefixLift 7080902
  have htrace : WordTrace (prefixWord ++ tailWord_7080902) baseStart_7080902 baseEnd_7080902 := by
    simpa [prefixWord, tailWord_7080902, baseEnd_7080902] using wordTrace_append hprefix tailTrace_7080902
  have hstable : (prefixWord ++ tailWord_7080902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080902).length < 2 ^ (prefixWord ++ tailWord_7080902).sum := by decide
  have hdescent : baseEnd_7080902 < baseStart_7080902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080938 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_7080938 : Nat := 118140960795 + 7080938 * 2 ^ 59
def prefixEnd_7080938 : Nat := 4983230072969 + 3 ^ 40 * 7080938 * 2
def baseEnd_7080938 : Nat := 3635924678686322031210365

theorem tailTrace_7080938 : CollatzResearch.WordTrace tailWord_7080938 prefixEnd_7080938 3635924678686322031210365 := by
  unfold tailWord_7080938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64565756505244607193998867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172175350680652285850663645 64565756505244607193998867)
  ·
    refine ⟨96848634757866910790998301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64565756505244607193998867 96848634757866910790998301)
    ·
      refine ⟨36318238034200091546624363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96848634757866910790998301 36318238034200091546624363)
      ·
        refine ⟨54477357051300137319936545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36318238034200091546624363 54477357051300137319936545)
        ·
          refine ⟨40858017788475102989952409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54477357051300137319936545 40858017788475102989952409)
          ·
            refine ⟨30643513341356327242464307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40858017788475102989952409 30643513341356327242464307)
            ·
              refine ⟨45965270012034490863696461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30643513341356327242464307 45965270012034490863696461)
              ·
                refine ⟨17236976254512934073886173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45965270012034490863696461 17236976254512934073886173)
                ·
                  refine ⟨6463866095442350277707315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17236976254512934073886173 6463866095442350277707315)
                  ·
                    refine ⟨9695799143163525416560973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463866095442350277707315 9695799143163525416560973)
                    ·
                      refine ⟨3635924678686322031210365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695799143163525416560973 3635924678686322031210365)
                      ·
                        rfl

theorem cell23_7080938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_7080938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080938 prefixEnd_7080938 := by exact prefixLift 7080938
  have htrace : WordTrace (prefixWord ++ tailWord_7080938) baseStart_7080938 baseEnd_7080938 := by
    simpa [prefixWord, tailWord_7080938, baseEnd_7080938] using wordTrace_append hprefix tailTrace_7080938
  have hstable : (prefixWord ++ tailWord_7080938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080938).length < 2 ^ (prefixWord ++ tailWord_7080938).sum := by decide
  have hdescent : baseEnd_7080938 < baseStart_7080938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080971 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 4, 4]
def baseStart_7080971 : Nat := 118140960795 + 7080971 * 2 ^ 59
def prefixEnd_7080971 : Nat := 4983230072969 + 3 ^ 40 * 7080971 * 2
def baseEnd_7080971 : Nat := 1211980541182640134032571

theorem tailTrace_7080971 : CollatzResearch.WordTrace tailWord_7080971 prefixEnd_7080971 1211980541182640134032571 := by
  unfold tailWord_7080971
  simp only [CollatzResearch.WordTrace]
  refine ⟨258264229629858875411946767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172176153086572583607964511 258264229629858875411946767)
  ·
    refine ⟨387396344444788313117920151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258264229629858875411946767 387396344444788313117920151)
    ·
      refine ⟨581094516667182469676880227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387396344444788313117920151 581094516667182469676880227)
      ·
        refine ⟨871641775000773704515320341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581094516667182469676880227 871641775000773704515320341)
        ·
          refine ⟨40858208203161267399155641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 871641775000773704515320341 40858208203161267399155641)
          ·
            refine ⟨30643656152370950549366731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40858208203161267399155641 30643656152370950549366731)
            ·
              refine ⟨45965484228556425824050097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30643656152370950549366731 45965484228556425824050097)
              ·
                refine ⟨34474113171417319368037573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45965484228556425824050097 34474113171417319368037573)
                ·
                  refine ⟨6463896219640747381507045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34474113171417319368037573 6463896219640747381507045)
                  ·
                    refine ⟨1211980541182640134032571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463896219640747381507045 1211980541182640134032571)
                    ·
                      rfl

theorem cell23_7080971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 4].length) (baseStart_7080971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080971 prefixEnd_7080971 := by exact prefixLift 7080971
  have htrace : WordTrace (prefixWord ++ tailWord_7080971) baseStart_7080971 baseEnd_7080971 := by
    simpa [prefixWord, tailWord_7080971, baseEnd_7080971] using wordTrace_append hprefix tailTrace_7080971
  have hstable : (prefixWord ++ tailWord_7080971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080971).length < 2 ^ (prefixWord ++ tailWord_7080971).sum := by decide
  have hdescent : baseEnd_7080971 < baseStart_7080971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080972 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 1, 1, 3]
def baseStart_7080972 : Nat := 118140960795 + 7080972 * 2 ^ 59
def prefixEnd_7080972 : Nat := 4983230072969 + 3 ^ 40 * 7080972 * 2
def baseEnd_7080972 : Nat := 3635942137028574898185209

theorem tailTrace_7080972 : CollatzResearch.WordTrace tailWord_7080972 prefixEnd_7080972 3635942137028574898185209 := by
  unfold tailWord_7080972
  simp only [CollatzResearch.WordTrace]
  refine ⟨129132133051427626291366585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172176177401903501721822113 129132133051427626291366585)
  ·
    refine ⟨96849099788570719718524939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129132133051427626291366585 96849099788570719718524939)
    ·
      refine ⟨145273649682856079577787409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96849099788570719718524939 145273649682856079577787409)
      ·
        refine ⟨108955237262142059683340557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145273649682856079577787409 108955237262142059683340557)
        ·
          refine ⟨40858213973303272381252709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108955237262142059683340557 40858213973303272381252709)
          ·
            refine ⟨7660915119994363571484883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40858213973303272381252709 7660915119994363571484883)
            ·
              refine ⟨11491372679991545357227325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660915119994363571484883 11491372679991545357227325)
              ·
                refine ⟨4309264754996829508960247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11491372679991545357227325 4309264754996829508960247)
                ·
                  refine ⟨6463897132495244263440371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309264754996829508960247 6463897132495244263440371)
                  ·
                    refine ⟨9695845698742866395160557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463897132495244263440371 9695845698742866395160557)
                    ·
                      refine ⟨3635942137028574898185209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695845698742866395160557 3635942137028574898185209)
                      ·
                        rfl

theorem cell23_7080972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_7080972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080972 prefixEnd_7080972 := by exact prefixLift 7080972
  have htrace : WordTrace (prefixWord ++ tailWord_7080972) baseStart_7080972 baseEnd_7080972 := by
    simpa [prefixWord, tailWord_7080972, baseEnd_7080972] using wordTrace_append hprefix tailTrace_7080972
  have hstable : (prefixWord ++ tailWord_7080972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080972).length < 2 ^ (prefixWord ++ tailWord_7080972).sum := by decide
  have hdescent : baseEnd_7080972 < baseStart_7080972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080981 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7080981 : Nat := 118140960795 + 7080981 * 2 ^ 59
def prefixEnd_7080981 : Nat := 4983230072969 + 3 ^ 40 * 7080981 * 2
def baseEnd_7080981 : Nat := 3635946758354465362972667

theorem tailTrace_7080981 : CollatzResearch.WordTrace tailWord_7080981 prefixEnd_7080981 3635946758354465362972667 := by
  unfold tailWord_7080981
  simp only [CollatzResearch.WordTrace]
  refine ⟨258264594359822647119810797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172176396239881764746540531 258264594359822647119810797)
  ·
    refine ⟨96849222884933492669929049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258264594359822647119810797 96849222884933492669929049)
    ·
      refine ⟨72636917163700119502446787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96849222884933492669929049 72636917163700119502446787)
      ·
        refine ⟨108955375745550179253670181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72636917163700119502446787 108955375745550179253670181)
        ·
          refine ⟨20429132952290658610063159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108955375745550179253670181 20429132952290658610063159)
          ·
            refine ⟨30643699428435987915094739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20429132952290658610063159 30643699428435987915094739)
            ·
              refine ⟨45965549142653981872642109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30643699428435987915094739 45965549142653981872642109)
              ·
                refine ⟨17237080928495243202240791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45965549142653981872642109 17237080928495243202240791)
                ·
                  refine ⟨25855621392742864803361187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17237080928495243202240791 25855621392742864803361187)
                  ·
                    refine ⟨38783432089114297205041781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25855621392742864803361187 38783432089114297205041781)
                    ·
                      refine ⟨3635946758354465362972667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38783432089114297205041781 3635946758354465362972667)
                      ·
                        rfl

theorem cell23_7080981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7080981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080981 prefixEnd_7080981 := by exact prefixLift 7080981
  have htrace : WordTrace (prefixWord ++ tailWord_7080981) baseStart_7080981 baseEnd_7080981 := by
    simpa [prefixWord, tailWord_7080981, baseEnd_7080981] using wordTrace_append hprefix tailTrace_7080981
  have hstable : (prefixWord ++ tailWord_7080981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080981).length < 2 ^ (prefixWord ++ tailWord_7080981).sum := by decide
  have hdescent : baseEnd_7080981 < baseStart_7080981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080984 : List Nat := [2, 1, 2, 3, 2, 2, 11]
def baseStart_7080984 : Nat := 118140960795 + 7080984 * 2 ^ 59
def prefixEnd_7080984 : Nat := 4983230072969 + 3 ^ 40 * 7080984 * 2
def baseEnd_7080984 : Nat := 44888250602425047546113

theorem tailTrace_7080984 : CollatzResearch.WordTrace tailWord_7080984 prefixEnd_7080984 44888250602425047546113 := by
  unfold tailWord_7080984
  simp only [CollatzResearch.WordTrace]
  refine ⟨129132351889405889316085003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172176469185874519088113337 129132351889405889316085003)
  ·
    refine ⟨193698527834108833974127505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129132351889405889316085003 193698527834108833974127505)
    ·
      refine ⟨145273895875581625480595629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193698527834108833974127505 145273895875581625480595629)
      ·
        refine ⟨54477710953343109555223361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145273895875581625480595629 54477710953343109555223361)
        ·
          refine ⟨40858283215007332166417521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54477710953343109555223361 40858283215007332166417521)
          ·
            refine ⟨30643712411255499124813141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40858283215007332166417521 30643712411255499124813141)
            ·
              refine ⟨44888250602425047546113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30643712411255499124813141 44888250602425047546113)
              ·
                rfl

theorem cell23_7080984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 11].length) (baseStart_7080984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080984 prefixEnd_7080984 := by exact prefixLift 7080984
  have htrace : WordTrace (prefixWord ++ tailWord_7080984) baseStart_7080984 baseEnd_7080984 := by
    simpa [prefixWord, tailWord_7080984, baseEnd_7080984] using wordTrace_append hprefix tailTrace_7080984
  have hstable : (prefixWord ++ tailWord_7080984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080984).length < 2 ^ (prefixWord ++ tailWord_7080984).sum := by decide
  have hdescent : baseEnd_7080984 < baseStart_7080984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080989 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_7080989 : Nat := 118140960795 + 7080989 * 2 ^ 59
def prefixEnd_7080989 : Nat := 4983230072969 + 3 ^ 40 * 7080989 * 2
def baseEnd_7080989 : Nat := 3635950866199701331672631

theorem tailTrace_7080989 : CollatzResearch.WordTrace tailWord_7080989 prefixEnd_7080989 3635950866199701331672631 := by
  unfold tailWord_7080989
  simp only [CollatzResearch.WordTrace]
  refine ⟨258264886143793664486102021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172176590762529109657401347 258264886143793664486102021)
  ·
    refine ⟨48424666151961312091144129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258264886143793664486102021 48424666151961312091144129)
    ·
      refine ⟨36318499613970984068358097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48424666151961312091144129 36318499613970984068358097)
      ·
        refine ⟨27238874710478238051268573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36318499613970984068358097 27238874710478238051268573)
        ·
          refine ⟨10214578016429339269225715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27238874710478238051268573 10214578016429339269225715)
          ·
            refine ⟨15321867024644008903838573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214578016429339269225715 15321867024644008903838573)
            ·
              refine ⟨5745700134241503338939465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15321867024644008903838573 5745700134241503338939465)
              ·
                refine ⟨4309275100681127504204599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745700134241503338939465 4309275100681127504204599)
                ·
                  refine ⟨6463912651021691256306899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309275100681127504204599 6463912651021691256306899)
                  ·
                    refine ⟨9695868976532536884460349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463912651021691256306899 9695868976532536884460349)
                    ·
                      refine ⟨3635950866199701331672631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695868976532536884460349 3635950866199701331672631)
                      ·
                        rfl

theorem cell23_7080989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_7080989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080989 prefixEnd_7080989 := by exact prefixLift 7080989
  have htrace : WordTrace (prefixWord ++ tailWord_7080989) baseStart_7080989 baseEnd_7080989 := by
    simpa [prefixWord, tailWord_7080989, baseEnd_7080989] using wordTrace_append hprefix tailTrace_7080989
  have hstable : (prefixWord ++ tailWord_7080989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080989).length < 2 ^ (prefixWord ++ tailWord_7080989).sum := by decide
  have hdescent : baseEnd_7080989 < baseStart_7080989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7080995 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 3, 2, 2]
def baseStart_7080995 : Nat := 118140960795 + 7080995 * 2 ^ 59
def prefixEnd_7080995 : Nat := 4983230072969 + 3 ^ 40 * 7080995 * 2
def baseEnd_7080995 : Nat := 3635953947083628308197603

theorem tailTrace_7080995 : CollatzResearch.WordTrace tailWord_7080995 prefixEnd_7080995 3635953947083628308197603 := by
  unfold tailWord_7080995
  simp only [CollatzResearch.WordTrace]
  refine ⟨258265104981771927510820439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172176736654514618340546959 258265104981771927510820439)
  ·
    refine ⟨387397657472657891266230659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258265104981771927510820439 387397657472657891266230659)
    ·
      refine ⟨581096486208986836899345989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387397657472657891266230659 581096486208986836899345989)
      ·
        refine ⟨108955591164185031918627373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 581096486208986836899345989 108955591164185031918627373)
        ·
          refine ⟨40858346686569386969485265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108955591164185031918627373 40858346686569386969485265)
          ·
            refine ⟨30643760014927040227113949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40858346686569386969485265 30643760014927040227113949)
            ·
              refine ⟨11491410005597640085167731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30643760014927040227113949 11491410005597640085167731)
              ·
                refine ⟨17237115008396460127751597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491410005597640085167731 17237115008396460127751597)
                ·
                  refine ⟨6463918128148672547906849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17237115008396460127751597 6463918128148672547906849)
                  ·
                    refine ⟨4847938596111504410930137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6463918128148672547906849 4847938596111504410930137)
                    ·
                      refine ⟨3635953947083628308197603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4847938596111504410930137 3635953947083628308197603)
                      ·
                        rfl

theorem cell23_7080995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_7080995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7080995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7080995 prefixEnd_7080995 := by exact prefixLift 7080995
  have htrace : WordTrace (prefixWord ++ tailWord_7080995) baseStart_7080995 baseEnd_7080995 := by
    simpa [prefixWord, tailWord_7080995, baseEnd_7080995] using wordTrace_append hprefix tailTrace_7080995
  have hstable : (prefixWord ++ tailWord_7080995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7080995).length < 2 ^ (prefixWord ++ tailWord_7080995).sum := by decide
  have hdescent : baseEnd_7080995 < baseStart_7080995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7080995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081004 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7081004 : Nat := 118140960795 + 7081004 * 2 ^ 59
def prefixEnd_7081004 : Nat := 4983230072969 + 3 ^ 40 * 7081004 * 2
def baseEnd_7081004 : Nat := 3635958568409518772985061

theorem tailTrace_7081004 : CollatzResearch.WordTrace tailWord_7081004 prefixEnd_7081004 3635958568409518772985061 := by
  unfold tailWord_7081004
  simp only [CollatzResearch.WordTrace]
  refine ⟨129132716619369661023949033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172176955492492881365265377 129132716619369661023949033)
  ·
    refine ⟨96849537464527245767961775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129132716619369661023949033 96849537464527245767961775)
    ·
      refine ⟨145274306196790868651942663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96849537464527245767961775 145274306196790868651942663)
      ·
        refine ⟨217911459295186302977913995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145274306196790868651942663 217911459295186302977913995)
        ·
          refine ⟨326867188942779454466870993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217911459295186302977913995 326867188942779454466870993)
          ·
            refine ⟨245150391707084590850153245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326867188942779454466870993 245150391707084590850153245)
            ·
              refine ⟨91931396890156721568807467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245150391707084590850153245 91931396890156721568807467)
              ·
                refine ⟨137897095335235082353211201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91931396890156721568807467 137897095335235082353211201)
                ·
                  refine ⟨103422821501426311764908401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137897095335235082353211201 103422821501426311764908401)
                  ·
                    refine ⟨77567116126069733823681301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103422821501426311764908401 77567116126069733823681301)
                    ·
                      refine ⟨3635958568409518772985061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77567116126069733823681301 3635958568409518772985061)
                      ·
                        rfl

theorem cell23_7081004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7081004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081004 prefixEnd_7081004 := by exact prefixLift 7081004
  have htrace : WordTrace (prefixWord ++ tailWord_7081004) baseStart_7081004 baseEnd_7081004 := by
    simpa [prefixWord, tailWord_7081004, baseEnd_7081004] using wordTrace_append hprefix tailTrace_7081004
  have hstable : (prefixWord ++ tailWord_7081004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081004).length < 2 ^ (prefixWord ++ tailWord_7081004).sum := by decide
  have hdescent : baseEnd_7081004 < baseStart_7081004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081011 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3]
def baseStart_7081011 : Nat := 118140960795 + 7081011 * 2 ^ 59
def prefixEnd_7081011 : Nat := 4983230072969 + 3 ^ 40 * 7081011 * 2
def baseEnd_7081011 : Nat := 3635962162774100245597529

theorem tailTrace_7081011 : CollatzResearch.WordTrace tailWord_7081011 prefixEnd_7081011 3635962162774100245597529 := by
  unfold tailWord_7081011
  simp only [CollatzResearch.WordTrace]
  refine ⟨258265688549713962243402887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172177125699809308162268591 258265688549713962243402887)
  ·
    refine ⟨387398532824570943365104331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258265688549713962243402887 387398532824570943365104331)
    ·
      refine ⟨581097799236856415047656497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387398532824570943365104331 581097799236856415047656497)
      ·
        refine ⟨435823349427642311285742373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581097799236856415047656497 435823349427642311285742373)
        ·
          refine ⟨81716878017682933366076695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435823349427642311285742373 81716878017682933366076695)
          ·
            refine ⟨122575317026524400049115043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81716878017682933366076695 122575317026524400049115043)
            ·
              refine ⟨183862975539786600073672565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122575317026524400049115043 183862975539786600073672565)
              ·
                refine ⟨17237153956854993756906803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183862975539786600073672565 17237153956854993756906803)
                ·
                  refine ⟨25855730935282490635360205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17237153956854993756906803 25855730935282490635360205)
                  ·
                    refine ⟨9695899100730933988260077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25855730935282490635360205 9695899100730933988260077)
                    ·
                      refine ⟨3635962162774100245597529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695899100730933988260077 3635962162774100245597529)
                      ·
                        rfl

theorem cell23_7081011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_7081011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081011 prefixEnd_7081011 := by exact prefixLift 7081011
  have htrace : WordTrace (prefixWord ++ tailWord_7081011) baseStart_7081011 baseEnd_7081011 := by
    simpa [prefixWord, tailWord_7081011, baseEnd_7081011] using wordTrace_append hprefix tailTrace_7081011
  have hstable : (prefixWord ++ tailWord_7081011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081011).length < 2 ^ (prefixWord ++ tailWord_7081011).sum := by decide
  have hdescent : baseEnd_7081011 < baseStart_7081011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081012 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7081012 : Nat := 118140960795 + 7081012 * 2 ^ 59
def prefixEnd_7081012 : Nat := 4983230072969 + 3 ^ 40 * 7081012 * 2
def baseEnd_7081012 : Nat := 3635962676254754741685025

theorem tailTrace_7081012 : CollatzResearch.WordTrace tailWord_7081012 prefixEnd_7081012 3635962676254754741685025 := by
  unfold tailWord_7081012
  simp only [CollatzResearch.WordTrace]
  refine ⟨129132862511355169707094645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172177150015140226276126193 129132862511355169707094645)
  ·
    refine ⟨12106205860439547160040123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129132862511355169707094645 12106205860439547160040123)
    ·
      refine ⟨18159308790659320740060185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12106205860439547160040123 18159308790659320740060185)
      ·
        refine ⟨13619481592994490555045139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18159308790659320740060185 13619481592994490555045139)
        ·
          refine ⟨20429222389491735832567709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13619481592994490555045139 20429222389491735832567709)
          ·
            refine ⟨7660958396059400937212891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20429222389491735832567709 7660958396059400937212891)
            ·
              refine ⟨11491437594089101405819337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660958396059400937212891 11491437594089101405819337)
              ·
                refine ⟨8618578195566826054364503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11491437594089101405819337 8618578195566826054364503)
                ·
                  refine ⟨12927867293350239081546755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8618578195566826054364503 12927867293350239081546755)
                  ·
                    refine ⟨19391800940025358622320133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12927867293350239081546755 19391800940025358622320133)
                    ·
                      refine ⟨3635962676254754741685025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19391800940025358622320133 3635962676254754741685025)
                      ·
                        rfl

theorem cell23_7081012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7081012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081012 prefixEnd_7081012 := by exact prefixLift 7081012
  have htrace : WordTrace (prefixWord ++ tailWord_7081012) baseStart_7081012 baseEnd_7081012 := by
    simpa [prefixWord, tailWord_7081012, baseEnd_7081012] using wordTrace_append hprefix tailTrace_7081012
  have hstable : (prefixWord ++ tailWord_7081012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081012).length < 2 ^ (prefixWord ++ tailWord_7081012).sum := by decide
  have hdescent : baseEnd_7081012 < baseStart_7081012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081045 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_7081045 : Nat := 118140960795 + 7081045 * 2 ^ 59
def prefixEnd_7081045 : Nat := 4983230072969 + 3 ^ 40 * 7081045 * 2
def baseEnd_7081045 : Nat := 3635979621116353112572373

theorem tailTrace_7081045 : CollatzResearch.WordTrace tailWord_7081045 prefixEnd_7081045 3635979621116353112572373 := by
  unfold tailWord_7081045
  simp only [CollatzResearch.WordTrace]
  refine ⟨258266928631590786050140589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172177952421060524033427059 258266928631590786050140589)
  ·
    refine ⟨96850098236846544768802721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258266928631590786050140589 96850098236846544768802721)
    ·
      refine ⟨72637573677634908576602041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96850098236846544768802721 72637573677634908576602041)
      ·
        refine ⟨54478180258226181432451531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72637573677634908576602041 54478180258226181432451531)
        ·
          refine ⟨81717270387339272148677297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54478180258226181432451531 81717270387339272148677297)
          ·
            refine ⟨61287952790504454111507973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81717270387339272148677297 61287952790504454111507973)
            ·
              refine ⟨11491491148219585145907745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61287952790504454111507973 11491491148219585145907745)
              ·
                refine ⟨8618618361164688859430809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11491491148219585145907745 8618618361164688859430809)
                ·
                  refine ⟨6463963770873516644573107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8618618361164688859430809 6463963770873516644573107)
                  ·
                    refine ⟨9695945656310274966859661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463963770873516644573107 9695945656310274966859661)
                    ·
                      refine ⟨3635979621116353112572373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695945656310274966859661 3635979621116353112572373)
                      ·
                        rfl

theorem cell23_7081045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_7081045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081045 prefixEnd_7081045 := by exact prefixLift 7081045
  have htrace : WordTrace (prefixWord ++ tailWord_7081045) baseStart_7081045 baseEnd_7081045 := by
    simpa [prefixWord, tailWord_7081045, baseEnd_7081045] using wordTrace_append hprefix tailTrace_7081045
  have hstable : (prefixWord ++ tailWord_7081045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081045).length < 2 ^ (prefixWord ++ tailWord_7081045).sum := by decide
  have hdescent : baseEnd_7081045 < baseStart_7081045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081061 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_7081061 : Nat := 118140960795 + 7081061 * 2 ^ 59
def prefixEnd_7081061 : Nat := 4983230072969 + 3 ^ 40 * 7081061 * 2
def baseEnd_7081061 : Nat := 1211995945602275016657433

theorem tailTrace_7081061 : CollatzResearch.WordTrace tailWord_7081061 prefixEnd_7081061 1211995945602275016657433 := by
  unfold tailWord_7081061
  simp only [CollatzResearch.WordTrace]
  refine ⟨258267512199532820782723037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172178341466355213855148691 258267512199532820782723037)
  ·
    refine ⟨96850317074824807793521139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258267512199532820782723037 96850317074824807793521139)
    ·
      refine ⟨145275475612237211690281709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96850317074824807793521139 145275475612237211690281709)
      ·
        refine ⟨54478303354588954383855641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145275475612237211690281709 54478303354588954383855641)
        ·
          refine ⟨40858727515941715787891731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54478303354588954383855641 40858727515941715787891731)
          ·
            refine ⟨61288091273912573681837597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40858727515941715787891731 61288091273912573681837597)
            ·
              refine ⟨22983034227717215130689099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61288091273912573681837597 22983034227717215130689099)
              ·
                refine ⟨34474551341575822696033649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22983034227717215130689099 34474551341575822696033649)
                ·
                  refine ⟨25855913506181867022025237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34474551341575822696033649 25855913506181867022025237)
                  ·
                    refine ⟨1211995945602275016657433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25855913506181867022025237 1211995945602275016657433)
                    ·
                      rfl

theorem cell23_7081061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_7081061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081061 prefixEnd_7081061 := by exact prefixLift 7081061
  have htrace : WordTrace (prefixWord ++ tailWord_7081061) baseStart_7081061 baseEnd_7081061 := by
    simpa [prefixWord, tailWord_7081061, baseEnd_7081061] using wordTrace_append hprefix tailTrace_7081061
  have hstable : (prefixWord ++ tailWord_7081061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081061).length < 2 ^ (prefixWord ++ tailWord_7081061).sum := by decide
  have hdescent : baseEnd_7081061 < baseStart_7081061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081071 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_7081071 : Nat := 118140960795 + 7081071 * 2 ^ 59
def prefixEnd_7081071 : Nat := 4983230072969 + 3 ^ 40 * 7081071 * 2
def baseEnd_7081071 : Nat := 3635992971613370010847253

theorem tailTrace_7081071 : CollatzResearch.WordTrace tailWord_7081071 prefixEnd_7081071 3635992971613370010847253 := by
  unfold tailWord_7081071
  simp only [CollatzResearch.WordTrace]
  refine ⟨258267876929496592490587067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172178584619664394993724711 258267876929496592490587067)
  ·
    refine ⟨387401815394244888735880601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258267876929496592490587067 387401815394244888735880601)
    ·
      refine ⟨290551361545683666551910451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387401815394244888735880601 290551361545683666551910451)
      ·
        refine ⟨435827042318525499827865677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290551361545683666551910451 435827042318525499827865677)
        ·
          refine ⟨163435140869447062435449629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435827042318525499827865677 163435140869447062435449629)
          ·
            refine ⟨61288177826042648413293611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163435140869447062435449629 61288177826042648413293611)
            ·
              refine ⟨91932266739063972619940417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61288177826042648413293611 91932266739063972619940417)
              ·
                refine ⟨68949200054297979464955313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91932266739063972619940417 68949200054297979464955313)
                ·
                  refine ⟨51711900040723484598716485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68949200054297979464955313 51711900040723484598716485)
                  ·
                    refine ⟨9695981257635653362259341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51711900040723484598716485 9695981257635653362259341)
                    ·
                      refine ⟨3635992971613370010847253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9695981257635653362259341 3635992971613370010847253)
                      ·
                        rfl

theorem cell23_7081071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_7081071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081071 prefixEnd_7081071 := by exact prefixLift 7081071
  have htrace : WordTrace (prefixWord ++ tailWord_7081071) baseStart_7081071 baseEnd_7081071 := by
    simpa [prefixWord, tailWord_7081071, baseEnd_7081071] using wordTrace_append hprefix tailTrace_7081071
  have hstable : (prefixWord ++ tailWord_7081071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081071).length < 2 ^ (prefixWord ++ tailWord_7081071).sum := by decide
  have hdescent : baseEnd_7081071 < baseStart_7081071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081085 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_7081085 : Nat := 118140960795 + 7081085 * 2 ^ 59
def prefixEnd_7081085 : Nat := 4983230072969 + 3 ^ 40 * 7081085 * 2
def baseEnd_7081085 : Nat := 3636000160342532956072189

theorem tailTrace_7081085 : CollatzResearch.WordTrace tailWord_7081085 prefixEnd_7081085 3636000160342532956072189 := by
  unfold tailWord_7081085
  simp only [CollatzResearch.WordTrace]
  refine ⟨258268387551445872881596709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172178925034297248587731139 258268387551445872881596709)
  ·
    refine ⟨48425322665896101165299383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258268387551445872881596709 48425322665896101165299383)
    ·
      refine ⟨72637983998844151747949075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48425322665896101165299383 72637983998844151747949075)
      ·
        refine ⟨108956975998266227621923613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72637983998844151747949075 108956975998266227621923613)
        ·
          refine ⟨40858865999349835358221355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108956975998266227621923613 40858865999349835358221355)
          ·
            refine ⟨61288298999024753037332033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40858865999349835358221355 61288298999024753037332033)
            ·
              refine ⟨45966224249268564777999025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61288298999024753037332033 45966224249268564777999025)
              ·
                refine ⟨34474668186951423583499269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45966224249268564777999025 34474668186951423583499269)
                ·
                  refine ⟨6464000285053391921906113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34474668186951423583499269 6464000285053391921906113)
                  ·
                    refine ⟨4848000213790043941429585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464000285053391921906113 4848000213790043941429585)
                    ·
                      refine ⟨3636000160342532956072189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848000213790043941429585 3636000160342532956072189)
                      ·
                        rfl

theorem cell23_7081085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_7081085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081085 prefixEnd_7081085 := by exact prefixLift 7081085
  have htrace : WordTrace (prefixWord ++ tailWord_7081085) baseStart_7081085 baseEnd_7081085 := by
    simpa [prefixWord, tailWord_7081085, baseEnd_7081085] using wordTrace_append hprefix tailTrace_7081085
  have hstable : (prefixWord ++ tailWord_7081085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081085).length < 2 ^ (prefixWord ++ tailWord_7081085).sum := by decide
  have hdescent : baseEnd_7081085 < baseStart_7081085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081089 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_7081089 : Nat := 118140960795 + 7081089 * 2 ^ 59
def prefixEnd_7081089 : Nat := 4983230072969 + 3 ^ 40 * 7081089 * 2
def baseEnd_7081089 : Nat := 3636002214265150940422171

theorem tailTrace_7081089 : CollatzResearch.WordTrace tailWord_7081089 prefixEnd_7081089 3636002214265150940422171 := by
  unfold tailWord_7081089
  simp only [CollatzResearch.WordTrace]
  refine ⟨258268533443431381564742321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172179022295620921043161547 258268533443431381564742321)
  ·
    refine ⟨193701400082573536173556741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258268533443431381564742321 193701400082573536173556741)
    ·
      refine ⟨36319012515482538032541889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193701400082573536173556741 36319012515482538032541889)
      ·
        refine ⟨27239259386611903524406417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36319012515482538032541889 27239259386611903524406417)
        ·
          refine ⟨20429444539958927643304813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27239259386611903524406417 20429444539958927643304813)
          ·
            refine ⟨7661041702484597866239305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20429444539958927643304813 7661041702484597866239305)
            ·
              refine ⟨5745781276863448399679479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661041702484597866239305 5745781276863448399679479)
              ·
                refine ⟨8618671915295172599519219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745781276863448399679479 8618671915295172599519219)
                ·
                  refine ⟨12928007872942758899278829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8618671915295172599519219 12928007872942758899278829)
                  ·
                    refine ⟨4848002952353534587229561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12928007872942758899278829 4848002952353534587229561)
                    ·
                      refine ⟨3636002214265150940422171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848002952353534587229561 3636002214265150940422171)
                      ·
                        rfl

theorem cell23_7081089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_7081089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081089 prefixEnd_7081089 := by exact prefixLift 7081089
  have htrace : WordTrace (prefixWord ++ tailWord_7081089) baseStart_7081089 baseEnd_7081089 := by
    simpa [prefixWord, tailWord_7081089, baseEnd_7081089] using wordTrace_append hprefix tailTrace_7081089
  have hstable : (prefixWord ++ tailWord_7081089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081089).length < 2 ^ (prefixWord ++ tailWord_7081089).sum := by decide
  have hdescent : baseEnd_7081089 < baseStart_7081089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081102 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7081102 : Nat := 118140960795 + 7081102 * 2 ^ 59
def prefixEnd_7081102 : Nat := 4983230072969 + 3 ^ 40 * 7081102 * 2
def baseEnd_7081102 : Nat := 3636008889513659389559611

theorem tailTrace_7081102 : CollatzResearch.WordTrace tailWord_7081102 prefixEnd_7081102 3636008889513659389559611 := by
  unfold tailWord_7081102
  simp only [CollatzResearch.WordTrace]
  refine ⟨32283625949048035598120695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172179338394922856523310373 32283625949048035598120695)
  ·
    refine ⟨48425438923572053397181043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32283625949048035598120695 48425438923572053397181043)
    ·
      refine ⟨72638158385358080095771565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48425438923572053397181043 72638158385358080095771565)
      ·
        refine ⟨27239309394509280035914337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72638158385358080095771565 27239309394509280035914337)
        ·
          refine ⟨20429482045881960026935753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27239309394509280035914337 20429482045881960026935753)
          ·
            refine ⟨15322111534411470020201815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20429482045881960026935753 15322111534411470020201815)
            ·
              refine ⟨22983167301617205030302723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15322111534411470020201815 22983167301617205030302723)
              ·
                refine ⟨34474750952425807545454085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22983167301617205030302723 34474750952425807545454085)
                ·
                  refine ⟨6464015803579838914772641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34474750952425807545454085 6464015803579838914772641)
                  ·
                    refine ⟨4848011852684879186079481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464015803579838914772641 4848011852684879186079481)
                    ·
                      refine ⟨3636008889513659389559611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848011852684879186079481 3636008889513659389559611)
                      ·
                        rfl

theorem cell23_7081102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7081102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081102 prefixEnd_7081102 := by exact prefixLift 7081102
  have htrace : WordTrace (prefixWord ++ tailWord_7081102) baseStart_7081102 baseEnd_7081102 := by
    simpa [prefixWord, tailWord_7081102, baseEnd_7081102] using wordTrace_append hprefix tailTrace_7081102
  have hstable : (prefixWord ++ tailWord_7081102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081102).length < 2 ^ (prefixWord ++ tailWord_7081102).sum := by decide
  have hdescent : baseEnd_7081102 < baseStart_7081102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081119 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7081119 : Nat := 118140960795 + 7081119 * 2 ^ 59
def prefixEnd_7081119 : Nat := 4983230072969 + 3 ^ 40 * 7081119 * 2
def baseEnd_7081119 : Nat := 3636017618684785823047033

theorem tailTrace_7081119 : CollatzResearch.WordTrace tailWord_7081119 prefixEnd_7081119 3636017618684785823047033 := by
  unfold tailWord_7081119
  simp only [CollatzResearch.WordTrace]
  refine ⟨258269627633322696688334411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172179751755548464458889607 258269627633322696688334411)
  ·
    refine ⟨387404441449984045032501617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258269627633322696688334411 387404441449984045032501617)
    ·
      refine ⟨290553331087488033774376213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387404441449984045032501617 290553331087488033774376213)
      ·
        refine ⟨13619687394726001583173885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 290553331087488033774376213 13619687394726001583173885)
        ·
          refine ⟨5107382773022250593690207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13619687394726001583173885 5107382773022250593690207)
          ·
            refine ⟨7661074159533375890535311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107382773022250593690207 7661074159533375890535311)
            ·
              refine ⟨11491611239300063835802967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661074159533375890535311 11491611239300063835802967)
              ·
                refine ⟨17237416858950095753704451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491611239300063835802967 17237416858950095753704451)
                ·
                  refine ⟨25856125288425143630556677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17237416858950095753704451 25856125288425143630556677)
                  ·
                    refine ⟨4848023491579714430729377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25856125288425143630556677 4848023491579714430729377)
                    ·
                      refine ⟨3636017618684785823047033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848023491579714430729377 3636017618684785823047033)
                      ·
                        rfl

theorem cell23_7081119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7081119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081119 prefixEnd_7081119 := by exact prefixLift 7081119
  have htrace : WordTrace (prefixWord ++ tailWord_7081119) baseStart_7081119 baseEnd_7081119 := by
    simpa [prefixWord, tailWord_7081119, baseEnd_7081119] using wordTrace_append hprefix tailTrace_7081119
  have hstable : (prefixWord ++ tailWord_7081119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081119).length < 2 ^ (prefixWord ++ tailWord_7081119).sum := by decide
  have hdescent : baseEnd_7081119 < baseStart_7081119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081121 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_7081121 : Nat := 118140960795 + 7081121 * 2 ^ 59
def prefixEnd_7081121 : Nat := 4983230072969 + 3 ^ 40 * 7081121 * 2
def baseEnd_7081121 : Nat := 1212006215215364938407341

theorem tailTrace_7081121 : CollatzResearch.WordTrace tailWord_7081121 prefixEnd_7081121 1212006215215364938407341 := by
  unfold tailWord_7081121
  simp only [CollatzResearch.WordTrace]
  refine ⟨258269700579315451029907217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172179800386210300686604811 258269700579315451029907217)
  ·
    refine ⟨193702275434486588272430413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258269700579315451029907217 193702275434486588272430413)
    ·
      refine ⟨72638353287932470602161405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193702275434486588272430413 72638353287932470602161405)
      ·
        refine ⟨27239382482974676475810527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72638353287932470602161405 27239382482974676475810527)
        ·
          refine ⟨40859073724462014713715791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27239382482974676475810527 40859073724462014713715791)
          ·
            refine ⟨61288610586693022070573687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40859073724462014713715791 61288610586693022070573687)
            ·
              refine ⟨91932915880039533105860531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61288610586693022070573687 91932915880039533105860531)
              ·
                refine ⟨137899373820059299658790797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91932915880039533105860531 137899373820059299658790797)
                ·
                  refine ⟨51712265182522237372046549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137899373820059299658790797 51712265182522237372046549)
                  ·
                    refine ⟨1212006215215364938407341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51712265182522237372046549 1212006215215364938407341)
                    ·
                      rfl

theorem cell23_7081121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_7081121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081121 prefixEnd_7081121 := by exact prefixLift 7081121
  have htrace : WordTrace (prefixWord ++ tailWord_7081121) baseStart_7081121 baseEnd_7081121 := by
    simpa [prefixWord, tailWord_7081121, baseEnd_7081121] using wordTrace_append hprefix tailTrace_7081121
  have hstable : (prefixWord ++ tailWord_7081121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081121).length < 2 ^ (prefixWord ++ tailWord_7081121).sum := by decide
  have hdescent : baseEnd_7081121 < baseStart_7081121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081178 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_7081178 : Nat := 118140960795 + 7081178 * 2 ^ 59
def prefixEnd_7081178 : Nat := 4983230072969 + 3 ^ 40 * 7081178 * 2
def baseEnd_7081178 : Nat := 3636047914043401092209261

theorem tailTrace_7081178 : CollatzResearch.WordTrace tailWord_7081178 prefixEnd_7081178 3636047914043401092209261 := by
  unfold tailWord_7081178
  simp only [CollatzResearch.WordTrace]
  refine ⟨64567944885027237441183047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172181186360072633176488125 64567944885027237441183047)
  ·
    refine ⟨96851917327540856161774571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64567944885027237441183047 96851917327540856161774571)
    ·
      refine ⟨145277875991311284242661857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96851917327540856161774571 145277875991311284242661857)
      ·
        refine ⟨108958406993483463181996393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145277875991311284242661857 108958406993483463181996393)
        ·
          refine ⟨81718805245112597386497295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108958406993483463181996393 81718805245112597386497295)
          ·
            refine ⟨122578207867668896079745943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81718805245112597386497295 122578207867668896079745943)
            ·
              refine ⟨183867311801503344119618915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122578207867668896079745943 183867311801503344119618915)
              ·
                refine ⟨275800967702255016179428373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183867311801503344119618915 275800967702255016179428373)
                ·
                  refine ⟨12928170361043203883410705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 275800967702255016179428373 12928170361043203883410705)
                  ·
                    refine ⟨9696127770782402912558029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12928170361043203883410705 9696127770782402912558029)
                    ·
                      refine ⟨3636047914043401092209261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696127770782402912558029 3636047914043401092209261)
                      ·
                        rfl

theorem cell23_7081178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_7081178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081178 prefixEnd_7081178 := by exact prefixLift 7081178
  have htrace : WordTrace (prefixWord ++ tailWord_7081178) baseStart_7081178 baseEnd_7081178 := by
    simpa [prefixWord, tailWord_7081178, baseEnd_7081178] using wordTrace_append hprefix tailTrace_7081178
  have hstable : (prefixWord ++ tailWord_7081178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081178).length < 2 ^ (prefixWord ++ tailWord_7081178).sum := by decide
  have hdescent : baseEnd_7081178 < baseStart_7081178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081195 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3]
def baseStart_7081195 : Nat := 118140960795 + 7081195 * 2 ^ 59
def prefixEnd_7081195 : Nat := 4983230072969 + 3 ^ 40 * 7081195 * 2
def baseEnd_7081195 : Nat := 3636056643214527525696683

theorem tailTrace_7081195 : CollatzResearch.WordTrace tailWord_7081195 prefixEnd_7081195 3636056643214527525696683 := by
  unfold tailWord_7081195
  simp only [CollatzResearch.WordTrace]
  refine ⟨258272399581047361668101039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172181599720698241112067359 258272399581047361668101039)
  ·
    refine ⟨387408599371571042502151559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258272399581047361668101039 387408599371571042502151559)
    ·
      refine ⟨581112899057356563753227339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387408599371571042502151559 581112899057356563753227339)
      ·
        refine ⟨871669348586034845629841009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581112899057356563753227339 871669348586034845629841009)
        ·
          refine ⟨653752011439526134222380757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871669348586034845629841009 653752011439526134222380757)
          ·
            refine ⟨15322312768113893770837049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 653752011439526134222380757 15322312768113893770837049)
            ·
              refine ⟨11491734576085420328127787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15322312768113893770837049 11491734576085420328127787)
              ·
                refine ⟨17237601864128130492191681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491734576085420328127787 17237601864128130492191681)
                ·
                  refine ⟨12928201398096097869143761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17237601864128130492191681 12928201398096097869143761)
                  ·
                    refine ⟨9696151048572073401857821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12928201398096097869143761 9696151048572073401857821)
                    ·
                      refine ⟨3636056643214527525696683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696151048572073401857821 3636056643214527525696683)
                      ·
                        rfl

theorem cell23_7081195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3].length) (baseStart_7081195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081195 prefixEnd_7081195 := by exact prefixLift 7081195
  have htrace : WordTrace (prefixWord ++ tailWord_7081195) baseStart_7081195 baseEnd_7081195 := by
    simpa [prefixWord, tailWord_7081195, baseEnd_7081195] using wordTrace_append hprefix tailTrace_7081195
  have hstable : (prefixWord ++ tailWord_7081195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081195).length < 2 ^ (prefixWord ++ tailWord_7081195).sum := by decide
  have hdescent : baseEnd_7081195 < baseStart_7081195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081201 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_7081201 : Nat := 118140960795 + 7081201 * 2 ^ 59
def prefixEnd_7081201 : Nat := 4983230072969 + 3 ^ 40 * 7081201 * 2
def baseEnd_7081201 : Nat := 3636059724098454502221655

theorem tailTrace_7081201 : CollatzResearch.WordTrace tailWord_7081201 prefixEnd_7081201 3636059724098454502221655 := by
  unfold tailWord_7081201
  simp only [CollatzResearch.WordTrace]
  refine ⟨258272618419025624692819457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172181745612683749795212971 258272618419025624692819457)
  ·
    refine ⟨193704463814269218519614593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258272618419025624692819457 193704463814269218519614593)
    ·
      refine ⟨145278347860701913889710945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193704463814269218519614593 145278347860701913889710945)
      ·
        refine ⟨108958760895526435417283209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145278347860701913889710945 108958760895526435417283209)
        ·
          refine ⟨81719070671644826562962407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108958760895526435417283209 81719070671644826562962407)
          ·
            refine ⟨122578606007467239844443611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81719070671644826562962407 122578606007467239844443611)
            ·
              refine ⟨183867909011200859766665417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122578606007467239844443611 183867909011200859766665417)
              ·
                refine ⟨137900931758400644824999063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183867909011200859766665417 137900931758400644824999063)
                ·
                  refine ⟨206851397637600967237498595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137900931758400644824999063 206851397637600967237498595)
                  ·
                    refine ⟨310277096456401450856247893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206851397637600967237498595 310277096456401450856247893)
                    ·
                      refine ⟨3636059724098454502221655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310277096456401450856247893 3636059724098454502221655)
                      ·
                        rfl

theorem cell23_7081201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_7081201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081201 prefixEnd_7081201 := by exact prefixLift 7081201
  have htrace : WordTrace (prefixWord ++ tailWord_7081201) baseStart_7081201 baseEnd_7081201 := by
    simpa [prefixWord, tailWord_7081201, baseEnd_7081201] using wordTrace_append hprefix tailTrace_7081201
  have hstable : (prefixWord ++ tailWord_7081201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081201).length < 2 ^ (prefixWord ++ tailWord_7081201).sum := by decide
  have hdescent : baseEnd_7081201 < baseStart_7081201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081219 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 1, 4]
def baseStart_7081219 : Nat := 118140960795 + 7081219 * 2 ^ 59
def prefixEnd_7081219 : Nat := 4983230072969 + 3 ^ 40 * 7081219 * 2
def baseEnd_7081219 : Nat := 1212022988916745143932191

theorem tailTrace_7081219 : CollatzResearch.WordTrace tailWord_7081219 prefixEnd_7081219 1212022988916745143932191 := by
  unfold tailWord_7081219
  simp only [CollatzResearch.WordTrace]
  refine ⟨258273274932960413766974711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172182183288640275844649807 258273274932960413766974711)
  ·
    refine ⟨387409912399440620650462067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258273274932960413766974711 387409912399440620650462067)
    ·
      refine ⟨581114868599160930975693101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387409912399440620650462067 581114868599160930975693101)
      ·
        refine ⟨217918075724685349115884913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581114868599160930975693101 217918075724685349115884913)
        ·
          refine ⟨163438556793514011836913685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217918075724685349115884913 163438556793514011836913685)
          ·
            refine ⟨7661182349695969304855329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163438556793514011836913685 7661182349695969304855329)
            ·
              refine ⟨5745886762271976978641497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661182349695969304855329 5745886762271976978641497)
              ·
                refine ⟨4309415071703982733981123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745886762271976978641497 4309415071703982733981123)
                ·
                  refine ⟨6464122607555974100971685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309415071703982733981123 6464122607555974100971685)
                  ·
                    refine ⟨1212022988916745143932191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6464122607555974100971685 1212022988916745143932191)
                    ·
                      rfl

theorem cell23_7081219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 4].length) (baseStart_7081219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081219 prefixEnd_7081219 := by exact prefixLift 7081219
  have htrace : WordTrace (prefixWord ++ tailWord_7081219) baseStart_7081219 baseEnd_7081219 := by
    simpa [prefixWord, tailWord_7081219, baseEnd_7081219] using wordTrace_append hprefix tailTrace_7081219
  have hstable : (prefixWord ++ tailWord_7081219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081219).length < 2 ^ (prefixWord ++ tailWord_7081219).sum := by decide
  have hdescent : baseEnd_7081219 < baseStart_7081219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081225 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 3]
def baseStart_7081225 : Nat := 118140960795 + 7081225 * 2 ^ 59
def prefixEnd_7081225 : Nat := 4983230072969 + 3 ^ 40 * 7081225 * 2
def baseEnd_7081225 : Nat := 3636072047634162408321545

theorem tailTrace_7081225 : CollatzResearch.WordTrace tailWord_7081225 prefixEnd_7081225 3636072047634162408321545 := by
  unfold tailWord_7081225
  simp only [CollatzResearch.WordTrace]
  refine ⟨258273493770938676791693129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172182329180625784527795419 258273493770938676791693129)
  ·
    refine ⟨193705120328204007593769847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258273493770938676791693129 193705120328204007593769847)
    ·
      refine ⟨290557680492306011390654771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193705120328204007593769847 290557680492306011390654771)
      ·
        refine ⟨435836520738459017085982157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290557680492306011390654771 435836520738459017085982157)
        ·
          refine ⟨163438695276922131407243309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435836520738459017085982157 163438695276922131407243309)
          ·
            refine ⟨61289510728845799277716241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163438695276922131407243309 61289510728845799277716241)
            ·
              refine ⟨45967133046634349458287181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61289510728845799277716241 45967133046634349458287181)
              ·
                refine ⟨17237674892487881046857693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45967133046634349458287181 17237674892487881046857693)
                ·
                  refine ⟨6464128084682955392571635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17237674892487881046857693 6464128084682955392571635)
                  ·
                    refine ⟨9696192127024433088857453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464128084682955392571635 9696192127024433088857453)
                    ·
                      refine ⟨3636072047634162408321545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696192127024433088857453 3636072047634162408321545)
                      ·
                        rfl

theorem cell23_7081225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_7081225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081225 prefixEnd_7081225 := by exact prefixLift 7081225
  have htrace : WordTrace (prefixWord ++ tailWord_7081225) baseStart_7081225 baseEnd_7081225 := by
    simpa [prefixWord, tailWord_7081225, baseEnd_7081225] using wordTrace_append hprefix tailTrace_7081225
  have hstable : (prefixWord ++ tailWord_7081225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081225).length < 2 ^ (prefixWord ++ tailWord_7081225).sum := by decide
  have hdescent : baseEnd_7081225 < baseStart_7081225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081228 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_7081228 : Nat := 118140960795 + 7081228 * 2 ^ 59
def prefixEnd_7081228 : Nat := 4983230072969 + 3 ^ 40 * 7081228 * 2
def baseEnd_7081228 : Nat := 1212024529358708632194677

theorem tailTrace_7081228 : CollatzResearch.WordTrace tailWord_7081228 prefixEnd_7081228 1212024529358708632194677 := by
  unfold tailWord_7081228
  simp only [CollatzResearch.WordTrace]
  refine ⟨129136801594963904152026169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172182402126618538869368225 129136801594963904152026169)
  ·
    refine ⟨96852601196222928114019627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129136801594963904152026169 96852601196222928114019627)
    ·
      refine ⟨145278901794334392171029441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96852601196222928114019627 145278901794334392171029441)
      ·
        refine ⟨108959176345750794128272081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145278901794334392171029441 108959176345750794128272081)
        ·
          refine ⟨81719382259313095596204061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108959176345750794128272081 81719382259313095596204061)
          ·
            refine ⟨30644768347242410848576523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81719382259313095596204061 30644768347242410848576523)
            ·
              refine ⟨45967152520863616272864785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30644768347242410848576523 45967152520863616272864785)
              ·
                refine ⟨34475364390647712204648589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45967152520863616272864785 34475364390647712204648589)
                ·
                  refine ⟨12928261646492892076743221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34475364390647712204648589 12928261646492892076743221)
                  ·
                    refine ⟨1212024529358708632194677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12928261646492892076743221 1212024529358708632194677)
                    ·
                      rfl

theorem cell23_7081228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_7081228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081228 prefixEnd_7081228 := by exact prefixLift 7081228
  have htrace : WordTrace (prefixWord ++ tailWord_7081228) baseStart_7081228 baseEnd_7081228 := by
    simpa [prefixWord, tailWord_7081228, baseEnd_7081228] using wordTrace_append hprefix tailTrace_7081228
  have hstable : (prefixWord ++ tailWord_7081228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081228).length < 2 ^ (prefixWord ++ tailWord_7081228).sum := by decide
  have hdescent : baseEnd_7081228 < baseStart_7081228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081242 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_7081242 : Nat := 118140960795 + 7081242 * 2 ^ 59
def prefixEnd_7081242 : Nat := 4983230072969 + 3 ^ 40 * 7081242 * 2
def baseEnd_7081242 : Nat := 3636080776805288841808967

theorem tailTrace_7081242 : CollatzResearch.WordTrace tailWord_7081242 prefixEnd_7081242 3636080776805288841808967 := by
  unfold tailWord_7081242
  simp only [CollatzResearch.WordTrace]
  refine ⟨64568528452969272173765495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172182742541251392463374653 64568528452969272173765495)
  ·
    refine ⟨96852792679453908260648243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64568528452969272173765495 96852792679453908260648243)
    ·
      refine ⟨145279189019180862390972365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96852792679453908260648243 145279189019180862390972365)
      ·
        refine ⟨54479695882192823396614637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145279189019180862390972365 54479695882192823396614637)
        ·
          refine ⟨20429885955822308773730489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54479695882192823396614637 20429885955822308773730489)
          ·
            refine ⟨15322414466866731580297867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20429885955822308773730489 15322414466866731580297867)
            ·
              refine ⟨22983621700300097370446801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15322414466866731580297867 22983621700300097370446801)
              ·
                refine ⟨17237716275225073027835101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22983621700300097370446801 17237716275225073027835101)
                ·
                  refine ⟨6464143603209402385438163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17237716275225073027835101 6464143603209402385438163)
                  ·
                    refine ⟨9696215404814103578157245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464143603209402385438163 9696215404814103578157245)
                    ·
                      refine ⟨3636080776805288841808967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696215404814103578157245 3636080776805288841808967)
                      ·
                        rfl

theorem cell23_7081242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_7081242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081242 prefixEnd_7081242 := by exact prefixLift 7081242
  have htrace : WordTrace (prefixWord ++ tailWord_7081242) baseStart_7081242 baseEnd_7081242 := by
    simpa [prefixWord, tailWord_7081242, baseEnd_7081242] using wordTrace_append hprefix tailTrace_7081242
  have hstable : (prefixWord ++ tailWord_7081242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081242).length < 2 ^ (prefixWord ++ tailWord_7081242).sum := by decide
  have hdescent : baseEnd_7081242 < baseStart_7081242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081245 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7081245 : Nat := 118140960795 + 7081245 * 2 ^ 59
def prefixEnd_7081245 : Nat := 4983230072969 + 3 ^ 40 * 7081245 * 2
def baseEnd_7081245 : Nat := 1212027439082417443357151

theorem tailTrace_7081245 : CollatzResearch.WordTrace tailWord_7081245 prefixEnd_7081245 1212027439082417443357151 := by
  unfold tailWord_7081245
  simp only [CollatzResearch.WordTrace]
  refine ⟨258274223230866220207421189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172182815487244146804947459 258274223230866220207421189)
  ·
    refine ⟨48426416855787416288891473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258274223230866220207421189 48426416855787416288891473)
    ·
      refine ⟨36319812641840562216668605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48426416855787416288891473 36319812641840562216668605)
      ·
        refine ⟨13619929740690210831250727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36319812641840562216668605 13619929740690210831250727)
        ·
          refine ⟨20429894611035316246876091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13619929740690210831250727 20429894611035316246876091)
          ·
            refine ⟨30644841916552974370314137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20429894611035316246876091 30644841916552974370314137)
            ·
              refine ⟨22983631437414730777735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30644841916552974370314137 22983631437414730777735603)
              ·
                refine ⟨34475447156122096166603405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22983631437414730777735603 34475447156122096166603405)
                ·
                  refine ⟨12928292683545786062476277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34475447156122096166603405 12928292683545786062476277)
                  ·
                    refine ⟨1212027439082417443357151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12928292683545786062476277 1212027439082417443357151)
                    ·
                      rfl

theorem cell23_7081245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7081245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081245 prefixEnd_7081245 := by exact prefixLift 7081245
  have htrace : WordTrace (prefixWord ++ tailWord_7081245) baseStart_7081245 baseEnd_7081245 := by
    simpa [prefixWord, tailWord_7081245, baseEnd_7081245] using wordTrace_append hprefix tailTrace_7081245
  have hstable : (prefixWord ++ tailWord_7081245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081245).length < 2 ^ (prefixWord ++ tailWord_7081245).sum := by decide
  have hdescent : baseEnd_7081245 < baseStart_7081245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081246 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7081246 : Nat := 118140960795 + 7081246 * 2 ^ 59
def prefixEnd_7081246 : Nat := 4983230072969 + 3 ^ 40 * 7081246 * 2
def baseEnd_7081246 : Nat := 3636082830727906826158949

theorem tailTrace_7081246 : CollatzResearch.WordTrace tailWord_7081246 prefixEnd_7081246 3636082830727906826158949 := by
  unfold tailWord_7081246
  simp only [CollatzResearch.WordTrace]
  refine ⟨32284282462982824672275949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172182839802575064918805061 32284282462982824672275949)
  ·
    refine ⟨12106605923618559252103481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32284282462982824672275949 12106605923618559252103481)
    ·
      refine ⟨9079954442713919439077611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12106605923618559252103481 9079954442713919439077611)
      ·
        refine ⟨13619931664070879158616417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079954442713919439077611 13619931664070879158616417)
        ·
          refine ⟨10214948748053159368962313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13619931664070879158616417 10214948748053159368962313)
          ·
            refine ⟨7661211561039869526721735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10214948748053159368962313 7661211561039869526721735)
            ·
              refine ⟨11491817341559804290082603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661211561039869526721735 11491817341559804290082603)
              ·
                refine ⟨17237726012339706435123905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491817341559804290082603 17237726012339706435123905)
                ·
                  refine ⟨12928294509254779826342929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17237726012339706435123905 12928294509254779826342929)
                  ·
                    refine ⟨9696220881941084869757197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12928294509254779826342929 9696220881941084869757197)
                    ·
                      refine ⟨3636082830727906826158949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696220881941084869757197 3636082830727906826158949)
                      ·
                        rfl

theorem cell23_7081246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7081246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081246 prefixEnd_7081246 := by exact prefixLift 7081246
  have htrace : WordTrace (prefixWord ++ tailWord_7081246) baseStart_7081246 baseEnd_7081246 := by
    simpa [prefixWord, tailWord_7081246, baseEnd_7081246] using wordTrace_append hprefix tailTrace_7081246
  have hstable : (prefixWord ++ tailWord_7081246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081246).length < 2 ^ (prefixWord ++ tailWord_7081246).sum := by decide
  have hdescent : baseEnd_7081246 < baseStart_7081246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081316 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_7081316 : Nat := 118140960795 + 7081316 * 2 ^ 59
def prefixEnd_7081316 : Nat := 4983230072969 + 3 ^ 40 * 7081316 * 2
def baseEnd_7081316 : Nat := 3636118774373721552283627

theorem tailTrace_7081316 : CollatzResearch.WordTrace tailWord_7081316 prefixEnd_7081316 3636118774373721552283627 := by
  unfold tailWord_7081316
  simp only [CollatzResearch.WordTrace]
  refine ⟨129138406406804499666627901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172184541875739332888837201 129138406406804499666627901)
  ·
    refine ⟨48426902402551687374985463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129138406406804499666627901 48426902402551687374985463)
    ·
      refine ⟨72640353603827531062478195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48426902402551687374985463 72640353603827531062478195)
      ·
        refine ⟨108960530405741296593717293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72640353603827531062478195 108960530405741296593717293)
        ·
          refine ⟨40860198902152986222643985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108960530405741296593717293 40860198902152986222643985)
          ·
            refine ⟨30645149176614739666982989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40860198902152986222643985 30645149176614739666982989)
            ·
              refine ⟨11491930941230527375118621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30645149176614739666982989 11491930941230527375118621)
              ·
                refine ⟨4309474102961447765669483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11491930941230527375118621 4309474102961447765669483)
                ·
                  refine ⟨6464211154442171648504225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309474102961447765669483 6464211154442171648504225)
                  ·
                    refine ⟨4848158365831628736378169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464211154442171648504225 4848158365831628736378169)
                    ·
                      refine ⟨3636118774373721552283627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848158365831628736378169 3636118774373721552283627)
                      ·
                        rfl

theorem cell23_7081316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_7081316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081316 prefixEnd_7081316 := by exact prefixLift 7081316
  have htrace : WordTrace (prefixWord ++ tailWord_7081316) baseStart_7081316 baseEnd_7081316 := by
    simpa [prefixWord, tailWord_7081316, baseEnd_7081316] using wordTrace_append hprefix tailTrace_7081316
  have hstable : (prefixWord ++ tailWord_7081316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081316).length < 2 ^ (prefixWord ++ tailWord_7081316).sum := by decide
  have hdescent : baseEnd_7081316 < baseStart_7081316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081322 : List Nat := [3, 1, 3, 3, 3, 1, 9]
def baseStart_7081322 : Nat := 118140960795 + 7081322 * 2 ^ 59
def prefixEnd_7081322 : Nat := 4983230072969 + 3 ^ 40 * 7081322 * 2
def baseEnd_7081322 : Nat := 44890393274785784306279

theorem tailTrace_7081322 : CollatzResearch.WordTrace tailWord_7081322 prefixEnd_7081322 44890393274785784306279 := by
  unfold tailWord_7081322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64569257912896815589493555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172184687767724841571982813 64569257912896815589493555)
  ·
    refine ⟨96853886869345223384240333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64569257912896815589493555 96853886869345223384240333)
    ·
      refine ⟨36320207576004458769090125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96853886869345223384240333 36320207576004458769090125)
      ·
        refine ⟨13620077841001672038408797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36320207576004458769090125 13620077841001672038408797)
        ·
          refine ⟨5107529190375627014403299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13620077841001672038408797 5107529190375627014403299)
          ·
            refine ⟨7661293785563440521604949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107529190375627014403299 7661293785563440521604949)
            ·
              refine ⟨44890393274785784306279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7661293785563440521604949 44890393274785784306279)
              ·
                rfl

theorem cell23_7081322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 9].length) (baseStart_7081322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081322 prefixEnd_7081322 := by exact prefixLift 7081322
  have htrace : WordTrace (prefixWord ++ tailWord_7081322) baseStart_7081322 baseEnd_7081322 := by
    simpa [prefixWord, tailWord_7081322, baseEnd_7081322] using wordTrace_append hprefix tailTrace_7081322
  have hstable : (prefixWord ++ tailWord_7081322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081322).length < 2 ^ (prefixWord ++ tailWord_7081322).sum := by decide
  have hdescent : baseEnd_7081322 < baseStart_7081322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081328 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_7081328 : Nat := 118140960795 + 7081328 * 2 ^ 59
def prefixEnd_7081328 : Nat := 4983230072969 + 3 ^ 40 * 7081328 * 2
def baseEnd_7081328 : Nat := 3636124936141575505333571

theorem tailTrace_7081328 : CollatzResearch.WordTrace tailWord_7081328 prefixEnd_7081328 3636124936141575505333571 := by
  unfold tailWord_7081328
  simp only [CollatzResearch.WordTrace]
  refine ⟨129138625244782762691346319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172184833659710350255128425 129138625244782762691346319)
  ·
    refine ⟨193707937867174144037019479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129138625244782762691346319 193707937867174144037019479)
    ·
      refine ⟨290561906800761216055529219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193707937867174144037019479 290561906800761216055529219)
      ·
        refine ⟨435842860201141824083293829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290561906800761216055529219 435842860201141824083293829)
        ·
          refine ⟨81720536287714092015617593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435842860201141824083293829 81720536287714092015617593)
          ·
            refine ⟨61290402215785569011713195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81720536287714092015617593 61290402215785569011713195)
            ·
              refine ⟨91935603323678353517569793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61290402215785569011713195 91935603323678353517569793)
              ·
                refine ⟨68951702492758765138177345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91935603323678353517569793 68951702492758765138177345)
                ·
                  refine ⟨51713776869569073853633009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68951702492758765138177345 51713776869569073853633009)
                  ·
                    refine ⟨38785332652176805390224757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51713776869569073853633009 38785332652176805390224757)
                    ·
                      refine ⟨3636124936141575505333571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38785332652176805390224757 3636124936141575505333571)
                      ·
                        rfl

theorem cell23_7081328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_7081328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081328 prefixEnd_7081328 := by exact prefixLift 7081328
  have htrace : WordTrace (prefixWord ++ tailWord_7081328) baseStart_7081328 baseEnd_7081328 := by
    simpa [prefixWord, tailWord_7081328, baseEnd_7081328] using wordTrace_append hprefix tailTrace_7081328
  have hstable : (prefixWord ++ tailWord_7081328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081328).length < 2 ^ (prefixWord ++ tailWord_7081328).sum := by decide
  have hdescent : baseEnd_7081328 < baseStart_7081328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081333 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_7081333 : Nat := 118140960795 + 7081333 * 2 ^ 59
def prefixEnd_7081333 : Nat := 4983230072969 + 3 ^ 40 * 7081333 * 2
def baseEnd_7081333 : Nat := 3636127503544847985771049

theorem tailTrace_7081333 : CollatzResearch.WordTrace tailWord_7081333 prefixEnd_7081333 3636127503544847985771049 := by
  unfold tailWord_7081333
  simp only [CollatzResearch.WordTrace]
  refine ⟨258277432854547411236624653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172184955236364940824416435 258277432854547411236624653)
  ·
    refine ⟨96854037320455279213734245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258277432854547411236624653 96854037320455279213734245)
    ·
      refine ⟨18160131997585364852575171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96854037320455279213734245 18160131997585364852575171)
      ·
        refine ⟨27240197996378047278862757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18160131997585364852575171 27240197996378047278862757)
        ·
          refine ⟨5107537124320883864786767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27240197996378047278862757 5107537124320883864786767)
          ·
            refine ⟨7661305686481325797180151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107537124320883864786767 7661305686481325797180151)
            ·
              refine ⟨11491958529721988695770227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661305686481325797180151 11491958529721988695770227)
              ·
                refine ⟨17237937794582983043655341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491958529721988695770227 17237937794582983043655341)
                ·
                  refine ⟨6464226672968618641370753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17237937794582983043655341 6464226672968618641370753)
                  ·
                    refine ⟨4848170004726463981028065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464226672968618641370753 4848170004726463981028065)
                    ·
                      refine ⟨3636127503544847985771049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848170004726463981028065 3636127503544847985771049)
                      ·
                        rfl

theorem cell23_7081333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_7081333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081333 prefixEnd_7081333 := by exact prefixLift 7081333
  have htrace : WordTrace (prefixWord ++ tailWord_7081333) baseStart_7081333 baseEnd_7081333 := by
    simpa [prefixWord, tailWord_7081333, baseEnd_7081333] using wordTrace_append hprefix tailTrace_7081333
  have hstable : (prefixWord ++ tailWord_7081333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081333).length < 2 ^ (prefixWord ++ tailWord_7081333).sum := by decide
  have hdescent : baseEnd_7081333 < baseStart_7081333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081338 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_7081338 : Nat := 118140960795 + 7081338 * 2 ^ 59
def prefixEnd_7081338 : Nat := 4983230072969 + 3 ^ 40 * 7081338 * 2
def baseEnd_7081338 : Nat := 3636130070948120466208525

theorem tailTrace_7081338 : CollatzResearch.WordTrace tailWord_7081338 prefixEnd_7081338 3636130070948120466208525 := by
  unfold tailWord_7081338
  simp only [CollatzResearch.WordTrace]
  refine ⟨64569403804882324272639167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172185076813019531393704445 64569403804882324272639167)
  ·
    refine ⟨96854105707323486408958751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64569403804882324272639167 96854105707323486408958751)
    ·
      refine ⟨145281158560985229613438127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96854105707323486408958751 145281158560985229613438127)
      ·
        refine ⟨217921737841477844420157191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145281158560985229613438127 217921737841477844420157191)
        ·
          refine ⟨326882606762216766630235787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217921737841477844420157191 326882606762216766630235787)
          ·
            refine ⟨490323910143325149945353681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326882606762216766630235787 490323910143325149945353681)
            ·
              refine ⟨367742932607493862459015261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490323910143325149945353681 367742932607493862459015261)
              ·
                refine ⟨137903599727810198422130723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367742932607493862459015261 137903599727810198422130723)
                ·
                  refine ⟨206855399591715297633196085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137903599727810198422130723 206855399591715297633196085)
                  ·
                    refine ⟨19392693711723309153112133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206855399591715297633196085 19392693711723309153112133)
                    ·
                      refine ⟨3636130070948120466208525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19392693711723309153112133 3636130070948120466208525)
                      ·
                        rfl

theorem cell23_7081338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_7081338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081338 prefixEnd_7081338 := by exact prefixLift 7081338
  have htrace : WordTrace (prefixWord ++ tailWord_7081338) baseStart_7081338 baseEnd_7081338 := by
    simpa [prefixWord, tailWord_7081338, baseEnd_7081338] using wordTrace_append hprefix tailTrace_7081338
  have hstable : (prefixWord ++ tailWord_7081338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081338).length < 2 ^ (prefixWord ++ tailWord_7081338).sum := by decide
  have hdescent : baseEnd_7081338 < baseStart_7081338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081349 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_7081349 : Nat := 118140960795 + 7081349 * 2 ^ 59
def prefixEnd_7081349 : Nat := 4983230072969 + 3 ^ 40 * 7081349 * 2
def baseEnd_7081349 : Nat := 3636135719235319923170975

theorem tailTrace_7081349 : CollatzResearch.WordTrace tailWord_7081349 prefixEnd_7081349 3636135719235319923170975 := by
  unfold tailWord_7081349
  simp only [CollatzResearch.WordTrace]
  refine ⟨258278016422489445969207101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172185344281659630646138067 258278016422489445969207101)
  ·
    refine ⟨96854256158433542238452663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258278016422489445969207101 96854256158433542238452663)
    ·
      refine ⟨145281384237650313357678995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96854256158433542238452663 145281384237650313357678995)
      ·
        refine ⟨217922076356475470036518493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145281384237650313357678995 217922076356475470036518493)
        ·
          refine ⟨81720778633678301263694435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217922076356475470036518493 81720778633678301263694435)
          ·
            refine ⟨122581167950517451895541653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81720778633678301263694435 122581167950517451895541653)
            ·
              refine ⟨5745992247680505557603515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122581167950517451895541653 5745992247680505557603515)
              ·
                refine ⟨8618988371520758336405273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745992247680505557603515 8618988371520758336405273)
                ·
                  refine ⟨6464241278640568752303955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8618988371520758336405273 6464241278640568752303955)
                  ·
                    refine ⟨9696361917960853128455933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464241278640568752303955 9696361917960853128455933)
                    ·
                      refine ⟨3636135719235319923170975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696361917960853128455933 3636135719235319923170975)
                      ·
                        rfl

theorem cell23_7081349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_7081349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081349 prefixEnd_7081349 := by exact prefixLift 7081349
  have htrace : WordTrace (prefixWord ++ tailWord_7081349) baseStart_7081349 baseEnd_7081349 := by
    simpa [prefixWord, tailWord_7081349, baseEnd_7081349] using wordTrace_append hprefix tailTrace_7081349
  have hstable : (prefixWord ++ tailWord_7081349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081349).length < 2 ^ (prefixWord ++ tailWord_7081349).sum := by decide
  have hdescent : baseEnd_7081349 < baseStart_7081349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081375 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7081375 : Nat := 118140960795 + 7081375 * 2 ^ 59
def prefixEnd_7081375 : Nat := 4983230072969 + 3 ^ 40 * 7081375 * 2
def baseEnd_7081375 : Nat := 3636149069732336821445855

theorem tailTrace_7081375 : CollatzResearch.WordTrace tailWord_7081375 prefixEnd_7081375 3636149069732336821445855 := by
  unfold tailWord_7081375
  simp only [CollatzResearch.WordTrace]
  refine ⟨258278964720395252409653579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172185976480263501606435719 258278964720395252409653579)
  ·
    refine ⟨387418447080592878614480369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258278964720395252409653579 387418447080592878614480369)
    ·
      refine ⟨290563835310444658960860277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387418447080592878614480369 290563835310444658960860277)
      ·
        refine ⟨27240359560354186777580651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290563835310444658960860277 27240359560354186777580651)
        ·
          refine ⟨40860539340531280166370977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27240359560354186777580651 40860539340531280166370977)
          ·
            refine ⟨30645404505398460124778233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40860539340531280166370977 30645404505398460124778233)
            ·
              refine ⟨22984053379048845093583675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30645404505398460124778233 22984053379048845093583675)
              ·
                refine ⟨34476080068573267640375513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22984053379048845093583675 34476080068573267640375513)
                ·
                  refine ⟨25857060051429950730281635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34476080068573267640375513 25857060051429950730281635)
                  ·
                    refine ⟨38785590077144926095422453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25857060051429950730281635 38785590077144926095422453)
                    ·
                      refine ⟨3636149069732336821445855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38785590077144926095422453 3636149069732336821445855)
                      ·
                        rfl

theorem cell23_7081375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7081375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081375 prefixEnd_7081375 := by exact prefixLift 7081375
  have htrace : WordTrace (prefixWord ++ tailWord_7081375) baseStart_7081375 baseEnd_7081375 := by
    simpa [prefixWord, tailWord_7081375, baseEnd_7081375] using wordTrace_append hprefix tailTrace_7081375
  have hstable : (prefixWord ++ tailWord_7081375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081375).length < 2 ^ (prefixWord ++ tailWord_7081375).sum := by decide
  have hdescent : baseEnd_7081375 < baseStart_7081375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081388 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7081388 : Nat := 118140960795 + 7081388 * 2 ^ 59
def prefixEnd_7081388 : Nat := 4983230072969 + 3 ^ 40 * 7081388 * 2
def baseEnd_7081388 : Nat := 3636155744980845270583295

theorem tailTrace_7081388 : CollatzResearch.WordTrace tailWord_7081388 prefixEnd_7081388 3636155744980845270583295 := by
  unfold tailWord_7081388
  simp only [CollatzResearch.WordTrace]
  refine ⟨129139719434674077814938409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172186292579565437086584545 129139719434674077814938409)
  ·
    refine ⟨96854789576005558361203807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129139719434674077814938409 96854789576005558361203807)
    ·
      refine ⟨145282184364008337541805711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96854789576005558361203807 145282184364008337541805711)
      ·
        refine ⟨217923276546012506312708567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145282184364008337541805711 217923276546012506312708567)
        ·
          refine ⟨326884914819018759469062851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217923276546012506312708567 326884914819018759469062851)
          ·
            refine ⟨490327372228528139203594277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326884914819018759469062851 490327372228528139203594277)
            ·
              refine ⟨91936382292849026100673927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490327372228528139203594277 91936382292849026100673927)
              ·
                refine ⟨137904573439273539151010891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91936382292849026100673927 137904573439273539151010891)
                ·
                  refine ⟨206856860158910308726516337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137904573439273539151010891 206856860158910308726516337)
                  ·
                    refine ⟨155142645119182731544887253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206856860158910308726516337 155142645119182731544887253)
                    ·
                      refine ⟨3636155744980845270583295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155142645119182731544887253 3636155744980845270583295)
                      ·
                        rfl

theorem cell23_7081388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7081388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081388 prefixEnd_7081388 := by exact prefixLift 7081388
  have htrace : WordTrace (prefixWord ++ tailWord_7081388) baseStart_7081388 baseEnd_7081388 := by
    simpa [prefixWord, tailWord_7081388, baseEnd_7081388] using wordTrace_append hprefix tailTrace_7081388
  have hstable : (prefixWord ++ tailWord_7081388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081388).length < 2 ^ (prefixWord ++ tailWord_7081388).sum := by decide
  have hdescent : baseEnd_7081388 < baseStart_7081388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081412 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 7]
def baseStart_7081412 : Nat := 118140960795 + 7081412 * 2 ^ 59
def prefixEnd_7081412 : Nat := 4983230072969 + 3 ^ 40 * 7081412 * 2
def baseEnd_7081412 : Nat := 404018674279617019631465

theorem tailTrace_7081412 : CollatzResearch.WordTrace tailWord_7081412 prefixEnd_7081412 404018674279617019631465 := by
  unfold tailWord_7081412
  simp only [CollatzResearch.WordTrace]
  refine ⟨129140157110630603864375245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172186876147507471819166993 129140157110630603864375245)
  ·
    refine ⟨48427558916486476449140717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129140157110630603864375245 48427558916486476449140717)
    ·
      refine ⟨18160334593682428668427769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48427558916486476449140717 18160334593682428668427769)
      ·
        refine ⟨13620250945261821501320827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18160334593682428668427769 13620250945261821501320827)
        ·
          refine ⟨20430376417892732251981241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13620250945261821501320827 20430376417892732251981241)
          ·
            refine ⟨15322782313419549188985931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20430376417892732251981241 15322782313419549188985931)
            ·
              refine ⟨22984173470129323783478897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15322782313419549188985931 22984173470129323783478897)
              ·
                refine ⟨17238130102596992837609173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22984173470129323783478897 17238130102596992837609173)
                ·
                  refine ⟨404018674279617019631465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17238130102596992837609173 404018674279617019631465)
                  ·
                    rfl

theorem cell23_7081412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_7081412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081412 prefixEnd_7081412 := by exact prefixLift 7081412
  have htrace : WordTrace (prefixWord ++ tailWord_7081412) baseStart_7081412 baseEnd_7081412 := by
    simpa [prefixWord, tailWord_7081412, baseEnd_7081412] using wordTrace_append hprefix tailTrace_7081412
  have hstable : (prefixWord ++ tailWord_7081412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081412).length < 2 ^ (prefixWord ++ tailWord_7081412).sum := by decide
  have hdescent : baseEnd_7081412 < baseStart_7081412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081462 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7081462 : Nat := 118140960795 + 7081462 * 2 ^ 59
def prefixEnd_7081462 : Nat := 4983230072969 + 3 ^ 40 * 7081462 * 2
def baseEnd_7081462 : Nat := 3636193742549277981057955

theorem tailTrace_7081462 : CollatzResearch.WordTrace tailWord_7081462 prefixEnd_7081462 3636193742549277981057955 := by
  unfold tailWord_7081462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142633616942504141754415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172188091914053377512047093 16142633616942504141754415)
  ·
    refine ⟨24213950425413756212631623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16142633616942504141754415 24213950425413756212631623)
    ·
      refine ⟨36320925638120634318947435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24213950425413756212631623 36320925638120634318947435)
      ·
        refine ⟨54481388457180951478421153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36320925638120634318947435 54481388457180951478421153)
        ·
          refine ⟨40861041342885713608815865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54481388457180951478421153 40861041342885713608815865)
          ·
            refine ⟨30645781007164285206611899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40861041342885713608815865 30645781007164285206611899)
            ·
              refine ⟨45968671510746427809917849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30645781007164285206611899 45968671510746427809917849)
              ·
                refine ⟨34476503633059820857438387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45968671510746427809917849 34476503633059820857438387)
                ·
                  refine ⟨51714755449589731286157581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34476503633059820857438387 51714755449589731286157581)
                  ·
                    refine ⟨19393033293596149232309093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51714755449589731286157581 19393033293596149232309093)
                    ·
                      refine ⟨3636193742549277981057955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19393033293596149232309093 3636193742549277981057955)
                      ·
                        rfl

theorem cell23_7081462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7081462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081462 prefixEnd_7081462 := by exact prefixLift 7081462
  have htrace : WordTrace (prefixWord ++ tailWord_7081462) baseStart_7081462 baseEnd_7081462 := by
    simpa [prefixWord, tailWord_7081462, baseEnd_7081462] using wordTrace_append hprefix tailTrace_7081462
  have hstable : (prefixWord ++ tailWord_7081462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081462).length < 2 ^ (prefixWord ++ tailWord_7081462).sum := by decide
  have hdescent : baseEnd_7081462 < baseStart_7081462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081482 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_7081482 : Nat := 118140960795 + 7081482 * 2 ^ 59
def prefixEnd_7081482 : Nat := 4983230072969 + 3 ^ 40 * 7081482 * 2
def baseEnd_7081482 : Nat := 3636204012162367902807863

theorem tailTrace_7081482 : CollatzResearch.WordTrace tailWord_7081482 prefixEnd_7081482 3636204012162367902807863 := by
  unfold tailWord_7081482
  simp only [CollatzResearch.WordTrace]
  refine ⟨64570716832751902420949675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172188578220671739789199133 64570716832751902420949675)
  ·
    refine ⟨96856075249127853631424513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64570716832751902420949675 96856075249127853631424513)
    ·
      refine ⟨72642056436845890223568385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96856075249127853631424513 72642056436845890223568385)
      ·
        refine ⟨54481542327634417667676289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72642056436845890223568385 54481542327634417667676289)
        ·
          refine ⟨40861156745725813250757217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54481542327634417667676289 40861156745725813250757217)
          ·
            refine ⟨30645867559294359938067913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40861156745725813250757217 30645867559294359938067913)
            ·
              refine ⟨22984400669470769953550935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30645867559294359938067913 22984400669470769953550935)
              ·
                refine ⟨34476601004206154930326403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22984400669470769953550935 34476601004206154930326403)
                ·
                  refine ⟨51714901506309232395489605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34476601004206154930326403 51714901506309232395489605)
                  ·
                    refine ⟨9696544032432981074154301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51714901506309232395489605 9696544032432981074154301)
                    ·
                      refine ⟨3636204012162367902807863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696544032432981074154301 3636204012162367902807863)
                      ·
                        rfl

theorem cell23_7081482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_7081482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081482 prefixEnd_7081482 := by exact prefixLift 7081482
  have htrace : WordTrace (prefixWord ++ tailWord_7081482) baseStart_7081482 baseEnd_7081482 := by
    simpa [prefixWord, tailWord_7081482, baseEnd_7081482] using wordTrace_append hprefix tailTrace_7081482
  have hstable : (prefixWord ++ tailWord_7081482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081482).length < 2 ^ (prefixWord ++ tailWord_7081482).sum := by decide
  have hdescent : baseEnd_7081482 < baseStart_7081482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081546 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_7081546 : Nat := 118140960795 + 7081546 * 2 ^ 59
def prefixEnd_7081546 : Nat := 4983230072969 + 3 ^ 40 * 7081546 * 2
def baseEnd_7081546 : Nat := 3636236874924255652407569

theorem tailTrace_7081546 : CollatzResearch.WordTrace tailWord_7081546 prefixEnd_7081546 3636236874924255652407569 := by
  unfold tailWord_7081546
  simp only [CollatzResearch.WordTrace]
  refine ⟨64571300400693937153532123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172190134401850499076085661 64571300400693937153532123)
  ·
    refine ⟨96856950601040905730298185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64571300400693937153532123 96856950601040905730298185)
    ·
      refine ⟨72642712950780679297723639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96856950601040905730298185 72642712950780679297723639)
      ·
        refine ⟨108964069426171018946585459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72642712950780679297723639 108964069426171018946585459)
        ·
          refine ⟨163446104139256528419878189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108964069426171018946585459 163446104139256528419878189)
          ·
            refine ⟨61292289052221198157454321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163446104139256528419878189 61292289052221198157454321)
            ·
              refine ⟨45969216789165898618090741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61292289052221198157454321 45969216789165898618090741)
              ·
                refine ⟨4309614073984302995446007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45969216789165898618090741 4309614073984302995446007)
                ·
                  refine ⟨6464421110976454493169011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309614073984302995446007 6464421110976454493169011)
                  ·
                    refine ⟨9696631666464681739753517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464421110976454493169011 9696631666464681739753517)
                    ·
                      refine ⟨3636236874924255652407569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696631666464681739753517 3636236874924255652407569)
                      ·
                        rfl

theorem cell23_7081546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_7081546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081546 prefixEnd_7081546 := by exact prefixLift 7081546
  have htrace : WordTrace (prefixWord ++ tailWord_7081546) baseStart_7081546 baseEnd_7081546 := by
    simpa [prefixWord, tailWord_7081546, baseEnd_7081546] using wordTrace_append hprefix tailTrace_7081546
  have hstable : (prefixWord ++ tailWord_7081546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081546).length < 2 ^ (prefixWord ++ tailWord_7081546).sum := by decide
  have hdescent : baseEnd_7081546 < baseStart_7081546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081555 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_7081555 : Nat := 118140960795 + 7081555 * 2 ^ 59
def prefixEnd_7081555 : Nat := 4983230072969 + 3 ^ 40 * 7081555 * 2
def baseEnd_7081555 : Nat := 3636241496250146117195027

theorem tailTrace_7081555 : CollatzResearch.WordTrace tailWord_7081555 prefixEnd_7081555 3636241496250146117195027 := by
  unfold tailWord_7081555
  simp only [CollatzResearch.WordTrace]
  refine ⟨258285529859743143151206119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172190353239828762100804079 258285529859743143151206119)
  ·
    refine ⟨387428294789614714726809179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258285529859743143151206119 387428294789614714726809179)
    ·
      refine ⟨581142442184422072090213769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387428294789614714726809179 581142442184422072090213769)
      ·
        refine ⟨435856831638316554067660327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581142442184422072090213769 435856831638316554067660327)
        ·
          refine ⟨653785247457474831101490491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435856831638316554067660327 653785247457474831101490491)
          ·
            refine ⟨980677871186212246652235737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653785247457474831101490491 980677871186212246652235737)
            ·
              refine ⟨735508403389659184989176803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980677871186212246652235737 735508403389659184989176803)
              ·
                refine ⟨1103262605084488777483765205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735508403389659184989176803 1103262605084488777483765205)
                ·
                  refine ⟨25857717306667705722275747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1103262605084488777483765205 25857717306667705722275747)
                  ·
                    refine ⟨38786575960001558583413621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25857717306667705722275747 38786575960001558583413621)
                    ·
                      refine ⟨3636241496250146117195027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38786575960001558583413621 3636241496250146117195027)
                      ·
                        rfl

theorem cell23_7081555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_7081555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081555 prefixEnd_7081555 := by exact prefixLift 7081555
  have htrace : WordTrace (prefixWord ++ tailWord_7081555) baseStart_7081555 baseEnd_7081555 := by
    simpa [prefixWord, tailWord_7081555, baseEnd_7081555] using wordTrace_append hprefix tailTrace_7081555
  have hstable : (prefixWord ++ tailWord_7081555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081555).length < 2 ^ (prefixWord ++ tailWord_7081555).sum := by decide
  have hdescent : baseEnd_7081555 < baseStart_7081555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081562 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_7081562 : Nat := 118140960795 + 7081562 * 2 ^ 59
def prefixEnd_7081562 : Nat := 4983230072969 + 3 ^ 40 * 7081562 * 2
def baseEnd_7081562 : Nat := 1212081696871575863269165

theorem tailTrace_7081562 : CollatzResearch.WordTrace tailWord_7081562 prefixEnd_7081562 1212081696871575863269165 := by
  unfold tailWord_7081562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64571446292679445836677735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172190523447145188897807293 64571446292679445836677735)
  ·
    refine ⟨96857169439019168755016603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64571446292679445836677735 96857169439019168755016603)
    ·
      refine ⟨145285754158528753132524905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96857169439019168755016603 145285754158528753132524905)
      ·
        refine ⟨108964315618896564849393679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145285754158528753132524905 108964315618896564849393679)
        ·
          refine ⟨163446473428344847274090519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108964315618896564849393679 163446473428344847274090519)
          ·
            refine ⟨245169710142517270911135779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163446473428344847274090519 245169710142517270911135779)
            ·
              refine ⟨367754565213775906366703669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245169710142517270911135779 367754565213775906366703669)
              ·
                refine ⟨34476990488791491221878469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367754565213775906366703669 34476990488791491221878469)
                ·
                  refine ⟨6464435716648404604102213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34476990488791491221878469 6464435716648404604102213)
                  ·
                    refine ⟨1212081696871575863269165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6464435716648404604102213 1212081696871575863269165)
                    ·
                      rfl

theorem cell23_7081562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_7081562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081562 prefixEnd_7081562 := by exact prefixLift 7081562
  have htrace : WordTrace (prefixWord ++ tailWord_7081562) baseStart_7081562 baseEnd_7081562 := by
    simpa [prefixWord, tailWord_7081562, baseEnd_7081562] using wordTrace_append hprefix tailTrace_7081562
  have hstable : (prefixWord ++ tailWord_7081562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081562).length < 2 ^ (prefixWord ++ tailWord_7081562).sum := by decide
  have hdescent : baseEnd_7081562 < baseStart_7081562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081585 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_7081585 : Nat := 118140960795 + 7081585 * 2 ^ 59
def prefixEnd_7081585 : Nat := 4983230072969 + 3 ^ 40 * 7081585 * 2
def baseEnd_7081585 : Nat := 3636256900669780999819889

theorem tailTrace_7081585 : CollatzResearch.WordTrace tailWord_7081585 prefixEnd_7081585 3636256900669780999819889 := by
  unfold tailWord_7081585
  simp only [CollatzResearch.WordTrace]
  refine ⟨258286624049634458274798209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172191082699756305516532139 258286624049634458274798209)
  ·
    refine ⟨193714968037225843706098657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258286624049634458274798209 193714968037225843706098657)
    ·
      refine ⟨145286226027919382779573993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193714968037225843706098657 145286226027919382779573993)
      ·
        refine ⟨108964669520939537084680495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145286226027919382779573993 108964669520939537084680495)
        ·
          refine ⟨163447004281409305627020743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108964669520939537084680495 163447004281409305627020743)
          ·
            refine ⟨245170506422113958440531115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163447004281409305627020743 245170506422113958440531115)
            ·
              refine ⟨367755759633170937660796673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245170506422113958440531115 367755759633170937660796673)
              ·
                refine ⟨275816819724878203245597505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367755759633170937660796673 275816819724878203245597505)
                ·
                  refine ⟨206862614793658652434198129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275816819724878203245597505 206862614793658652434198129)
                  ·
                    refine ⟨155146961095243989325648597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206862614793658652434198129 155146961095243989325648597)
                    ·
                      refine ⟨3636256900669780999819889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155146961095243989325648597 3636256900669780999819889)
                      ·
                        rfl

theorem cell23_7081585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_7081585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081585 prefixEnd_7081585 := by exact prefixLift 7081585
  have htrace : WordTrace (prefixWord ++ tailWord_7081585) baseStart_7081585 baseEnd_7081585 := by
    simpa [prefixWord, tailWord_7081585, baseEnd_7081585] using wordTrace_append hprefix tailTrace_7081585
  have hstable : (prefixWord ++ tailWord_7081585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081585).length < 2 ^ (prefixWord ++ tailWord_7081585).sum := by decide
  have hdescent : baseEnd_7081585 < baseStart_7081585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081586 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7081586 : Nat := 118140960795 + 7081586 * 2 ^ 59
def prefixEnd_7081586 : Nat := 4983230072969 + 3 ^ 40 * 7081586 * 2
def baseEnd_7081586 : Nat := 3636257414150435495907385

theorem tailTrace_7081586 : CollatzResearch.WordTrace tailWord_7081586 prefixEnd_7081586 3636257414150435495907385 := by
  unfold tailWord_7081586
  simp only [CollatzResearch.WordTrace]
  refine ⟨64571665130657708861396153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172191107015087223630389741 64571665130657708861396153)
  ·
    refine ⟨48428748847993281646047115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64571665130657708861396153 48428748847993281646047115)
    ·
      refine ⟨72643123271989922469070673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48428748847993281646047115 72643123271989922469070673)
      ·
        refine ⟨54482342453992441851803005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72643123271989922469070673 54482342453992441851803005)
        ·
          refine ⟨20430878420247165694426127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54482342453992441851803005 20430878420247165694426127)
          ·
            refine ⟨30646317630370748541639191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20430878420247165694426127 30646317630370748541639191)
            ·
              refine ⟨45969476445556122812458787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30646317630370748541639191 45969476445556122812458787)
              ·
                refine ⟨68954214668334184218688181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45969476445556122812458787 68954214668334184218688181)
                ·
                  refine ⟨6464457625156329770502017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68954214668334184218688181 6464457625156329770502017)
                  ·
                    refine ⟨4848343218867247327876513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464457625156329770502017 4848343218867247327876513)
                    ·
                      refine ⟨3636257414150435495907385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848343218867247327876513 3636257414150435495907385)
                      ·
                        rfl

theorem cell23_7081586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7081586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081586 prefixEnd_7081586 := by exact prefixLift 7081586
  have htrace : WordTrace (prefixWord ++ tailWord_7081586) baseStart_7081586 baseEnd_7081586 := by
    simpa [prefixWord, tailWord_7081586, baseEnd_7081586] using wordTrace_append hprefix tailTrace_7081586
  have hstable : (prefixWord ++ tailWord_7081586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081586).length < 2 ^ (prefixWord ++ tailWord_7081586).sum := by decide
  have hdescent : baseEnd_7081586 < baseStart_7081586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081615 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_7081615 : Nat := 118140960795 + 7081615 * 2 ^ 59
def prefixEnd_7081615 : Nat := 4983230072969 + 3 ^ 40 * 7081615 * 2
def baseEnd_7081615 : Nat := 3636272305089415882444751

theorem tailTrace_7081615 : CollatzResearch.WordTrace tailWord_7081615 prefixEnd_7081615 3636272305089415882444751 := by
  unfold tailWord_7081615
  simp only [CollatzResearch.WordTrace]
  refine ⟨258287718239525773398390299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172191812159683848932260199 258287718239525773398390299)
  ·
    refine ⟨387431577359288660097585449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258287718239525773398390299 387431577359288660097585449)
    ·
      refine ⟨290573683019466495073189087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387431577359288660097585449 290573683019466495073189087)
      ·
        refine ⟨435860524529199742609783631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290573683019466495073189087 435860524529199742609783631)
        ·
          refine ⟨653790786793799613914675447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435860524529199742609783631 653790786793799613914675447)
          ·
            refine ⟨980686180190699420872013171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653790786793799613914675447 980686180190699420872013171)
            ·
              refine ⟨1471029270286049131308019757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980686180190699420872013171 1471029270286049131308019757)
              ·
                refine ⟨551635976357268424240507409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1471029270286049131308019757 551635976357268424240507409)
                ·
                  refine ⟨413726982267951318180380557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551635976357268424240507409 413726982267951318180380557)
                  ·
                    refine ⟨155147618350481744317642709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413726982267951318180380557 155147618350481744317642709)
                    ·
                      refine ⟨3636272305089415882444751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155147618350481744317642709 3636272305089415882444751)
                      ·
                        rfl

theorem cell23_7081615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_7081615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081615 prefixEnd_7081615 := by exact prefixLift 7081615
  have htrace : WordTrace (prefixWord ++ tailWord_7081615) baseStart_7081615 baseEnd_7081615 := by
    simpa [prefixWord, tailWord_7081615, baseEnd_7081615] using wordTrace_append hprefix tailTrace_7081615
  have hstable : (prefixWord ++ tailWord_7081615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081615).length < 2 ^ (prefixWord ++ tailWord_7081615).sum := by decide
  have hdescent : baseEnd_7081615 < baseStart_7081615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081620 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7081620 : Nat := 118140960795 + 7081620 * 2 ^ 59
def prefixEnd_7081620 : Nat := 4983230072969 + 3 ^ 40 * 7081620 * 2
def baseEnd_7081620 : Nat := 3636274872492688362882229

theorem tailTrace_7081620 : CollatzResearch.WordTrace tailWord_7081620 prefixEnd_7081620 3636274872492688362882229 := by
  unfold tailWord_7081620
  simp only [CollatzResearch.WordTrace]
  refine ⟨129143950302253829626161157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172191933736338439501548209 129143950302253829626161157)
  ·
    refine ⟨24214490681672593054905217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129143950302253829626161157 24214490681672593054905217)
    ·
      refine ⟨18160868011254444791178913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24214490681672593054905217 18160868011254444791178913)
      ·
        refine ⟨13620651008440833593384185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18160868011254444791178913 13620651008440833593384185)
        ·
          refine ⟨10215488256330625195038139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13620651008440833593384185 10215488256330625195038139)
          ·
            refine ⟨15323232384495937792557209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215488256330625195038139 15323232384495937792557209)
            ·
              refine ⟨11492424288371953344417907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15323232384495937792557209 11492424288371953344417907)
              ·
                refine ⟨17238636432557930016626861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492424288371953344417907 17238636432557930016626861)
                ·
                  refine ⟨6464488662209223756235073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17238636432557930016626861 6464488662209223756235073)
                  ·
                    refine ⟨4848366496656917817176305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464488662209223756235073 4848366496656917817176305)
                    ·
                      refine ⟨3636274872492688362882229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848366496656917817176305 3636274872492688362882229)
                      ·
                        rfl

theorem cell23_7081620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7081620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081620 prefixEnd_7081620 := by exact prefixLift 7081620
  have htrace : WordTrace (prefixWord ++ tailWord_7081620) baseStart_7081620 baseEnd_7081620 := by
    simpa [prefixWord, tailWord_7081620, baseEnd_7081620] using wordTrace_append hprefix tailTrace_7081620
  have hstable : (prefixWord ++ tailWord_7081620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081620).length < 2 ^ (prefixWord ++ tailWord_7081620).sum := by decide
  have hdescent : baseEnd_7081620 < baseStart_7081620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081636 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_7081636 : Nat := 118140960795 + 7081636 * 2 ^ 59
def prefixEnd_7081636 : Nat := 4983230072969 + 3 ^ 40 * 7081636 * 2
def baseEnd_7081636 : Nat := 3636283088183160300282155

theorem tailTrace_7081636 : CollatzResearch.WordTrace tailWord_7081636 prefixEnd_7081636 3636283088183160300282155 := by
  unfold tailWord_7081636
  simp only [CollatzResearch.WordTrace]
  refine ⟨129144242086224846992452381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172192322781633129323269841 129144242086224846992452381)
  ·
    refine ⟨48429090782334317622169643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129144242086224846992452381 48429090782334317622169643)
    ·
      refine ⟨72643636173501476433254465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48429090782334317622169643 72643636173501476433254465)
      ·
        refine ⟨54482727130126107324940849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72643636173501476433254465 54482727130126107324940849)
        ·
          refine ⟨40862045347594580493705637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54482727130126107324940849 40862045347594580493705637)
          ·
            refine ⟨7661633502673983842569807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40862045347594580493705637 7661633502673983842569807)
            ·
              refine ⟨11492450254010975763854711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661633502673983842569807 11492450254010975763854711)
              ·
                refine ⟨17238675381016463645782067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492450254010975763854711 17238675381016463645782067)
                ·
                  refine ⟨25858013071524695468673101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17238675381016463645782067 25858013071524695468673101)
                  ·
                    refine ⟨9696754901821760800752413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25858013071524695468673101 9696754901821760800752413)
                    ·
                      refine ⟨3636283088183160300282155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696754901821760800752413 3636283088183160300282155)
                      ·
                        rfl

theorem cell23_7081636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_7081636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081636 prefixEnd_7081636 := by exact prefixLift 7081636
  have htrace : WordTrace (prefixWord ++ tailWord_7081636) baseStart_7081636 baseEnd_7081636 := by
    simpa [prefixWord, tailWord_7081636, baseEnd_7081636] using wordTrace_append hprefix tailTrace_7081636
  have hstable : (prefixWord ++ tailWord_7081636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081636).length < 2 ^ (prefixWord ++ tailWord_7081636).sum := by decide
  have hdescent : baseEnd_7081636 < baseStart_7081636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081654 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7081654 : Nat := 118140960795 + 7081654 * 2 ^ 59
def prefixEnd_7081654 : Nat := 4983230072969 + 3 ^ 40 * 7081654 * 2
def baseEnd_7081654 : Nat := 3636292330834941229857073

theorem tailTrace_7081654 : CollatzResearch.WordTrace tailWord_7081654 prefixEnd_7081654 3636292330834941229857073 := by
  unfold tailWord_7081654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143071292899030191191251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172192760457589655372706677 16143071292899030191191251)
  ·
    refine ⟨24214606939348545286786877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16143071292899030191191251 24214606939348545286786877)
    ·
      refine ⟨9080477602255704482545079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24214606939348545286786877 9080477602255704482545079)
      ·
        refine ⟨13620716403383556723817619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080477602255704482545079 13620716403383556723817619)
        ·
          refine ⟨20431074605075335085726429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13620716403383556723817619 20431074605075335085726429)
          ·
            refine ⟨7661652976903250657147411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20431074605075335085726429 7661652976903250657147411)
            ·
              refine ⟨11492479465354875985721117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661652976903250657147411 11492479465354875985721117)
              ·
                refine ⟨4309679799508078494645419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11492479465354875985721117 4309679799508078494645419)
                ·
                  refine ⟨6464519699262117741968129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309679799508078494645419 6464519699262117741968129)
                  ·
                    refine ⟨4848389774446588306476097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464519699262117741968129 4848389774446588306476097)
                    ·
                      refine ⟨3636292330834941229857073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848389774446588306476097 3636292330834941229857073)
                      ·
                        rfl

theorem cell23_7081654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7081654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081654 prefixEnd_7081654 := by exact prefixLift 7081654
  have htrace : WordTrace (prefixWord ++ tailWord_7081654) baseStart_7081654 baseEnd_7081654 := by
    simpa [prefixWord, tailWord_7081654, baseEnd_7081654] using wordTrace_append hprefix tailTrace_7081654
  have hstable : (prefixWord ++ tailWord_7081654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081654).length < 2 ^ (prefixWord ++ tailWord_7081654).sum := by decide
  have hdescent : baseEnd_7081654 < baseStart_7081654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081659 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 1, 4, 2]
def baseStart_7081659 : Nat := 118140960795 + 7081659 * 2 ^ 59
def prefixEnd_7081659 : Nat := 4983230072969 + 3 ^ 40 * 7081659 * 2
def baseEnd_7081659 : Nat := 3636294898238213710294549

theorem tailTrace_7081659 : CollatzResearch.WordTrace tailWord_7081659 prefixEnd_7081659 3636294898238213710294549 := by
  unfold tailWord_7081659
  simp only [CollatzResearch.WordTrace]
  refine ⟨258289323051366368912992031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172192882034244245941994687 258289323051366368912992031)
  ·
    refine ⟨387433984577049553369488047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258289323051366368912992031 387433984577049553369488047)
    ·
      refine ⟨581150976865574330054232071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387433984577049553369488047 581150976865574330054232071)
      ·
        refine ⟨871726465298361495081348107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581150976865574330054232071 871726465298361495081348107)
        ·
          refine ⟨1307589697947542242622022161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871726465298361495081348107 1307589697947542242622022161)
          ·
            refine ⟨980692273460656681966516621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307589697947542242622022161 980692273460656681966516621)
            ·
              refine ⟨367759602547746255737443733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980692273460656681966516621 367759602547746255737443733)
              ·
                refine ⟨17238731369425605737692675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367759602547746255737443733 17238731369425605737692675)
                ·
                  refine ⟨25858097054138408606539013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17238731369425605737692675 25858097054138408606539013)
                  ·
                    refine ⟨4848393197650951613726065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25858097054138408606539013 4848393197650951613726065)
                    ·
                      refine ⟨3636294898238213710294549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848393197650951613726065 3636294898238213710294549)
                      ·
                        rfl

theorem cell23_7081659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4, 2].length) (baseStart_7081659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081659 prefixEnd_7081659 := by exact prefixLift 7081659
  have htrace : WordTrace (prefixWord ++ tailWord_7081659) baseStart_7081659 baseEnd_7081659 := by
    simpa [prefixWord, tailWord_7081659, baseEnd_7081659] using wordTrace_append hprefix tailTrace_7081659
  have hstable : (prefixWord ++ tailWord_7081659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081659).length < 2 ^ (prefixWord ++ tailWord_7081659).sum := by decide
  have hdescent : baseEnd_7081659 < baseStart_7081659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081670 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7081670 : Nat := 118140960795 + 7081670 * 2 ^ 59
def prefixEnd_7081670 : Nat := 4983230072969 + 3 ^ 40 * 7081670 * 2
def baseEnd_7081670 : Nat := 3636300546525413167256999

theorem tailTrace_7081670 : CollatzResearch.WordTrace tailWord_7081670 prefixEnd_7081670 3636300546525413167256999 := by
  unfold tailWord_7081670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071553882947703680988827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172193149502884345194428309 8071553882947703680988827)
  ·
    refine ⟨12107330824421555521483241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071553882947703680988827 12107330824421555521483241)
    ·
      refine ⟨9080498118316166641112431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12107330824421555521483241 9080498118316166641112431)
      ·
        refine ⟨13620747177474249961668647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080498118316166641112431 13620747177474249961668647)
        ·
          refine ⟨20431120766211374942502971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13620747177474249961668647 20431120766211374942502971)
          ·
            refine ⟨30646681149317062413754457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20431120766211374942502971 30646681149317062413754457)
            ·
              refine ⟨22985010861987796810315843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30646681149317062413754457 22985010861987796810315843)
              ·
                refine ⟨34477516292981695215473765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22985010861987796810315843 34477516292981695215473765)
                ·
                  refine ⟨6464534304934067852901331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34477516292981695215473765 6464534304934067852901331)
                  ·
                    refine ⟨9696801457401101779351997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464534304934067852901331 9696801457401101779351997)
                    ·
                      refine ⟨3636300546525413167256999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9696801457401101779351997 3636300546525413167256999)
                      ·
                        rfl

theorem cell23_7081670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7081670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081670 prefixEnd_7081670 := by exact prefixLift 7081670
  have htrace : WordTrace (prefixWord ++ tailWord_7081670) baseStart_7081670 baseEnd_7081670 := by
    simpa [prefixWord, tailWord_7081670, baseEnd_7081670] using wordTrace_append hprefix tailTrace_7081670
  have hstable : (prefixWord ++ tailWord_7081670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081670).length < 2 ^ (prefixWord ++ tailWord_7081670).sum := by decide
  have hdescent : baseEnd_7081670 < baseStart_7081670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081729 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7081729 : Nat := 118140960795 + 7081729 * 2 ^ 59
def prefixEnd_7081729 : Nat := 4983230072969 + 3 ^ 40 * 7081729 * 2
def baseEnd_7081729 : Nat := 1212110280628009478806409

theorem tailTrace_7081729 : CollatzResearch.WordTrace tailWord_7081729 prefixEnd_7081729 1212110280628009478806409 := by
  unfold tailWord_7081729
  simp only [CollatzResearch.WordTrace]
  refine ⟨258291876161112770868040241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172194584107408513912026827 258291876161112770868040241)
  ·
    refine ⟨193718907120834578151030181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258291876161112770868040241 193718907120834578151030181)
    ·
      refine ⟨36322295085156483403318159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193718907120834578151030181 36322295085156483403318159)
      ·
        refine ⟨54483442627734725104977239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36322295085156483403318159 54483442627734725104977239)
        ·
          refine ⟨81725163941602087657465859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54483442627734725104977239 81725163941602087657465859)
          ·
            refine ⟨122587745912403131486198789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81725163941602087657465859 122587745912403131486198789)
            ·
              refine ⟨22985202358575587153662273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122587745912403131486198789 22985202358575587153662273)
              ·
                refine ⟨17238901768931690365246705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22985202358575587153662273 17238901768931690365246705)
                ·
                  refine ⟨12929176326698767773935029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17238901768931690365246705 12929176326698767773935029)
                  ·
                    refine ⟨1212110280628009478806409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12929176326698767773935029 1212110280628009478806409)
                    ·
                      rfl

theorem cell23_7081729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7081729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081729 prefixEnd_7081729 := by exact prefixLift 7081729
  have htrace : WordTrace (prefixWord ++ tailWord_7081729) baseStart_7081729 baseEnd_7081729 := by
    simpa [prefixWord, tailWord_7081729, baseEnd_7081729] using wordTrace_append hprefix tailTrace_7081729
  have hstable : (prefixWord ++ tailWord_7081729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081729).length < 2 ^ (prefixWord ++ tailWord_7081729).sum := by decide
  have hdescent : baseEnd_7081729 < baseStart_7081729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081827 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 1, 4]
def baseStart_7081827 : Nat := 118140960795 + 7081827 * 2 ^ 59
def prefixEnd_7081827 : Nat := 4983230072969 + 3 ^ 40 * 7081827 * 2
def baseEnd_7081827 : Nat := 1212127054329389684331259

theorem tailTrace_7081827 : CollatzResearch.WordTrace tailWord_7081827 prefixEnd_7081827 1212127054329389684331259 := by
  unfold tailWord_7081827
  simp only [CollatzResearch.WordTrace]
  refine ⟨258295450514757733605107735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172196967009838489070071823 258295450514757733605107735)
  ·
    refine ⟨387443175772136600407661603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258295450514757733605107735 387443175772136600407661603)
    ·
      refine ⟨581164763658204900611492405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387443175772136600407661603 581164763658204900611492405)
      ·
        refine ⟨54484196592956709432327413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 581164763658204900611492405 54484196592956709432327413)
        ·
          refine ⟨5107893430589691509280695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54484196592956709432327413 5107893430589691509280695)
          ·
            refine ⟨7661840145884537263921043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107893430589691509280695 7661840145884537263921043)
            ·
              refine ⟨11492760218826805895881565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661840145884537263921043 11492760218826805895881565)
              ·
                refine ⟨4309785082060052210955587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11492760218826805895881565 4309785082060052210955587)
                ·
                  refine ⟨6464677623090078316433381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309785082060052210955587 6464677623090078316433381)
                  ·
                    refine ⟨1212127054329389684331259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6464677623090078316433381 1212127054329389684331259)
                    ·
                      rfl

theorem cell23_7081827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 4].length) (baseStart_7081827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081827 prefixEnd_7081827 := by exact prefixLift 7081827
  have htrace : WordTrace (prefixWord ++ tailWord_7081827) baseStart_7081827 baseEnd_7081827 := by
    simpa [prefixWord, tailWord_7081827, baseEnd_7081827] using wordTrace_append hprefix tailTrace_7081827
  have hstable : (prefixWord ++ tailWord_7081827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081827).length < 2 ^ (prefixWord ++ tailWord_7081827).sum := by decide
  have hdescent : baseEnd_7081827 < baseStart_7081827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081836 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_7081836 : Nat := 118140960795 + 7081836 * 2 ^ 59
def prefixEnd_7081836 : Nat := 4983230072969 + 3 ^ 40 * 7081836 * 2
def baseEnd_7081836 : Nat := 1212128594771353172593745

theorem tailTrace_7081836 : CollatzResearch.WordTrace tailWord_7081836 prefixEnd_7081836 1212128594771353172593745 := by
  unfold tailWord_7081836
  simp only [CollatzResearch.WordTrace]
  refine ⟨129147889385862564071092681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172197185847816752094790241 129147889385862564071092681)
  ·
    refine ⟨96860917039396923053319511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129147889385862564071092681 96860917039396923053319511)
    ·
      refine ⟨145291375559095384579979267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96860917039396923053319511 145291375559095384579979267)
      ·
        refine ⟨217937063338643076869968901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145291375559095384579979267 217937063338643076869968901)
        ·
          refine ⟨40863199375995576913119169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217937063338643076869968901 40863199375995576913119169)
          ·
            refine ⟨30647399531996682684839377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40863199375995576913119169 30647399531996682684839377)
            ·
              refine ⟨22985549648997512013629533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30647399531996682684839377 22985549648997512013629533)
              ·
                refine ⟨8619581118374067005111075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22985549648997512013629533 8619581118374067005111075)
                ·
                  refine ⟨12929371677561100507666613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619581118374067005111075 12929371677561100507666613)
                  ·
                    refine ⟨1212128594771353172593745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12929371677561100507666613 1212128594771353172593745)
                    ·
                      rfl

theorem cell23_7081836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_7081836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081836 prefixEnd_7081836 := by exact prefixLift 7081836
  have htrace : WordTrace (prefixWord ++ tailWord_7081836) baseStart_7081836 baseEnd_7081836 := by
    simpa [prefixWord, tailWord_7081836, baseEnd_7081836] using wordTrace_append hprefix tailTrace_7081836
  have hstable : (prefixWord ++ tailWord_7081836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081836).length < 2 ^ (prefixWord ++ tailWord_7081836).sum := by decide
  have hdescent : baseEnd_7081836 < baseStart_7081836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081839 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_7081839 : Nat := 118140960795 + 7081839 * 2 ^ 59
def prefixEnd_7081839 : Nat := 4983230072969 + 3 ^ 40 * 7081839 * 2
def baseEnd_7081839 : Nat := 3636387324756023006043721

theorem tailTrace_7081839 : CollatzResearch.WordTrace tailWord_7081839 prefixEnd_7081839 3636387324756023006043721 := by
  unfold tailWord_7081839
  simp only [CollatzResearch.WordTrace]
  refine ⟨258295888190714259654544571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172197258793809506436363047 258295888190714259654544571)
  ·
    refine ⟨387443832286071389481816857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258295888190714259654544571 387443832286071389481816857)
    ·
      refine ⟨290582874214553542111362643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387443832286071389481816857 290582874214553542111362643)
      ·
        refine ⟨435874311321830313167043965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290582874214553542111362643 435874311321830313167043965)
        ·
          refine ⟨163452866745686367437641487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435874311321830313167043965 163452866745686367437641487)
          ·
            refine ⟨245179300118529551156462231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163452866745686367437641487 245179300118529551156462231)
            ·
              refine ⟨367768950177794326734693347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245179300118529551156462231 367768950177794326734693347)
              ·
                refine ⟨551653425266691490102040021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367768950177794326734693347 551653425266691490102040021)
                ·
                  refine ⟨12929377154688081799266563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 551653425266691490102040021 12929377154688081799266563)
                  ·
                    refine ⟨19394065732032122698899845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12929377154688081799266563 19394065732032122698899845)
                    ·
                      refine ⟨3636387324756023006043721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19394065732032122698899845 3636387324756023006043721)
                      ·
                        rfl

theorem cell23_7081839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_7081839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081839 prefixEnd_7081839 := by exact prefixLift 7081839
  have htrace : WordTrace (prefixWord ++ tailWord_7081839) baseStart_7081839 baseEnd_7081839 := by
    simpa [prefixWord, tailWord_7081839, baseEnd_7081839] using wordTrace_append hprefix tailTrace_7081839
  have hstable : (prefixWord ++ tailWord_7081839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081839).length < 2 ^ (prefixWord ++ tailWord_7081839).sum := by decide
  have hdescent : baseEnd_7081839 < baseStart_7081839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081857 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 6]
def baseStart_7081857 : Nat := 118140960795 + 7081857 * 2 ^ 59
def prefixEnd_7081857 : Nat := 4983230072969 + 3 ^ 40 * 7081857 * 2
def baseEnd_7081857 : Nat := 404044063045311548402071

theorem tailTrace_7081857 : CollatzResearch.WordTrace tailWord_7081857 prefixEnd_7081857 404044063045311548402071 := by
  unfold tailWord_7081857
  simp only [CollatzResearch.WordTrace]
  refine ⟨258296544704649048728699825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172197696469766032485799883 258296544704649048728699825)
  ·
    refine ⟨193722408528486786546524869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258296544704649048728699825 193722408528486786546524869)
    ·
      refine ⟨36322951599091272477473413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193722408528486786546524869 36322951599091272477473413)
      ·
        refine ⟨6810553424829613589526265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36322951599091272477473413 6810553424829613589526265)
        ·
          refine ⟨5107915068622210192144699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6810553424829613589526265 5107915068622210192144699)
          ·
            refine ⟨7661872602933315288217049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107915068622210192144699 7661872602933315288217049)
            ·
              refine ⟨5746404452199986466162787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661872602933315288217049 5746404452199986466162787)
              ·
                refine ⟨8619606678299979699244181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746404452199986466162787 8619606678299979699244181)
                ·
                  refine ⟨404044063045311548402071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8619606678299979699244181 404044063045311548402071)
                  ·
                    rfl

theorem cell23_7081857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 6].length) (baseStart_7081857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081857 prefixEnd_7081857 := by exact prefixLift 7081857
  have htrace : WordTrace (prefixWord ++ tailWord_7081857) baseStart_7081857 baseEnd_7081857 := by
    simpa [prefixWord, tailWord_7081857, baseEnd_7081857] using wordTrace_append hprefix tailTrace_7081857
  have hstable : (prefixWord ++ tailWord_7081857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081857).length < 2 ^ (prefixWord ++ tailWord_7081857).sum := by decide
  have hdescent : baseEnd_7081857 < baseStart_7081857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081873 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_7081873 : Nat := 118140960795 + 7081873 * 2 ^ 59
def prefixEnd_7081873 : Nat := 4983230072969 + 3 ^ 40 * 7081873 * 2
def baseEnd_7081873 : Nat := 3636404783098275873018565

theorem tailTrace_7081873 : CollatzResearch.WordTrace tailWord_7081873 prefixEnd_7081873 3636404783098275873018565 := by
  unfold tailWord_7081873
  simp only [CollatzResearch.WordTrace]
  refine ⟨258297128272591083461282273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172198085515060722307521515 258297128272591083461282273)
  ·
    refine ⟨193722846204443312595961705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258297128272591083461282273 193722846204443312595961705)
    ·
      refine ⟨145292134653332484446971279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193722846204443312595961705 145292134653332484446971279)
      ·
        refine ⟨217938201979998726670456919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145292134653332484446971279 217938201979998726670456919)
        ·
          refine ⟨326907302969998090005685379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217938201979998726670456919 326907302969998090005685379)
          ·
            refine ⟨490360954454997135008528069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326907302969998090005685379 490360954454997135008528069)
            ·
              refine ⟨91942678960311962814099013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490360954454997135008528069 91942678960311962814099013)
              ·
                refine ⟨17239252305058493027643565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91942678960311962814099013 17239252305058493027643565)
                ·
                  refine ⟨6464719614396934885366337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17239252305058493027643565 6464719614396934885366337)
                  ·
                    refine ⟨4848539710797701164024753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464719614396934885366337 4848539710797701164024753)
                    ·
                      refine ⟨3636404783098275873018565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848539710797701164024753 3636404783098275873018565)
                      ·
                        rfl

theorem cell23_7081873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_7081873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081873 prefixEnd_7081873 := by exact prefixLift 7081873
  have htrace : WordTrace (prefixWord ++ tailWord_7081873) baseStart_7081873 baseEnd_7081873 := by
    simpa [prefixWord, tailWord_7081873, baseEnd_7081873] using wordTrace_append hprefix tailTrace_7081873
  have hstable : (prefixWord ++ tailWord_7081873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081873).length < 2 ^ (prefixWord ++ tailWord_7081873).sum := by decide
  have hdescent : baseEnd_7081873 < baseStart_7081873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081879 : List Nat := [1, 1, 3, 3, 1, 3, 2, 9]
def baseStart_7081879 : Nat := 118140960795 + 7081879 * 2 ^ 59
def prefixEnd_7081879 : Nat := 4983230072969 + 3 ^ 40 * 7081879 * 2
def baseEnd_7081879 : Nat := 134681772740081587020131

theorem tailTrace_7081879 : CollatzResearch.WordTrace tailWord_7081879 prefixEnd_7081879 134681772740081587020131 := by
  unfold tailWord_7081879
  simp only [CollatzResearch.WordTrace]
  refine ⟨258297347110569346486000691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172198231407046230990667127 258297347110569346486000691)
  ·
    refine ⟨387446020665854019729001037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258297347110569346486000691 387446020665854019729001037)
    ·
      refine ⟨145292257749695257398375389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387446020665854019729001037 145292257749695257398375389)
      ·
        refine ⟨54484596656135721524390771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145292257749695257398375389 54484596656135721524390771)
        ·
          refine ⟨81726894984203582286586157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54484596656135721524390771 81726894984203582286586157)
          ·
            refine ⟨30647585619076343357469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81726894984203582286586157 30647585619076343357469809)
            ·
              refine ⟨22985689214307257518102357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30647585619076343357469809 22985689214307257518102357)
              ·
                refine ⟨134681772740081587020131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22985689214307257518102357 134681772740081587020131)
                ·
                  rfl

theorem cell23_7081879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 9].length) (baseStart_7081879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081879 prefixEnd_7081879 := by exact prefixLift 7081879
  have htrace : WordTrace (prefixWord ++ tailWord_7081879) baseStart_7081879 baseEnd_7081879 := by
    simpa [prefixWord, tailWord_7081879, baseEnd_7081879] using wordTrace_append hprefix tailTrace_7081879
  have hstable : (prefixWord ++ tailWord_7081879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081879).length < 2 ^ (prefixWord ++ tailWord_7081879).sum := by decide
  have hdescent : baseEnd_7081879 < baseStart_7081879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081896 : List Nat := [2, 1, 6, 2, 12]
def baseStart_7081896 : Nat := 118140960795 + 7081896 * 2 ^ 59
def prefixEnd_7081896 : Nat := 4983230072969 + 3 ^ 40 * 7081896 * 2
def baseEnd_7081896 : Nat := 4988225779359848124871

theorem tailTrace_7081896 : CollatzResearch.WordTrace tailWord_7081896 prefixEnd_7081896 4988225779359848124871 := by
  unfold tailWord_7081896
  simp only [CollatzResearch.WordTrace]
  refine ⟨129148983575753879194684771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172198644767671838926246361 129148983575753879194684771)
  ·
    refine ⟨193723475363630818792027157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129148983575753879194684771 193723475363630818792027157)
    ·
      refine ⟨9080787907670194630876273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193723475363630818792027157 9080787907670194630876273)
      ·
        refine ⟨6810590930752645973157205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9080787907670194630876273 6810590930752645973157205)
        ·
          refine ⟨4988225779359848124871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6810590930752645973157205 4988225779359848124871)
          ·
            rfl

theorem cell23_7081896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 12].length) (baseStart_7081896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081896 prefixEnd_7081896 := by exact prefixLift 7081896
  have htrace : WordTrace (prefixWord ++ tailWord_7081896) baseStart_7081896 baseEnd_7081896 := by
    simpa [prefixWord, tailWord_7081896, baseEnd_7081896] using wordTrace_append hprefix tailTrace_7081896
  have hstable : (prefixWord ++ tailWord_7081896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081896).length < 2 ^ (prefixWord ++ tailWord_7081896).sum := by decide
  have hdescent : baseEnd_7081896 < baseStart_7081896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081974 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_7081974 : Nat := 118140960795 + 7081974 * 2 ^ 59
def prefixEnd_7081974 : Nat := 4983230072969 + 3 ^ 40 * 7081974 * 2
def baseEnd_7081974 : Nat := 3636456644644379977855601

theorem tailTrace_7081974 : CollatzResearch.WordTrace tailWord_7081974 prefixEnd_7081974 3636456644644379977855601 := by
  unfold tailWord_7081974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143800752826573606919311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172200541363483451807139317 16143800752826573606919311)
  ·
    refine ⟨24215701129239860410378967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16143800752826573606919311 24215701129239860410378967)
    ·
      refine ⟨36323551693859790615568451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24215701129239860410378967 36323551693859790615568451)
      ·
        refine ⟨54485327540789685923352677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36323551693859790615568451 54485327540789685923352677)
        ·
          refine ⟨10215998913898066110628627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54485327540789685923352677 10215998913898066110628627)
          ·
            refine ⟨15323998370847099165942941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215998913898066110628627 15323998370847099165942941)
            ·
              refine ⟨5746499389067662187228603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15323998370847099165942941 5746499389067662187228603)
              ·
                refine ⟨8619749083601493280842905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746499389067662187228603 8619749083601493280842905)
                ·
                  refine ⟨6464811812701119960632179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8619749083601493280842905 6464811812701119960632179)
                  ·
                    refine ⟨9697217719051679940948269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6464811812701119960632179 9697217719051679940948269)
                    ·
                      refine ⟨3636456644644379977855601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9697217719051679940948269 3636456644644379977855601)
                      ·
                        rfl

theorem cell23_7081974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_7081974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081974 prefixEnd_7081974 := by exact prefixLift 7081974
  have htrace : WordTrace (prefixWord ++ tailWord_7081974) baseStart_7081974 baseEnd_7081974 := by
    simpa [prefixWord, tailWord_7081974, baseEnd_7081974] using wordTrace_append hprefix tailTrace_7081974
  have hstable : (prefixWord ++ tailWord_7081974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081974).length < 2 ^ (prefixWord ++ tailWord_7081974).sum := by decide
  have hdescent : baseEnd_7081974 < baseStart_7081974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7081976 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_7081976 : Nat := 118140960795 + 7081976 * 2 ^ 59
def prefixEnd_7081976 : Nat := 4983230072969 + 3 ^ 40 * 7081976 * 2
def baseEnd_7081976 : Nat := 3636457671605688970030591

theorem tailTrace_7081976 : CollatzResearch.WordTrace tailWord_7081976 prefixEnd_7081976 3636457671605688970030591 := by
  unfold tailWord_7081976
  simp only [CollatzResearch.WordTrace]
  refine ⟨129150442495608966026140891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172200589994145288034854521 129150442495608966026140891)
  ·
    refine ⟨193725663743413449039211337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129150442495608966026140891 193725663743413449039211337)
    ·
      refine ⟨145294247807560086779408503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193725663743413449039211337 145294247807560086779408503)
      ·
        refine ⟨217941371711340130169112755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145294247807560086779408503 217941371711340130169112755)
        ·
          refine ⟨326912057567010195253669133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217941371711340130169112755 326912057567010195253669133)
          ·
            refine ⟨122592021587628823220125925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326912057567010195253669133 122592021587628823220125925)
            ·
              refine ⟨22986004047680404353773611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122592021587628823220125925 22986004047680404353773611)
              ·
                refine ⟨34479006071520606530660417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22986004047680404353773611 34479006071520606530660417)
                ·
                  refine ⟨25859254553640454897995313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34479006071520606530660417 25859254553640454897995313)
                  ·
                    refine ⟨19394440915230341173496485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25859254553640454897995313 19394440915230341173496485)
                    ·
                      refine ⟨3636457671605688970030591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19394440915230341173496485 3636457671605688970030591)
                      ·
                        rfl

theorem cell23_7081976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_7081976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7081976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7081976 prefixEnd_7081976 := by exact prefixLift 7081976
  have htrace : WordTrace (prefixWord ++ tailWord_7081976) baseStart_7081976 baseEnd_7081976 := by
    simpa [prefixWord, tailWord_7081976, baseEnd_7081976] using wordTrace_append hprefix tailTrace_7081976
  have hstable : (prefixWord ++ tailWord_7081976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7081976).length < 2 ^ (prefixWord ++ tailWord_7081976).sum := by decide
  have hdescent : baseEnd_7081976 < baseStart_7081976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7081976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082003 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 5]
def baseStart_7082003 : Nat := 118140960795 + 7082003 * 2 ^ 59
def prefixEnd_7082003 : Nat := 4983230072969 + 3 ^ 40 * 7082003 * 2
def baseEnd_7082003 : Nat := 404052392842595596043663

theorem tailTrace_7082003 : CollatzResearch.WordTrace tailWord_7082003 prefixEnd_7082003 404052392842595596043663 := by
  unfold tailWord_7082003
  simp only [CollatzResearch.WordTrace]
  refine ⟨258301869762120115663514663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172201246508080077109009775 258301869762120115663514663)
  ·
    refine ⟨387452804643180173495271995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258301869762120115663514663 387452804643180173495271995)
    ·
      refine ⟨581179206964770260242907993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387452804643180173495271995 581179206964770260242907993)
      ·
        refine ⟨435884405223577695182180995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581179206964770260242907993 435884405223577695182180995)
        ·
          refine ⟨653826607835366542773271493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435884405223577695182180995 653826607835366542773271493)
          ·
            refine ⟨122592488969131226769988405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 653826607835366542773271493 122592488969131226769988405)
            ·
              refine ⟨11493045840856052509686413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122592488969131226769988405 11493045840856052509686413)
              ·
                refine ⟨4309892190321019691132405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11493045840856052509686413 4309892190321019691132405)
                ·
                  refine ⟨404052392842595596043663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309892190321019691132405 404052392842595596043663)
                  ·
                    rfl

theorem cell23_7082003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 5].length) (baseStart_7082003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082003 prefixEnd_7082003 := by exact prefixLift 7082003
  have htrace : WordTrace (prefixWord ++ tailWord_7082003) baseStart_7082003 baseEnd_7082003 := by
    simpa [prefixWord, tailWord_7082003, baseEnd_7082003] using wordTrace_append hprefix tailTrace_7082003
  have hstable : (prefixWord ++ tailWord_7082003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082003).length < 2 ^ (prefixWord ++ tailWord_7082003).sum := by decide
  have hdescent : baseEnd_7082003 < baseStart_7082003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082020 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 7]
def baseStart_7082020 : Nat := 118140960795 + 7082020 * 2 ^ 59
def prefixEnd_7082020 : Nat := 4983230072969 + 3 ^ 40 * 7082020 * 2
def baseEnd_7082020 : Nat := 404053362750498533097821

theorem tailTrace_7082020 : CollatzResearch.WordTrace tailWord_7082020 prefixEnd_7082020 404053362750498533097821 := by
  unfold tailWord_7082020
  simp only [CollatzResearch.WordTrace]
  refine ⟨129151244901529263783441757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172201659868705685044589009 129151244901529263783441757)
  ·
    refine ⟨48431716838073473918790659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129151244901529263783441757 48431716838073473918790659)
    ·
      refine ⟨72647575257110210878185989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48431716838073473918790659 72647575257110210878185989)
      ·
        refine ⟨13621420360708164539659873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72647575257110210878185989 13621420360708164539659873)
        ·
          refine ⟨10216065270531123404744905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621420360708164539659873 10216065270531123404744905)
          ·
            refine ⟨7662048952898342553558679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10216065270531123404744905 7662048952898342553558679)
            ·
              refine ⟨11493073429347513830338019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662048952898342553558679 11493073429347513830338019)
              ·
                refine ⟨17239610144021270745507029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493073429347513830338019 17239610144021270745507029)
                ·
                  refine ⟨404053362750498533097821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17239610144021270745507029 404053362750498533097821)
                  ·
                    rfl

theorem cell23_7082020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_7082020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082020 prefixEnd_7082020 := by exact prefixLift 7082020
  have htrace : WordTrace (prefixWord ++ tailWord_7082020) baseStart_7082020 baseEnd_7082020 := by
    simpa [prefixWord, tailWord_7082020, baseEnd_7082020] using wordTrace_append hprefix tailTrace_7082020
  have hstable : (prefixWord ++ tailWord_7082020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082020).length < 2 ^ (prefixWord ++ tailWord_7082020).sum := by decide
  have hdescent : baseEnd_7082020 < baseStart_7082020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082053 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_7082053 : Nat := 118140960795 + 7082053 * 2 ^ 59
def prefixEnd_7082053 : Nat := 4983230072969 + 3 ^ 40 * 7082053 * 2
def baseEnd_7082053 : Nat := 3636497209616085168767737

theorem tailTrace_7082053 : CollatzResearch.WordTrace tailWord_7082053 prefixEnd_7082053 3636497209616085168767737 := by
  unfold tailWord_7082053
  simp only [CollatzResearch.WordTrace]
  refine ⟨258303693411938974202834813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172202462274625982801889875 258303693411938974202834813)
  ·
    refine ⟨96863885029477115326063055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258303693411938974202834813 96863885029477115326063055)
    ·
      refine ⟨145295827544215672989094583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96863885029477115326063055 145295827544215672989094583)
      ·
        refine ⟨217943741316323509483641875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145295827544215672989094583 217943741316323509483641875)
        ·
          refine ⟨326915611974485264225462813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217943741316323509483641875 326915611974485264225462813)
          ·
            refine ⟨122593354490431974084548555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326915611974485264225462813 122593354490431974084548555)
            ·
              refine ⟨183890031735647961126822833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122593354490431974084548555 183890031735647961126822833)
              ·
                refine ⟨137917523801735970845117125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183890031735647961126822833 137917523801735970845117125)
                ·
                  refine ⟨25859535712825494533459461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137917523801735970845117125 25859535712825494533459461)
                  ·
                    refine ⟨4848662946154780225023649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25859535712825494533459461 4848662946154780225023649)
                    ·
                      refine ⟨3636497209616085168767737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848662946154780225023649 3636497209616085168767737)
                      ·
                        rfl

theorem cell23_7082053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_7082053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082053 prefixEnd_7082053 := by exact prefixLift 7082053
  have htrace : WordTrace (prefixWord ++ tailWord_7082053) baseStart_7082053 baseEnd_7082053 := by
    simpa [prefixWord, tailWord_7082053, baseEnd_7082053] using wordTrace_append hprefix tailTrace_7082053
  have hstable : (prefixWord ++ tailWord_7082053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082053).length < 2 ^ (prefixWord ++ tailWord_7082053).sum := by decide
  have hdescent : baseEnd_7082053 < baseStart_7082053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082073 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_7082073 : Nat := 118140960795 + 7082073 * 2 ^ 59
def prefixEnd_7082073 : Nat := 4983230072969 + 3 ^ 40 * 7082073 * 2
def baseEnd_7082073 : Nat := 3636507479229175090517645

theorem tailTrace_7082073 : CollatzResearch.WordTrace tailWord_7082073 prefixEnd_7082073 3636507479229175090517645 := by
  unfold tailWord_7082073
  simp only [CollatzResearch.WordTrace]
  refine ⟨258304422871866517618562873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172202948581244345079041915 258304422871866517618562873)
  ·
    refine ⟨193728317153899888213922155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258304422871866517618562873 193728317153899888213922155)
    ·
      refine ⟨290592475730849832320883233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193728317153899888213922155 290592475730849832320883233)
      ·
        refine ⟨217944356798137374240662425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290592475730849832320883233 217944356798137374240662425)
        ·
          refine ⟨163458267598603030680496819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217944356798137374240662425 163458267598603030680496819)
          ·
            refine ⟨245187401397904546020745229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163458267598603030680496819 245187401397904546020745229)
            ·
              refine ⟨91945275524214204757779461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245187401397904546020745229 91945275524214204757779461)
              ·
                refine ⟨17239739160790163392083649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91945275524214204757779461 17239739160790163392083649)
                ·
                  refine ⟨12929804370592622544062737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17239739160790163392083649 12929804370592622544062737)
                  ·
                    refine ⟨9697353277944466908047053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12929804370592622544062737 9697353277944466908047053)
                    ·
                      refine ⟨3636507479229175090517645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9697353277944466908047053 3636507479229175090517645)
                      ·
                        rfl

theorem cell23_7082073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_7082073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082073 prefixEnd_7082073 := by exact prefixLift 7082073
  have htrace : WordTrace (prefixWord ++ tailWord_7082073) baseStart_7082073 baseEnd_7082073 := by
    simpa [prefixWord, tailWord_7082073, baseEnd_7082073] using wordTrace_append hprefix tailTrace_7082073
  have hstable : (prefixWord ++ tailWord_7082073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082073).length < 2 ^ (prefixWord ++ tailWord_7082073).sum := by decide
  have hdescent : baseEnd_7082073 < baseStart_7082073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082093 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 6]
def baseStart_7082093 : Nat := 118140960795 + 7082093 * 2 ^ 59
def prefixEnd_7082093 : Nat := 4983230072969 + 3 ^ 40 * 7082093 * 2
def baseEnd_7082093 : Nat := 404057527649140556918617

theorem tailTrace_7082093 : CollatzResearch.WordTrace tailWord_7082093 prefixEnd_7082093 404057527649140556918617 := by
  unfold tailWord_7082093
  simp only [CollatzResearch.WordTrace]
  refine ⟨258305152331794061034290933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172203434887862707356193955 258305152331794061034290933)
  ·
    refine ⟨24216108031105693221964775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258305152331794061034290933 24216108031105693221964775)
    ·
      refine ⟨36324162046658539832947163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24216108031105693221964775 36324162046658539832947163)
      ·
        refine ⟨54486243069987809749420745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36324162046658539832947163 54486243069987809749420745)
        ·
          refine ⟨40864682302490857312065559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54486243069987809749420745 40864682302490857312065559)
          ·
            refine ⟨61297023453736285968098339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40864682302490857312065559 61297023453736285968098339)
            ·
              refine ⟨91945535180604428952147509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61297023453736285968098339 91945535180604428952147509)
              ·
                refine ⟨8619893923181665214263829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91945535180604428952147509 8619893923181665214263829)
                ·
                  refine ⟨404057527649140556918617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8619893923181665214263829 404057527649140556918617)
                  ·
                    rfl

theorem cell23_7082093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_7082093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082093 prefixEnd_7082093 := by exact prefixLift 7082093
  have htrace : WordTrace (prefixWord ++ tailWord_7082093) baseStart_7082093 baseEnd_7082093 := by
    simpa [prefixWord, tailWord_7082093, baseEnd_7082093] using wordTrace_append hprefix tailTrace_7082093
  have hstable : (prefixWord ++ tailWord_7082093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082093).length < 2 ^ (prefixWord ++ tailWord_7082093).sum := by decide
  have hdescent : baseEnd_7082093 < baseStart_7082093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082157 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7082157 : Nat := 118140960795 + 7082157 * 2 ^ 59
def prefixEnd_7082157 : Nat := 4983230072969 + 3 ^ 40 * 7082157 * 2
def baseEnd_7082157 : Nat := 1212183537201384253955753

theorem tailTrace_7082157 : CollatzResearch.WordTrace tailWord_7082157 prefixEnd_7082157 1212183537201384253955753 := by
  unfold tailWord_7082157
  simp only [CollatzResearch.WordTrace]
  refine ⟨258307486603562199964620725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172204991069041466643080483 258307486603562199964620725)
  ·
    refine ⟨24216326869083956246683193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258307486603562199964620725 24216326869083956246683193)
    ·
      refine ⟨18162245151812967185012395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24216326869083956246683193 18162245151812967185012395)
      ·
        refine ⟨27243367727719450777518593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18162245151812967185012395 27243367727719450777518593)
        ·
          refine ⟨20432525795789588083138945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27243367727719450777518593 20432525795789588083138945)
          ·
            refine ⟨15324394346842191062354209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20432525795789588083138945 15324394346842191062354209)
            ·
              refine ⟨11493295760131643296765657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15324394346842191062354209 11493295760131643296765657)
              ·
                refine ⟨8619971820098732472574243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11493295760131643296765657 8619971820098732472574243)
                ·
                  refine ⟨12929957730148098708861365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619971820098732472574243 12929957730148098708861365)
                  ·
                    refine ⟨1212183537201384253955753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12929957730148098708861365 1212183537201384253955753)
                    ·
                      rfl

theorem cell23_7082157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7082157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082157 prefixEnd_7082157 := by exact prefixLift 7082157
  have htrace : WordTrace (prefixWord ++ tailWord_7082157) baseStart_7082157 baseEnd_7082157 := by
    simpa [prefixWord, tailWord_7082157, baseEnd_7082157] using wordTrace_append hprefix tailTrace_7082157
  have hstable : (prefixWord ++ tailWord_7082157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082157).length < 2 ^ (prefixWord ++ tailWord_7082157).sum := by decide
  have hdescent : baseEnd_7082157 < baseStart_7082157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082173 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7082173 : Nat := 118140960795 + 7082173 * 2 ^ 59
def prefixEnd_7082173 : Nat := 4983230072969 + 3 ^ 40 * 7082173 * 2
def baseEnd_7082173 : Nat := 3636558827294624699267185

theorem tailTrace_7082173 : CollatzResearch.WordTrace tailWord_7082173 prefixEnd_7082173 3636558827294624699267185 := by
  unfold tailWord_7082173
  simp only [CollatzResearch.WordTrace]
  refine ⟨258308070171504234697203173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172205380114336156464802115 258308070171504234697203173)
  ·
    refine ⟨48432763157157044005725595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258308070171504234697203173 48432763157157044005725595)
    ·
      refine ⟨72649144735735566008588393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48432763157157044005725595 72649144735735566008588393)
      ·
        refine ⟨54486858551801674506441295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72649144735735566008588393 54486858551801674506441295)
        ·
          refine ⟨81730287827702511759661943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54486858551801674506441295 81730287827702511759661943)
          ·
            refine ⟨122595431741553767639492915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81730287827702511759661943 122595431741553767639492915)
            ·
              refine ⟨183893147612330651459239373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122595431741553767639492915 183893147612330651459239373)
              ·
                refine ⟨68959930354623994297214765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183893147612330651459239373 68959930354623994297214765)
                ·
                  refine ⟨25859973882983997861455537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68959930354623994297214765 25859973882983997861455537)
                  ·
                    refine ⟨19394980412237998396091653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25859973882983997861455537 19394980412237998396091653)
                    ·
                      refine ⟨3636558827294624699267185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19394980412237998396091653 3636558827294624699267185)
                      ·
                        rfl

theorem cell23_7082173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7082173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082173 prefixEnd_7082173 := by exact prefixLift 7082173
  have htrace : WordTrace (prefixWord ++ tailWord_7082173) baseStart_7082173 baseEnd_7082173 := by
    simpa [prefixWord, tailWord_7082173, baseEnd_7082173] using wordTrace_append hprefix tailTrace_7082173
  have hstable : (prefixWord ++ tailWord_7082173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082173).length < 2 ^ (prefixWord ++ tailWord_7082173).sum := by decide
  have hdescent : baseEnd_7082173 < baseStart_7082173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082180 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7082180 : Nat := 118140960795 + 7082180 * 2 ^ 59
def prefixEnd_7082180 : Nat := 4983230072969 + 3 ^ 40 * 7082180 * 2
def baseEnd_7082180 : Nat := 3636562421659206171879653

theorem tailTrace_7082180 : CollatzResearch.WordTrace tailWord_7082180 prefixEnd_7082180 3636562421659206171879653 := by
  unfold tailWord_7082180
  simp only [CollatzResearch.WordTrace]
  refine ⟨129154162741239437446353997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172205550321652583261805329 129154162741239437446353997)
  ·
    refine ⟨48432811027964789042382749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129154162741239437446353997 48432811027964789042382749)
    ·
      refine ⟨18162304135486795890893531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48432811027964789042382749 18162304135486795890893531)
      ·
        refine ⟨27243456203230193836340297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18162304135486795890893531 27243456203230193836340297)
        ·
          refine ⟨20432592152422645377255223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27243456203230193836340297 20432592152422645377255223)
          ·
            refine ⟨30648888228633968065882835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20432592152422645377255223 30648888228633968065882835)
            ·
              refine ⟨45973332342950952098824253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30648888228633968065882835 45973332342950952098824253)
              ·
                refine ⟨17239999628606607037059095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45973332342950952098824253 17239999628606607037059095)
                ·
                  refine ⟨25859999442909910555588643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17239999628606607037059095 25859999442909910555588643)
                  ·
                    refine ⟨38789999164364865833382965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25859999442909910555588643 38789999164364865833382965)
                    ·
                      refine ⟨3636562421659206171879653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38789999164364865833382965 3636562421659206171879653)
                      ·
                        rfl

theorem cell23_7082180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7082180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082180 prefixEnd_7082180 := by exact prefixLift 7082180
  have htrace : WordTrace (prefixWord ++ tailWord_7082180) baseStart_7082180 baseEnd_7082180 := by
    simpa [prefixWord, tailWord_7082180, baseEnd_7082180] using wordTrace_append hprefix tailTrace_7082180
  have hstable : (prefixWord ++ tailWord_7082180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082180).length < 2 ^ (prefixWord ++ tailWord_7082180).sum := by decide
  have hdescent : baseEnd_7082180 < baseStart_7082180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082188 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7082188 : Nat := 118140960795 + 7082188 * 2 ^ 59
def prefixEnd_7082188 : Nat := 4983230072969 + 3 ^ 40 * 7082188 * 2
def baseEnd_7082188 : Nat := 3636566529504442140579617

theorem tailTrace_7082188 : CollatzResearch.WordTrace tailWord_7082188 prefixEnd_7082188 3636566529504442140579617 := by
  unfold tailWord_7082188
  simp only [CollatzResearch.WordTrace]
  refine ⟨129154308633224946129499609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172205744844299928172666145 129154308633224946129499609)
  ·
    refine ⟨96865731474918709597124707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129154308633224946129499609 96865731474918709597124707)
    ·
      refine ⟨145298597212378064395687061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96865731474918709597124707 145298597212378064395687061)
      ·
        refine ⟨6810871744330221768547831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145298597212378064395687061 6810871744330221768547831)
        ·
          refine ⟨10216307616495332652821747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810871744330221768547831 10216307616495332652821747)
          ·
            refine ⟨15324461424742998979232621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216307616495332652821747 15324461424742998979232621)
            ·
              refine ⟨5746673034278624617212233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15324461424742998979232621 5746673034278624617212233)
              ·
                refine ⟨4310004775708968462909175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746673034278624617212233 4310004775708968462909175)
                ·
                  refine ⟨6465007163563452694363763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310004775708968462909175 6465007163563452694363763)
                  ·
                    refine ⟨9697510745345179041545645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6465007163563452694363763 9697510745345179041545645)
                    ·
                      refine ⟨3636566529504442140579617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9697510745345179041545645 3636566529504442140579617)
                      ·
                        rfl

theorem cell23_7082188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7082188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082188 prefixEnd_7082188 := by exact prefixLift 7082188
  have htrace : WordTrace (prefixWord ++ tailWord_7082188) baseStart_7082188 baseEnd_7082188 := by
    simpa [prefixWord, tailWord_7082188, baseEnd_7082188] using wordTrace_append hprefix tailTrace_7082188
  have hstable : (prefixWord ++ tailWord_7082188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082188).length < 2 ^ (prefixWord ++ tailWord_7082188).sum := by decide
  have hdescent : baseEnd_7082188 < baseStart_7082188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082194 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7082194 : Nat := 118140960795 + 7082194 * 2 ^ 59
def prefixEnd_7082194 : Nat := 4983230072969 + 3 ^ 40 * 7082194 * 2
def baseEnd_7082194 : Nat := 3636569610388369117104589

theorem tailTrace_7082194 : CollatzResearch.WordTrace tailWord_7082194 prefixEnd_7082194 3636569610388369117104589 := by
  unfold tailWord_7082194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64577209026107038820929409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172205890736285436855811757 64577209026107038820929409)
  ·
    refine ⟨48432906769580279115697057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64577209026107038820929409 48432906769580279115697057)
    ·
      refine ⟨36324680077185209336772793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48432906769580279115697057 36324680077185209336772793)
      ·
        refine ⟨27243510057888907002579595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36324680077185209336772793 27243510057888907002579595)
        ·
          refine ⟨40865265086833360503869393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27243510057888907002579595 40865265086833360503869393)
          ·
            refine ⟨30648948815125020377902045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40865265086833360503869393 30648948815125020377902045)
            ·
              refine ⟨11493355805671882641713267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30648948815125020377902045 11493355805671882641713267)
              ·
                refine ⟨17240033708507823962569901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493355805671882641713267 17240033708507823962569901)
                ·
                  refine ⟨6465012640690433985963713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17240033708507823962569901 6465012640690433985963713)
                  ·
                    refine ⟨4848759480517825489472785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465012640690433985963713 4848759480517825489472785)
                    ·
                      refine ⟨3636569610388369117104589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848759480517825489472785 3636569610388369117104589)
                      ·
                        rfl

theorem cell23_7082194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7082194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082194 prefixEnd_7082194 := by exact prefixLift 7082194
  have htrace : WordTrace (prefixWord ++ tailWord_7082194) baseStart_7082194 baseEnd_7082194 := by
    simpa [prefixWord, tailWord_7082194, baseEnd_7082194] using wordTrace_append hprefix tailTrace_7082194
  have hstable : (prefixWord ++ tailWord_7082194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082194).length < 2 ^ (prefixWord ++ tailWord_7082194).sum := by decide
  have hdescent : baseEnd_7082194 < baseStart_7082194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082211 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7082211 : Nat := 118140960795 + 7082211 * 2 ^ 59
def prefixEnd_7082211 : Nat := 4983230072969 + 3 ^ 40 * 7082211 * 2
def baseEnd_7082211 : Nat := 3636578339559495550592011

theorem tailTrace_7082211 : CollatzResearch.WordTrace tailWord_7082211 prefixEnd_7082211 3636578339559495550592011 := by
  unfold tailWord_7082211
  simp only [CollatzResearch.WordTrace]
  refine ⟨258309456145366567187086487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172206304096911044791390991 258309456145366567187086487)
  ·
    refine ⟨387464184218049850780629731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258309456145366567187086487 387464184218049850780629731)
    ·
      refine ⟨581196276327074776170944597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387464184218049850780629731 581196276327074776170944597)
      ·
        refine ⟨6810893863207907533253257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 581196276327074776170944597 6810893863207907533253257)
        ·
          refine ⟨5108170397405930649939943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6810893863207907533253257 5108170397405930649939943)
          ·
            refine ⟨7662255596108895974909915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5108170397405930649939943 7662255596108895974909915)
            ·
              refine ⟨11493383394163343962364873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662255596108895974909915 11493383394163343962364873)
              ·
                refine ⟨8620037545622507971773655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11493383394163343962364873 8620037545622507971773655)
                ·
                  refine ⟨12930056318433761957660483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620037545622507971773655 12930056318433761957660483)
                  ·
                    refine ⟨19395084477650642936490725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12930056318433761957660483 19395084477650642936490725)
                    ·
                      refine ⟨3636578339559495550592011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19395084477650642936490725 3636578339559495550592011)
                      ·
                        rfl

theorem cell23_7082211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7082211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082211 prefixEnd_7082211 := by exact prefixLift 7082211
  have htrace : WordTrace (prefixWord ++ tailWord_7082211) baseStart_7082211 baseEnd_7082211 := by
    simpa [prefixWord, tailWord_7082211, baseEnd_7082211] using wordTrace_append hprefix tailTrace_7082211
  have hstable : (prefixWord ++ tailWord_7082211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082211).length < 2 ^ (prefixWord ++ tailWord_7082211).sum := by decide
  have hdescent : baseEnd_7082211 < baseStart_7082211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082237 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_7082237 : Nat := 118140960795 + 7082237 * 2 ^ 59
def prefixEnd_7082237 : Nat := 4983230072969 + 3 ^ 40 * 7082237 * 2
def baseEnd_7082237 : Nat := 3636591690056512448866891

theorem tailTrace_7082237 : CollatzResearch.WordTrace tailWord_7082237 prefixEnd_7082237 3636591690056512448866891 := by
  unfold tailWord_7082237
  simp only [CollatzResearch.WordTrace]
  refine ⟨258310404443272373627532965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172206936295514915751688643 258310404443272373627532965)
  ·
    refine ⟨48433200833113570055162431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258310404443272373627532965 48433200833113570055162431)
    ·
      refine ⟨72649801249670355082743647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48433200833113570055162431 72649801249670355082743647)
      ·
        refine ⟨108974701874505532624115471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72649801249670355082743647 108974701874505532624115471)
        ·
          refine ⟨163462052811758298936173207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108974701874505532624115471 163462052811758298936173207)
          ·
            refine ⟨245193079217637448404259811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163462052811758298936173207 245193079217637448404259811)
            ·
              refine ⟨367789618826456172606389717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245193079217637448404259811 367789618826456172606389717)
              ·
                refine ⟨8620069191245066545462259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367789618826456172606389717 8620069191245066545462259)
                ·
                  refine ⟨12930103786867599818193389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620069191245066545462259 12930103786867599818193389)
                  ·
                    refine ⟨4848788920075349931822521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12930103786867599818193389 4848788920075349931822521)
                    ·
                      refine ⟨3636591690056512448866891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848788920075349931822521 3636591690056512448866891)
                      ·
                        rfl

theorem cell23_7082237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_7082237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082237 prefixEnd_7082237 := by exact prefixLift 7082237
  have htrace : WordTrace (prefixWord ++ tailWord_7082237) baseStart_7082237 baseEnd_7082237 := by
    simpa [prefixWord, tailWord_7082237, baseEnd_7082237] using wordTrace_append hprefix tailTrace_7082237
  have hstable : (prefixWord ++ tailWord_7082237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082237).length < 2 ^ (prefixWord ++ tailWord_7082237).sum := by decide
  have hdescent : baseEnd_7082237 < baseStart_7082237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082243 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 2, 6]
def baseStart_7082243 : Nat := 118140960795 + 7082243 * 2 ^ 59
def prefixEnd_7082243 : Nat := 4983230072969 + 3 ^ 40 * 7082243 * 2
def baseEnd_7082243 : Nat := 1212198256980146475130621

theorem tailTrace_7082243 : CollatzResearch.WordTrace tailWord_7082243 prefixEnd_7082243 1212198256980146475130621 := by
  unfold tailWord_7082243
  simp only [CollatzResearch.WordTrace]
  refine ⟨258310623281250636652251383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172207082187500424434834255 258310623281250636652251383)
  ·
    refine ⟨387465934921875954978377075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258310623281250636652251383 387465934921875954978377075)
    ·
      refine ⟨581198902382813932467565613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387465934921875954978377075 581198902382813932467565613)
      ·
        refine ⟨217949588393555224675337105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581198902382813932467565613 217949588393555224675337105)
        ·
          refine ⟨163462191295166418506502829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217949588393555224675337105 163462191295166418506502829)
          ·
            refine ⟨61298321735687406939938561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163462191295166418506502829 61298321735687406939938561)
            ·
              refine ⟨45973741301765555204953921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61298321735687406939938561 45973741301765555204953921)
              ·
                refine ⟨34480305976324166403715441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45973741301765555204953921 34480305976324166403715441)
                ·
                  refine ⟨25860229482243124802786581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34480305976324166403715441 25860229482243124802786581)
                  ·
                    refine ⟨1212198256980146475130621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25860229482243124802786581 1212198256980146475130621)
                    ·
                      rfl

theorem cell23_7082243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_7082243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082243 prefixEnd_7082243 := by exact prefixLift 7082243
  have htrace : WordTrace (prefixWord ++ tailWord_7082243) baseStart_7082243 baseEnd_7082243 := by
    simpa [prefixWord, tailWord_7082243, baseEnd_7082243] using wordTrace_append hprefix tailTrace_7082243
  have hstable : (prefixWord ++ tailWord_7082243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082243).length < 2 ^ (prefixWord ++ tailWord_7082243).sum := by decide
  have hdescent : baseEnd_7082243 < baseStart_7082243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082273 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 9]
def baseStart_7082273 : Nat := 118140960795 + 7082273 * 2 ^ 59
def prefixEnd_7082273 : Nat := 4983230072969 + 3 ^ 40 * 7082273 * 2
def baseEnd_7082273 : Nat := 404067797262230478668525

theorem tailTrace_7082273 : CollatzResearch.WordTrace tailWord_7082273 prefixEnd_7082273 404067797262230478668525 := by
  unfold tailWord_7082273
  simp only [CollatzResearch.WordTrace]
  refine ⟨258311717471141951775843473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172207811647427967850562315 258311717471141951775843473)
  ·
    refine ⟨193733788103356463831882605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258311717471141951775843473 193733788103356463831882605)
    ·
      refine ⟨72650170538758673936955977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193733788103356463831882605 72650170538758673936955977)
      ·
        refine ⟨54487627904069005452716983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72650170538758673936955977 54487627904069005452716983)
        ·
          refine ⟨81731441856103508179075475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54487627904069005452716983 81731441856103508179075475)
          ·
            refine ⟨122597162784155262268613213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81731441856103508179075475 122597162784155262268613213)
            ·
              refine ⟨45973936044058223350729955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122597162784155262268613213 45973936044058223350729955)
              ·
                refine ⟨68960904066087335026094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45973936044058223350729955 68960904066087335026094933)
                ·
                  refine ⟨404067797262230478668525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68960904066087335026094933 404067797262230478668525)
                  ·
                    rfl

theorem cell23_7082273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_7082273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082273 prefixEnd_7082273 := by exact prefixLift 7082273
  have htrace : WordTrace (prefixWord ++ tailWord_7082273) baseStart_7082273 baseEnd_7082273 := by
    simpa [prefixWord, tailWord_7082273, baseEnd_7082273] using wordTrace_append hprefix tailTrace_7082273
  have hstable : (prefixWord ++ tailWord_7082273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082273).length < 2 ^ (prefixWord ++ tailWord_7082273).sum := by decide
  have hdescent : baseEnd_7082273 < baseStart_7082273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082300 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_7082300 : Nat := 118140960795 + 7082300 * 2 ^ 59
def prefixEnd_7082300 : Nat := 4983230072969 + 3 ^ 40 * 7082300 * 2
def baseEnd_7082300 : Nat := 3636624039337745702379101

theorem tailTrace_7082300 : CollatzResearch.WordTrace tailWord_7082300 prefixEnd_7082300 3636624039337745702379101 := by
  unfold tailWord_7082300
  simp only [CollatzResearch.WordTrace]
  refine ⟨129156351121022067693538177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172208468161362756924717569 129156351121022067693538177)
  ·
    refine ⟨96867263340766550770153633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129156351121022067693538177 96867263340766550770153633)
    ·
      refine ⟨72650447505574913077615225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96867263340766550770153633 72650447505574913077615225)
      ·
        refine ⟨54487835629181184808211419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72650447505574913077615225 54487835629181184808211419)
        ·
          refine ⟨81731753443771777212317129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54487835629181184808211419 81731753443771777212317129)
          ·
            refine ⟨61298815082828832909237847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81731753443771777212317129 61298815082828832909237847)
            ·
              refine ⟨91948222624243249363856771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61298815082828832909237847 91948222624243249363856771)
              ·
                refine ⟨137922333936364874045785157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91948222624243249363856771 137922333936364874045785157)
                ·
                  refine ⟨25860437613068413883584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137922333936364874045785157 25860437613068413883584717)
                  ·
                    refine ⟨9697664104900655206344269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25860437613068413883584717 9697664104900655206344269)
                    ·
                      refine ⟨3636624039337745702379101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9697664104900655206344269 3636624039337745702379101)
                      ·
                        rfl

theorem cell23_7082300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_7082300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082300 prefixEnd_7082300 := by exact prefixLift 7082300
  have htrace : WordTrace (prefixWord ++ tailWord_7082300) baseStart_7082300 baseEnd_7082300 := by
    simpa [prefixWord, tailWord_7082300, baseEnd_7082300] using wordTrace_append hprefix tailTrace_7082300
  have hstable : (prefixWord ++ tailWord_7082300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082300).length < 2 ^ (prefixWord ++ tailWord_7082300).sum := by decide
  have hdescent : baseEnd_7082300 < baseStart_7082300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082313 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_7082313 : Nat := 118140960795 + 7082313 * 2 ^ 59
def prefixEnd_7082313 : Nat := 4983230072969 + 3 ^ 40 * 7082313 * 2
def baseEnd_7082313 : Nat := 3636630714586254151516541

theorem tailTrace_7082313 : CollatzResearch.WordTrace tailWord_7082313 prefixEnd_7082313 3636630714586254151516541 := by
  unfold tailWord_7082313
  simp only [CollatzResearch.WordTrace]
  refine ⟨258313176390997038607299593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172208784260664692404866395 258313176390997038607299593)
  ·
    refine ⟨193734882293247778955474695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258313176390997038607299593 193734882293247778955474695)
    ·
      refine ⟨290602323439871668433212043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193734882293247778955474695 290602323439871668433212043)
      ·
        refine ⟨435903485159807502649818065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290602323439871668433212043 435903485159807502649818065)
        ·
          refine ⟨326927613869855626987363549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435903485159807502649818065 326927613869855626987363549)
          ·
            refine ⟨122597855201195860120261331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326927613869855626987363549 122597855201195860120261331)
            ·
              refine ⟨183896782801793790180391997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122597855201195860120261331 183896782801793790180391997)
              ·
                refine ⟨68961293550672671317646999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183896782801793790180391997 68961293550672671317646999)
                ·
                  refine ⟨103441940326009006976470499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68961293550672671317646999 103441940326009006976470499)
                  ·
                    refine ⟨155162910489013510464705749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103441940326009006976470499 155162910489013510464705749)
                    ·
                      refine ⟨3636630714586254151516541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155162910489013510464705749 3636630714586254151516541)
                      ·
                        rfl

theorem cell23_7082313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_7082313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082313 prefixEnd_7082313 := by exact prefixLift 7082313
  have htrace : WordTrace (prefixWord ++ tailWord_7082313) baseStart_7082313 baseEnd_7082313 := by
    simpa [prefixWord, tailWord_7082313, baseEnd_7082313] using wordTrace_append hprefix tailTrace_7082313
  have hstable : (prefixWord ++ tailWord_7082313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082313).length < 2 ^ (prefixWord ++ tailWord_7082313).sum := by decide
  have hdescent : baseEnd_7082313 < baseStart_7082313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082340 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_7082340 : Nat := 118140960795 + 7082340 * 2 ^ 59
def prefixEnd_7082340 : Nat := 4983230072969 + 3 ^ 40 * 7082340 * 2
def baseEnd_7082340 : Nat := 3636644578563925545878917

theorem tailTrace_7082340 : CollatzResearch.WordTrace tailWord_7082340 prefixEnd_7082340 3636644578563925545878917 := by
  unfold tailWord_7082340
  simp only [CollatzResearch.WordTrace]
  refine ⟨129157080580949611109266237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172209440774599481479021649 129157080580949611109266237)
  ·
    refine ⟨48433905217856104165974839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129157080580949611109266237 48433905217856104165974839)
    ·
      refine ⟨72650857826784156248962259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48433905217856104165974839 72650857826784156248962259)
      ·
        refine ⟨108976286740176234373443389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72650857826784156248962259 108976286740176234373443389)
        ·
          refine ⟨40866107527566087890041271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108976286740176234373443389 40866107527566087890041271)
          ·
            refine ⟨61299161291349131835061907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40866107527566087890041271 61299161291349131835061907)
            ·
              refine ⟨91948741937023697752592861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61299161291349131835061907 91948741937023697752592861)
              ·
                refine ⟨34480778226383886657222323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91948741937023697752592861 34480778226383886657222323)
                ·
                  refine ⟨51721167339575829985833485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34480778226383886657222323 51721167339575829985833485)
                  ·
                    refine ⟨19395437752340936244687557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51721167339575829985833485 19395437752340936244687557)
                    ·
                      refine ⟨3636644578563925545878917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19395437752340936244687557 3636644578563925545878917)
                      ·
                        rfl

theorem cell23_7082340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_7082340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082340 prefixEnd_7082340 := by exact prefixLift 7082340
  have htrace : WordTrace (prefixWord ++ tailWord_7082340) baseStart_7082340 baseEnd_7082340 := by
    simpa [prefixWord, tailWord_7082340, baseEnd_7082340] using wordTrace_append hprefix tailTrace_7082340
  have hstable : (prefixWord ++ tailWord_7082340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082340).length < 2 ^ (prefixWord ++ tailWord_7082340).sum := by decide
  have hdescent : baseEnd_7082340 < baseStart_7082340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082357 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7082357 : Nat := 118140960795 + 7082357 * 2 ^ 59
def prefixEnd_7082357 : Nat := 4983230072969 + 3 ^ 40 * 7082357 * 2
def baseEnd_7082357 : Nat := 3636653307735051979366339

theorem tailTrace_7082357 : CollatzResearch.WordTrace tailWord_7082357 prefixEnd_7082357 3636653307735051979366339 := by
  unfold tailWord_7082357
  simp only [CollatzResearch.WordTrace]
  refine ⟨258314781202837634121901325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172209854135225089414600883 258314781202837634121901325)
  ·
    refine ⟨96868042951064112795712997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258314781202837634121901325 96868042951064112795712997)
    ·
      refine ⟨18162758053324521149196187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96868042951064112795712997 18162758053324521149196187)
      ·
        refine ⟨27244137079986781723794281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18162758053324521149196187 27244137079986781723794281)
        ·
          refine ⟨20433102809990086292845711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27244137079986781723794281 20433102809990086292845711)
          ·
            refine ⟨30649654214985129439268567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20433102809990086292845711 30649654214985129439268567)
            ·
              refine ⟨45974481322477694158902851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30649654214985129439268567 45974481322477694158902851)
              ·
                refine ⟨68961721983716541238354277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45974481322477694158902851 68961721983716541238354277)
                ·
                  refine ⟨12930322871946851482191427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68961721983716541238354277 12930322871946851482191427)
                  ·
                    refine ⟨19395484307920277223287141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12930322871946851482191427 19395484307920277223287141)
                    ·
                      refine ⟨3636653307735051979366339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19395484307920277223287141 3636653307735051979366339)
                      ·
                        rfl

theorem cell23_7082357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7082357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082357 prefixEnd_7082357 := by exact prefixLift 7082357
  have htrace : WordTrace (prefixWord ++ tailWord_7082357) baseStart_7082357 baseEnd_7082357 := by
    simpa [prefixWord, tailWord_7082357, baseEnd_7082357] using wordTrace_append hprefix tailTrace_7082357
  have hstable : (prefixWord ++ tailWord_7082357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082357).length < 2 ^ (prefixWord ++ tailWord_7082357).sum := by decide
  have hdescent : baseEnd_7082357 < baseStart_7082357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082358 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_7082358 : Nat := 118140960795 + 7082358 * 2 ^ 59
def prefixEnd_7082358 : Nat := 4983230072969 + 3 ^ 40 * 7082358 * 2
def baseEnd_7082358 : Nat := 404072646801745163939315

theorem tailTrace_7082358 : CollatzResearch.WordTrace tailWord_7082358 prefixEnd_7082358 404072646801745163939315 := by
  unfold tailWord_7082358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144676104739625705792983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172209878450556007528458485 16144676104739625705792983)
  ·
    refine ⟨24217014157109438558689475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144676104739625705792983 24217014157109438558689475)
    ·
      refine ⟨36325521235664157838034213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24217014157109438558689475 36325521235664157838034213)
      ·
        refine ⟨6811035231687029594631415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36325521235664157838034213 6811035231687029594631415)
        ·
          refine ⟨10216552847530544391947123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811035231687029594631415 10216552847530544391947123)
          ·
            refine ⟨15324829271295816587920685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216552847530544391947123 15324829271295816587920685)
            ·
              refine ⟨5746810976735931220470257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15324829271295816587920685 5746810976735931220470257)
              ·
                refine ⟨4310108232551948415352693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746810976735931220470257 4310108232551948415352693)
                ·
                  refine ⟨404072646801745163939315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310108232551948415352693 404072646801745163939315)
                  ·
                    rfl

theorem cell23_7082358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_7082358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082358 prefixEnd_7082358 := by exact prefixLift 7082358
  have htrace : WordTrace (prefixWord ++ tailWord_7082358) baseStart_7082358 baseEnd_7082358 := by
    simpa [prefixWord, tailWord_7082358, baseEnd_7082358] using wordTrace_append hprefix tailTrace_7082358
  have hstable : (prefixWord ++ tailWord_7082358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082358).length < 2 ^ (prefixWord ++ tailWord_7082358).sum := by decide
  have hdescent : baseEnd_7082358 < baseStart_7082358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082394 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7082394 : Nat := 118140960795 + 7082394 * 2 ^ 59
def prefixEnd_7082394 : Nat := 4983230072969 + 3 ^ 40 * 7082394 * 2
def baseEnd_7082394 : Nat := 3636672306519268334603669

theorem tailTrace_7082394 : CollatzResearch.WordTrace tailWord_7082394 prefixEnd_7082394 3636672306519268334603669 := by
  unfold tailWord_7082394
  simp only [CollatzResearch.WordTrace]
  refine ⟨64579032675925897360249559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172210753802469059627332157 64579032675925897360249559)
  ·
    refine ⟨96868549013888846040374339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64579032675925897360249559 96868549013888846040374339)
    ·
      refine ⟨145302823520833269060561509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96868549013888846040374339 145302823520833269060561509)
      ·
        refine ⟨27244279410156237948855283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145302823520833269060561509 27244279410156237948855283)
        ·
          refine ⟨40866419115234356923282925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27244279410156237948855283 40866419115234356923282925)
          ·
            refine ⟨15324907168212883846231097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40866419115234356923282925 15324907168212883846231097)
            ·
              refine ⟨11493680376159662884673323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15324907168212883846231097 11493680376159662884673323)
              ·
                refine ⟨17240520564239494327009985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493680376159662884673323 17240520564239494327009985)
                ·
                  refine ⟨12930390423179620745257489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17240520564239494327009985 12930390423179620745257489)
                  ·
                    refine ⟨9697792817384715558943117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12930390423179620745257489 9697792817384715558943117)
                    ·
                      refine ⟨3636672306519268334603669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9697792817384715558943117 3636672306519268334603669)
                      ·
                        rfl

theorem cell23_7082394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7082394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082394 prefixEnd_7082394 := by exact prefixLift 7082394
  have htrace : WordTrace (prefixWord ++ tailWord_7082394) baseStart_7082394 baseEnd_7082394 := by
    simpa [prefixWord, tailWord_7082394, baseEnd_7082394] using wordTrace_append hprefix tailTrace_7082394
  have hstable : (prefixWord ++ tailWord_7082394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082394).length < 2 ^ (prefixWord ++ tailWord_7082394).sum := by decide
  have hdescent : baseEnd_7082394 < baseStart_7082394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082447 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_7082447 : Nat := 118140960795 + 7082447 * 2 ^ 59
def prefixEnd_7082447 : Nat := 4983230072969 + 3 ^ 40 * 7082447 * 2
def baseEnd_7082447 : Nat := 3636699520993956627240925

theorem tailTrace_7082447 : CollatzResearch.WordTrace tailWord_7082447 prefixEnd_7082447 3636699520993956627240925 := by
  unfold tailWord_7082447
  simp only [CollatzResearch.WordTrace]
  refine ⟨258318063772511579492677595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172212042515007719661785063 258318063772511579492677595)
  ·
    refine ⟨387477095658767369239016393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258318063772511579492677595 387477095658767369239016393)
    ·
      refine ⟨290607821744075526929262295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387477095658767369239016393 290607821744075526929262295)
      ·
        refine ⟨435911732616113290393893443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290607821744075526929262295 435911732616113290393893443)
        ·
          refine ⟨653867598924169935590840165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435911732616113290393893443 653867598924169935590840165)
          ·
            refine ⟨122600174798281862923282531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 653867598924169935590840165 122600174798281862923282531)
            ·
              refine ⟨183900262197422794384923797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122600174798281862923282531 183900262197422794384923797)
              ·
                refine ⟨8620324790504193486793303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183900262197422794384923797 8620324790504193486793303)
                ·
                  refine ⟨12930487185756290230189955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620324790504193486793303 12930487185756290230189955)
                  ·
                    refine ⟨19395730778634435345284933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12930487185756290230189955 19395730778634435345284933)
                    ·
                      refine ⟨3636699520993956627240925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19395730778634435345284933 3636699520993956627240925)
                      ·
                        rfl

theorem cell23_7082447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_7082447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082447 prefixEnd_7082447 := by exact prefixLift 7082447
  have htrace : WordTrace (prefixWord ++ tailWord_7082447) baseStart_7082447 baseEnd_7082447 := by
    simpa [prefixWord, tailWord_7082447, baseEnd_7082447] using wordTrace_append hprefix tailTrace_7082447
  have hstable : (prefixWord ++ tailWord_7082447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082447).length < 2 ^ (prefixWord ++ tailWord_7082447).sum := by decide
  have hdescent : baseEnd_7082447 < baseStart_7082447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082457 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_7082457 : Nat := 118140960795 + 7082457 * 2 ^ 59
def prefixEnd_7082457 : Nat := 4983230072969 + 3 ^ 40 * 7082457 * 2
def baseEnd_7082457 : Nat := 1212234885266833862705293

theorem tailTrace_7082457 : CollatzResearch.WordTrace tailWord_7082457 prefixEnd_7082457 1212234885266833862705293 := by
  unfold tailWord_7082457
  simp only [CollatzResearch.WordTrace]
  refine ⟨258318428502475351200541625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172212285668316900800361083 258318428502475351200541625)
  ·
    refine ⟨193738821376856513400406219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258318428502475351200541625 193738821376856513400406219)
    ·
      refine ⟨290608232065284770100609329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193738821376856513400406219 290608232065284770100609329)
      ·
        refine ⟨217956174048963577575456997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290608232065284770100609329 217956174048963577575456997)
        ·
          refine ⟨40866782634180670795398187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217956174048963577575456997 40866782634180670795398187)
          ·
            refine ⟨61300173951271006193097281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40866782634180670795398187 61300173951271006193097281)
            ·
              refine ⟨45975130463453254644822961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61300173951271006193097281 45975130463453254644822961)
              ·
                refine ⟨34481347847589940983617221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45975130463453254644822961 34481347847589940983617221)
                ·
                  refine ⟨6465252721423113934428229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34481347847589940983617221 6465252721423113934428229)
                  ·
                    refine ⟨1212234885266833862705293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465252721423113934428229 1212234885266833862705293)
                    ·
                      rfl

theorem cell23_7082457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_7082457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082457 prefixEnd_7082457 := by exact prefixLift 7082457
  have htrace : WordTrace (prefixWord ++ tailWord_7082457) baseStart_7082457 baseEnd_7082457 := by
    simpa [prefixWord, tailWord_7082457, baseEnd_7082457] using wordTrace_append hprefix tailTrace_7082457
  have hstable : (prefixWord ++ tailWord_7082457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082457).length < 2 ^ (prefixWord ++ tailWord_7082457).sum := by decide
  have hdescent : baseEnd_7082457 < baseStart_7082457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082464 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2]
def baseStart_7082464 : Nat := 118140960795 + 7082464 * 2 ^ 59
def prefixEnd_7082464 : Nat := 4983230072969 + 3 ^ 40 * 7082464 * 2
def baseEnd_7082464 : Nat := 3636708250165083060728347

theorem tailTrace_7082464 : CollatzResearch.WordTrace tailWord_7082464 prefixEnd_7082464 3636708250165083060728347 := by
  unfold tailWord_7082464
  simp only [CollatzResearch.WordTrace]
  refine ⟨129159341906724995698023223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172212455875633327597364297 129159341906724995698023223)
  ·
    refine ⟨193739012860087493547034835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129159341906724995698023223 193739012860087493547034835)
    ·
      refine ⟨290608519290131240320552253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193739012860087493547034835 290608519290131240320552253)
      ·
        refine ⟨108978194733799215120207095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290608519290131240320552253 108978194733799215120207095)
        ·
          refine ⟨163467292100698822680310643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108978194733799215120207095 163467292100698822680310643)
          ·
            refine ⟨245200938151048234020465965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163467292100698822680310643 245200938151048234020465965)
            ·
              refine ⟨91950351806643087757674737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245200938151048234020465965 91950351806643087757674737)
              ·
                refine ⟨68962763854982315818256053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91950351806643087757674737 68962763854982315818256053)
                ·
                  refine ⟨6465259111404592107961505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68962763854982315818256053 6465259111404592107961505)
                  ·
                    refine ⟨4848944333553444080971129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465259111404592107961505 4848944333553444080971129)
                    ·
                      refine ⟨3636708250165083060728347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848944333553444080971129 3636708250165083060728347)
                      ·
                        rfl

theorem cell23_7082464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_7082464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082464 prefixEnd_7082464 := by exact prefixLift 7082464
  have htrace : WordTrace (prefixWord ++ tailWord_7082464) baseStart_7082464 baseEnd_7082464 := by
    simpa [prefixWord, tailWord_7082464, baseEnd_7082464] using wordTrace_append hprefix tailTrace_7082464
  have hstable : (prefixWord ++ tailWord_7082464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082464).length < 2 ^ (prefixWord ++ tailWord_7082464).sum := by decide
  have hdescent : baseEnd_7082464 < baseStart_7082464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082474 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7082474 : Nat := 118140960795 + 7082474 * 2 ^ 59
def prefixEnd_7082474 : Nat := 4983230072969 + 3 ^ 40 * 7082474 * 2
def baseEnd_7082474 : Nat := 1212237794990542673867767

theorem tailTrace_7082474 : CollatzResearch.WordTrace tailWord_7082474 prefixEnd_7082474 1212237794990542673867767 := by
  unfold tailWord_7082474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64579762135853440775977619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172212699028942508735940317 64579762135853440775977619)
  ·
    refine ⟨96869643203780161163966429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64579762135853440775977619 96869643203780161163966429)
    ·
      refine ⟨36326116201417560436487411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96869643203780161163966429 36326116201417560436487411)
      ·
        refine ⟨54489174302126340654731117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36326116201417560436487411 54489174302126340654731117)
        ·
          refine ⟨20433440363297377745524169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54489174302126340654731117 20433440363297377745524169)
          ·
            refine ⟨15325080272473033309143127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20433440363297377745524169 15325080272473033309143127)
            ·
              refine ⟨22987620408709549963714691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15325080272473033309143127 22987620408709549963714691)
              ·
                refine ⟨34481430613064324945572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22987620408709549963714691 34481430613064324945572037)
                ·
                  refine ⟨6465268239949560927294757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34481430613064324945572037 6465268239949560927294757)
                  ·
                    refine ⟨1212237794990542673867767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465268239949560927294757 1212237794990542673867767)
                    ·
                      rfl

theorem cell23_7082474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7082474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082474 prefixEnd_7082474 := by exact prefixLift 7082474
  have htrace : WordTrace (prefixWord ++ tailWord_7082474) baseStart_7082474 baseEnd_7082474 := by
    simpa [prefixWord, tailWord_7082474, baseEnd_7082474] using wordTrace_append hprefix tailTrace_7082474
  have hstable : (prefixWord ++ tailWord_7082474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082474).length < 2 ^ (prefixWord ++ tailWord_7082474).sum := by decide
  have hdescent : baseEnd_7082474 < baseStart_7082474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082481 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_7082481 : Nat := 118140960795 + 7082481 * 2 ^ 59
def prefixEnd_7082481 : Nat := 4983230072969 + 3 ^ 40 * 7082481 * 2
def baseEnd_7082481 : Nat := 3636716979336209494215769

theorem tailTrace_7082481 : CollatzResearch.WordTrace tailWord_7082481 prefixEnd_7082481 3636716979336209494215769 := by
  unfold tailWord_7082481
  simp only [CollatzResearch.WordTrace]
  refine ⟨258319303854388403299415297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172212869236258935532943531 258319303854388403299415297)
  ·
    refine ⟨193739477890791302474561473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258319303854388403299415297 193739477890791302474561473)
    ·
      refine ⟨145304608418093476855921105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193739477890791302474561473 145304608418093476855921105)
      ·
        refine ⟨108978456313570107641940829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145304608418093476855921105 108978456313570107641940829)
        ·
          refine ⟨40866921117588790365727811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108978456313570107641940829 40866921117588790365727811)
          ·
            refine ⟨61300381676383185548591717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40866921117588790365727811 61300381676383185548591717)
            ·
              refine ⟨11493821564321847290360947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61300381676383185548591717 11493821564321847290360947)
              ·
                refine ⟨17240732346482770935541421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493821564321847290360947 17240732346482770935541421)
                ·
                  refine ⟨6465274629931039100828033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17240732346482770935541421 6465274629931039100828033)
                  ·
                    refine ⟨4848955972448279325621025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465274629931039100828033 4848955972448279325621025)
                    ·
                      refine ⟨3636716979336209494215769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848955972448279325621025 3636716979336209494215769)
                      ·
                        rfl

theorem cell23_7082481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_7082481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082481 prefixEnd_7082481 := by exact prefixLift 7082481
  have htrace : WordTrace (prefixWord ++ tailWord_7082481) baseStart_7082481 baseEnd_7082481 := by
    simpa [prefixWord, tailWord_7082481, baseEnd_7082481] using wordTrace_append hprefix tailTrace_7082481
  have hstable : (prefixWord ++ tailWord_7082481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082481).length < 2 ^ (prefixWord ++ tailWord_7082481).sum := by decide
  have hdescent : baseEnd_7082481 < baseStart_7082481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082490 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_7082490 : Nat := 118140960795 + 7082490 * 2 ^ 59
def prefixEnd_7082490 : Nat := 4983230072969 + 3 ^ 40 * 7082490 * 2
def baseEnd_7082490 : Nat := 3636721600662099959003227

theorem tailTrace_7082490 : CollatzResearch.WordTrace tailWord_7082490 prefixEnd_7082490 3636721600662099959003227 := by
  unfold tailWord_7082490
  simp only [CollatzResearch.WordTrace]
  refine ⟨64579908027838949459123231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172213088074237198557661949 64579908027838949459123231)
  ·
    refine ⟨96869862041758424188684847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64579908027838949459123231 96869862041758424188684847)
    ·
      refine ⟨145304793062637636283027271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96869862041758424188684847 145304793062637636283027271)
      ·
        refine ⟨217957189593956454424540907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145304793062637636283027271 217957189593956454424540907)
        ·
          refine ⟨326935784390934681636811361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217957189593956454424540907 326935784390934681636811361)
          ·
            refine ⟨245201838293201011227608521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326935784390934681636811361 245201838293201011227608521)
            ·
              refine ⟨183901378719900758420706391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245201838293201011227608521 183901378719900758420706391)
              ·
                refine ⟨275852068079851137631059587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183901378719900758420706391 275852068079851137631059587)
                ·
                  refine ⟨413778102119776706446589381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275852068079851137631059587 413778102119776706446589381)
                  ·
                    refine ⟨77583394147458132458735509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413778102119776706446589381 77583394147458132458735509)
                    ·
                      refine ⟨3636721600662099959003227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77583394147458132458735509 3636721600662099959003227)
                      ·
                        rfl

theorem cell23_7082490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_7082490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082490 prefixEnd_7082490 := by exact prefixLift 7082490
  have htrace : WordTrace (prefixWord ++ tailWord_7082490) baseStart_7082490 baseEnd_7082490 := by
    simpa [prefixWord, tailWord_7082490, baseEnd_7082490] using wordTrace_append hprefix tailTrace_7082490
  have hstable : (prefixWord ++ tailWord_7082490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082490).length < 2 ^ (prefixWord ++ tailWord_7082490).sum := by decide
  have hdescent : baseEnd_7082490 < baseStart_7082490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082498 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7082498 : Nat := 118140960795 + 7082498 * 2 ^ 59
def prefixEnd_7082498 : Nat := 4983230072969 + 3 ^ 40 * 7082498 * 2
def baseEnd_7082498 : Nat := 3636725708507335927703191

theorem tailTrace_7082498 : CollatzResearch.WordTrace tailWord_7082498 prefixEnd_7082498 3636725708507335927703191 := by
  unfold tailWord_7082498
  simp only [CollatzResearch.WordTrace]
  refine ⟨64579980973831703800696037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172213282596884543468522765 64579980973831703800696037)
  ·
    refine ⟨12108746432593444462630507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64579980973831703800696037 12108746432593444462630507)
    ·
      refine ⟨18163119648890166693945761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12108746432593444462630507 18163119648890166693945761)
      ·
        refine ⟨13622339736667625020459321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18163119648890166693945761 13622339736667625020459321)
        ·
          refine ⟨10216754802500718765344491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13622339736667625020459321 10216754802500718765344491)
          ·
            refine ⟨15325132203751078148016737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216754802500718765344491 15325132203751078148016737)
            ·
              refine ⟨11493849152813308611012553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15325132203751078148016737 11493849152813308611012553)
              ·
                refine ⟨8620386864609981458259415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11493849152813308611012553 8620386864609981458259415)
                ·
                  refine ⟨12930580296914972187389123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620386864609981458259415 12930580296914972187389123)
                  ·
                    refine ⟨19395870445372458281083685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12930580296914972187389123 19395870445372458281083685)
                    ·
                      refine ⟨3636725708507335927703191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19395870445372458281083685 3636725708507335927703191)
                      ·
                        rfl

theorem cell23_7082498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7082498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082498 prefixEnd_7082498 := by exact prefixLift 7082498
  have htrace : WordTrace (prefixWord ++ tailWord_7082498) baseStart_7082498 baseEnd_7082498 := by
    simpa [prefixWord, tailWord_7082498, baseEnd_7082498] using wordTrace_append hprefix tailTrace_7082498
  have hstable : (prefixWord ++ tailWord_7082498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082498).length < 2 ^ (prefixWord ++ tailWord_7082498).sum := by decide
  have hdescent : baseEnd_7082498 < baseStart_7082498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082532 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7082532 : Nat := 118140960795 + 7082532 * 2 ^ 59
def prefixEnd_7082532 : Nat := 4983230072969 + 3 ^ 40 * 7082532 * 2
def baseEnd_7082532 : Nat := 3636743166849588794678035

theorem tailTrace_7082532 : CollatzResearch.WordTrace tailWord_7082532 prefixEnd_7082532 3636743166849588794678035 := by
  unfold tailWord_7082532
  simp only [CollatzResearch.WordTrace]
  refine ⟨129160581988601819504760925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172214109318135759339681233 129160581988601819504760925)
  ·
    refine ⟨48435218245725682314285347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129160581988601819504760925 48435218245725682314285347)
    ·
      refine ⟨72652827368588523471428021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48435218245725682314285347 72652827368588523471428021)
      ·
        refine ⟨6811202565805174075446377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72652827368588523471428021 6811202565805174075446377)
        ·
          refine ⟨5108401924353880556584783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6811202565805174075446377 5108401924353880556584783)
          ·
            refine ⟨7662602886530820834877175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5108401924353880556584783 7662602886530820834877175)
            ·
              refine ⟨11493904329796231252315763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662602886530820834877175 11493904329796231252315763)
              ·
                refine ⟨17240856494694346878473645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493904329796231252315763 17240856494694346878473645)
                ·
                  refine ⟨6465321185510380079427617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17240856494694346878473645 6465321185510380079427617)
                  ·
                    refine ⟨4848990889132785059570713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465321185510380079427617 4848990889132785059570713)
                    ·
                      refine ⟨3636743166849588794678035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4848990889132785059570713 3636743166849588794678035)
                      ·
                        rfl

theorem cell23_7082532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7082532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082532 prefixEnd_7082532 := by exact prefixLift 7082532
  have htrace : WordTrace (prefixWord ++ tailWord_7082532) baseStart_7082532 baseEnd_7082532 := by
    simpa [prefixWord, tailWord_7082532, baseEnd_7082532] using wordTrace_append hprefix tailTrace_7082532
  have hstable : (prefixWord ++ tailWord_7082532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082532).length < 2 ^ (prefixWord ++ tailWord_7082532).sum := by decide
  have hdescent : baseEnd_7082532 < baseStart_7082532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082607 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 4, 5]
def baseStart_7082607 : Nat := 118140960795 + 7082607 * 2 ^ 59
def prefixEnd_7082607 : Nat := 4983230072969 + 3 ^ 40 * 7082607 * 2
def baseEnd_7082607 : Nat := 1212260559299558667080063

theorem tailTrace_7082607 : CollatzResearch.WordTrace tailWord_7082607 prefixEnd_7082607 1212260559299558667080063 := by
  unfold tailWord_7082607
  simp only [CollatzResearch.WordTrace]
  refine ⟨258323899451931926818502075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172215932967954617879001383 258323899451931926818502075)
  ·
    refine ⟨387485849177897890227753113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258323899451931926818502075 387485849177897890227753113)
    ·
      refine ⟨290614386883423417670814835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387485849177897890227753113 290614386883423417670814835)
      ·
        refine ⟨435921580325135126506222253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290614386883423417670814835 435921580325135126506222253)
        ·
          refine ⟨163470592621925672439833345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435921580325135126506222253 163470592621925672439833345)
          ·
            refine ⟨122602944466444254329875009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163470592621925672439833345 122602944466444254329875009)
            ·
              refine ⟨91952208349833190747406257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122602944466444254329875009 91952208349833190747406257)
              ·
                refine ⟨68964156262374893060554693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91952208349833190747406257 68964156262374893060554693)
                ·
                  refine ⟨12930779299195292448854005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68964156262374893060554693 12930779299195292448854005)
                  ·
                    refine ⟨1212260559299558667080063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12930779299195292448854005 1212260559299558667080063)
                    ·
                      rfl

theorem cell23_7082607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_7082607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082607 prefixEnd_7082607 := by exact prefixLift 7082607
  have htrace : WordTrace (prefixWord ++ tailWord_7082607) baseStart_7082607 baseEnd_7082607 := by
    simpa [prefixWord, tailWord_7082607, baseEnd_7082607] using wordTrace_append hprefix tailTrace_7082607
  have hstable : (prefixWord ++ tailWord_7082607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082607).length < 2 ^ (prefixWord ++ tailWord_7082607).sum := by decide
  have hdescent : baseEnd_7082607 < baseStart_7082607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082624 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_7082624 : Nat := 118140960795 + 7082624 * 2 ^ 59
def prefixEnd_7082624 : Nat := 4983230072969 + 3 ^ 40 * 7082624 * 2
def baseEnd_7082624 : Nat := 1212263469023267478242537

theorem tailTrace_7082624 : CollatzResearch.WordTrace tailWord_7082624 prefixEnd_7082624 1212263469023267478242537 := by
  unfold tailWord_7082624
  simp only [CollatzResearch.WordTrace]
  refine ⟨129162259746435169360935463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172216346328580225814580617 129162259746435169360935463)
  ·
    refine ⟨193743389619652754041403195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129162259746435169360935463 193743389619652754041403195)
    ·
      refine ⟨290615084429479131062104793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193743389619652754041403195 290615084429479131062104793)
      ·
        refine ⟨217961313322109348296578595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290615084429479131062104793 217961313322109348296578595)
        ·
          refine ⟨326941969983164022444867893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217961313322109348296578595 326941969983164022444867893)
          ·
            refine ⟨30650809685921627104206365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326941969983164022444867893 30650809685921627104206365)
            ·
              refine ⟨11494053632220610164077387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30650809685921627104206365 11494053632220610164077387)
              ·
                refine ⟨17241080448330915246116081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11494053632220610164077387 17241080448330915246116081)
                ·
                  refine ⟨12930810336248186434587061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17241080448330915246116081 12930810336248186434587061)
                  ·
                    refine ⟨1212263469023267478242537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12930810336248186434587061 1212263469023267478242537)
                    ·
                      rfl

theorem cell23_7082624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_7082624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082624 prefixEnd_7082624 := by exact prefixLift 7082624
  have htrace : WordTrace (prefixWord ++ tailWord_7082624) baseStart_7082624 baseEnd_7082624 := by
    simpa [prefixWord, tailWord_7082624, baseEnd_7082624] using wordTrace_append hprefix tailTrace_7082624
  have hstable : (prefixWord ++ tailWord_7082624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082624).length < 2 ^ (prefixWord ++ tailWord_7082624).sum := by decide
  have hdescent : baseEnd_7082624 < baseStart_7082624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082626 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7082626 : Nat := 118140960795 + 7082626 * 2 ^ 59
def prefixEnd_7082626 : Nat := 4983230072969 + 3 ^ 40 * 7082626 * 2
def baseEnd_7082626 : Nat := 3636791434031111426902603

theorem tailTrace_7082626 : CollatzResearch.WordTrace tailWord_7082626 prefixEnd_7082626 3636791434031111426902603 := by
  unfold tailWord_7082626
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581148109715773265860933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172216394959242062042295821 64581148109715773265860933)
  ·
    refine ⟨12108965270571707487348925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64581148109715773265860933 12108965270571707487348925)
    ·
      refine ⟨4540861976464390307755847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12108965270571707487348925 4540861976464390307755847)
      ·
        refine ⟨6811292964696585461633771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540861976464390307755847 6811292964696585461633771)
        ·
          refine ⟨10216939447044878192450657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811292964696585461633771 10216939447044878192450657)
          ·
            refine ⟨7662704585283658644337993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10216939447044878192450657 7662704585283658644337993)
            ·
              refine ⟨5747028438962743983253495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7662704585283658644337993 5747028438962743983253495)
              ·
                refine ⟨8620542658444115974880243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747028438962743983253495 8620542658444115974880243)
                ·
                  refine ⟨12930813987666173962320365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620542658444115974880243 12930813987666173962320365)
                  ·
                    refine ⟨4849055245374815235870137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12930813987666173962320365 4849055245374815235870137)
                    ·
                      refine ⟨3636791434031111426902603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849055245374815235870137 3636791434031111426902603)
                      ·
                        rfl

theorem cell23_7082626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7082626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082626 prefixEnd_7082626 := by exact prefixLift 7082626
  have htrace : WordTrace (prefixWord ++ tailWord_7082626) baseStart_7082626 baseEnd_7082626 := by
    simpa [prefixWord, tailWord_7082626, baseEnd_7082626] using wordTrace_append hprefix tailTrace_7082626
  have hstable : (prefixWord ++ tailWord_7082626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082626).length < 2 ^ (prefixWord ++ tailWord_7082626).sum := by decide
  have hdescent : baseEnd_7082626 < baseStart_7082626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082688 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 1, 4]
def baseStart_7082688 : Nat := 118140960795 + 7082688 * 2 ^ 59
def prefixEnd_7082688 : Nat := 4983230072969 + 3 ^ 40 * 7082688 * 2
def baseEnd_7082688 : Nat := 1212274423277230061442439

theorem tailTrace_7082688 : CollatzResearch.WordTrace tailWord_7082688 prefixEnd_7082688 1212274423277230061442439 := by
  unfold tailWord_7082688
  simp only [CollatzResearch.WordTrace]
  refine ⟨129163426882319238826100359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172217902509758985101467145 129163426882319238826100359)
  ·
    refine ⟨193745140323478858239150539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129163426882319238826100359 193745140323478858239150539)
    ·
      refine ⟨290617710485218287358725809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193745140323478858239150539 290617710485218287358725809)
      ·
        refine ⟨217963282863913715519044357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290617710485218287358725809 217963282863913715519044357)
        ·
          refine ⟨40868115536983821659820817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217963282863913715519044357 40868115536983821659820817)
          ·
            refine ⟨30651086652737866244865613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40868115536983821659820817 30651086652737866244865613)
            ·
              refine ⟨11494157494776699841824605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30651086652737866244865613 11494157494776699841824605)
              ·
                refine ⟨4310309060541262440684227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11494157494776699841824605 4310309060541262440684227)
                ·
                  refine ⟨6465463590811893661026341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310309060541262440684227 6465463590811893661026341)
                  ·
                    refine ⟨1212274423277230061442439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465463590811893661026341 1212274423277230061442439)
                    ·
                      rfl

theorem cell23_7082688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 4].length) (baseStart_7082688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082688 prefixEnd_7082688 := by exact prefixLift 7082688
  have htrace : WordTrace (prefixWord ++ tailWord_7082688) baseStart_7082688 baseEnd_7082688 := by
    simpa [prefixWord, tailWord_7082688, baseEnd_7082688] using wordTrace_append hprefix tailTrace_7082688
  have hstable : (prefixWord ++ tailWord_7082688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082688).length < 2 ^ (prefixWord ++ tailWord_7082688).sum := by decide
  have hdescent : baseEnd_7082688 < baseStart_7082688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082714 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_7082714 : Nat := 118140960795 + 7082714 * 2 ^ 59
def prefixEnd_7082714 : Nat := 4983230072969 + 3 ^ 40 * 7082714 * 2
def baseEnd_7082714 : Nat := 1212278873442902360867399

theorem tailTrace_7082714 : CollatzResearch.WordTrace tailWord_7082714 prefixEnd_7082714 1212278873442902360867399 := by
  unfold tailWord_7082714
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581950515636071023161799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172218534708362856061764797 64581950515636071023161799)
  ·
    refine ⟨96872925773454106534742699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64581950515636071023161799 96872925773454106534742699)
    ·
      refine ⟨145309388660181159802114049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96872925773454106534742699 145309388660181159802114049)
      ·
        refine ⟨108982041495135869851585537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145309388660181159802114049 108982041495135869851585537)
        ·
          refine ⟨81736531121351902388689153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108982041495135869851585537 81736531121351902388689153)
          ·
            refine ⟨61302398341013926791516865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81736531121351902388689153 61302398341013926791516865)
            ·
              refine ⟨45976798755760445093637649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61302398341013926791516865 45976798755760445093637649)
              ·
                refine ⟨34482599066820333820228237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45976798755760445093637649 34482599066820333820228237)
                ·
                  refine ⟨12930974650057625182585589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34482599066820333820228237 12930974650057625182585589)
                  ·
                    refine ⟨1212278873442902360867399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12930974650057625182585589 1212278873442902360867399)
                    ·
                      rfl

theorem cell23_7082714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_7082714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082714 prefixEnd_7082714 := by exact prefixLift 7082714
  have htrace : WordTrace (prefixWord ++ tailWord_7082714) baseStart_7082714 baseEnd_7082714 := by
    simpa [prefixWord, tailWord_7082714, baseEnd_7082714] using wordTrace_append hprefix tailTrace_7082714
  have hstable : (prefixWord ++ tailWord_7082714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082714).length < 2 ^ (prefixWord ++ tailWord_7082714).sum := by decide
  have hdescent : baseEnd_7082714 < baseStart_7082714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082738 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7082738 : Nat := 118140960795 + 7082738 * 2 ^ 59
def prefixEnd_7082738 : Nat := 4983230072969 + 3 ^ 40 * 7082738 * 2
def baseEnd_7082738 : Nat := 3636848943864414988702087

theorem tailTrace_7082738 : CollatzResearch.WordTrace tailWord_7082738 prefixEnd_7082738 3636848943864414988702087 := by
  unfold tailWord_7082738
  simp only [CollatzResearch.WordTrace]
  refine ⟨64582169353614334047880217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172219118276304890794347245 64582169353614334047880217)
  ·
    refine ⟨48436627015210750535910163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64582169353614334047880217 48436627015210750535910163)
    ·
      refine ⟨72654940522816125803865245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48436627015210750535910163 72654940522816125803865245)
      ·
        refine ⟨27245602696056047176449467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72654940522816125803865245 27245602696056047176449467)
        ·
          refine ⟨40868404044084070764674201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27245602696056047176449467 40868404044084070764674201)
          ·
            refine ⟨30651303033063053073505651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40868404044084070764674201 30651303033063053073505651)
            ·
              refine ⟨45976954549594579610258477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30651303033063053073505651 45976954549594579610258477)
              ·
                refine ⟨17241357956097967353846929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45976954549594579610258477 17241357956097967353846929)
                ·
                  refine ⟨12931018467073475515385197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17241357956097967353846929 12931018467073475515385197)
                  ·
                    refine ⟨4849131925152553318269449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12931018467073475515385197 4849131925152553318269449)
                    ·
                      refine ⟨3636848943864414988702087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849131925152553318269449 3636848943864414988702087)
                      ·
                        rfl

theorem cell23_7082738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7082738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082738 prefixEnd_7082738 := by exact prefixLift 7082738
  have htrace : WordTrace (prefixWord ++ tailWord_7082738) baseStart_7082738 baseEnd_7082738 := by
    simpa [prefixWord, tailWord_7082738, baseEnd_7082738] using wordTrace_append hprefix tailTrace_7082738
  have hstable : (prefixWord ++ tailWord_7082738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082738).length < 2 ^ (prefixWord ++ tailWord_7082738).sum := by decide
  have hdescent : baseEnd_7082738 < baseStart_7082738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082744 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_7082744 : Nat := 118140960795 + 7082744 * 2 ^ 59
def prefixEnd_7082744 : Nat := 4983230072969 + 3 ^ 40 * 7082744 * 2
def baseEnd_7082744 : Nat := 1212284008249447321742353

theorem tailTrace_7082744 : CollatzResearch.WordTrace tailWord_7082744 prefixEnd_7082744 1212284008249447321742353 := by
  unfold tailWord_7082744
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164448126217799608119643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172219264168290399477492857 129164448126217799608119643)
  ·
    refine ⟨193746672189326699412179465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129164448126217799608119643 193746672189326699412179465)
    ·
      refine ⟨145310004141995024559134599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193746672189326699412179465 145310004141995024559134599)
      ·
        refine ⟨217965006212992536838701899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145310004141995024559134599 217965006212992536838701899)
        ·
          refine ⟨326947509319488805258052849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217965006212992536838701899 326947509319488805258052849)
          ·
            refine ⟨245210631989616603943539637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326947509319488805258052849 245210631989616603943539637)
            ·
              refine ⟨22988496749026556619706841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245210631989616603943539637 22988496749026556619706841)
              ·
                refine ⟨17241372561769917464780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22988496749026556619706841 17241372561769917464780131)
                ·
                  refine ⟨25862058842654876197170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17241372561769917464780131 25862058842654876197170197)
                  ·
                    refine ⟨1212284008249447321742353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25862058842654876197170197 1212284008249447321742353)
                    ·
                      rfl

theorem cell23_7082744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_7082744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082744 prefixEnd_7082744 := by exact prefixLift 7082744
  have htrace : WordTrace (prefixWord ++ tailWord_7082744) baseStart_7082744 baseEnd_7082744 := by
    simpa [prefixWord, tailWord_7082744, baseEnd_7082744] using wordTrace_append hprefix tailTrace_7082744
  have hstable : (prefixWord ++ tailWord_7082744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082744).length < 2 ^ (prefixWord ++ tailWord_7082744).sum := by decide
  have hdescent : baseEnd_7082744 < baseStart_7082744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082748 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_7082748 : Nat := 118140960795 + 7082748 * 2 ^ 59
def prefixEnd_7082748 : Nat := 4983230072969 + 3 ^ 40 * 7082748 * 2
def baseEnd_7082748 : Nat := 1212284692890319983192347

theorem tailTrace_7082748 : CollatzResearch.WordTrace tailWord_7082748 prefixEnd_7082748 1212284692890319983192347 := by
  unfold tailWord_7082748
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164521072210553949692449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172219361429614071932923265 129164521072210553949692449)
  ·
    refine ⟨96873390804157915462269337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129164521072210553949692449 96873390804157915462269337)
    ·
      refine ⟨72655043103118436596702003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96873390804157915462269337 72655043103118436596702003)
      ·
        refine ⟨108982564654677654895053005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72655043103118436596702003 108982564654677654895053005)
        ·
          refine ⟨40868461745504120585644877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108982564654677654895053005 40868461745504120585644877)
          ·
            refine ⟨15325673154564045219616829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40868461745504120585644877 15325673154564045219616829)
            ·
              refine ⟨5747127432961516957356311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15325673154564045219616829 5747127432961516957356311)
              ·
                refine ⟨8620691149442275436034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747127432961516957356311 8620691149442275436034467)
                ·
                  refine ⟨12931036724163413154051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620691149442275436034467 12931036724163413154051701)
                  ·
                    refine ⟨1212284692890319983192347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12931036724163413154051701 1212284692890319983192347)
                    ·
                      rfl

theorem cell23_7082748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_7082748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082748 prefixEnd_7082748 := by exact prefixLift 7082748
  have htrace : WordTrace (prefixWord ++ tailWord_7082748) baseStart_7082748 baseEnd_7082748 := by
    simpa [prefixWord, tailWord_7082748, baseEnd_7082748] using wordTrace_append hprefix tailTrace_7082748
  have hstable : (prefixWord ++ tailWord_7082748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082748).length < 2 ^ (prefixWord ++ tailWord_7082748).sum := by decide
  have hdescent : baseEnd_7082748 < baseStart_7082748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082761 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_7082761 : Nat := 118140960795 + 7082761 * 2 ^ 59
def prefixEnd_7082761 : Nat := 4983230072969 + 3 ^ 40 * 7082761 * 2
def baseEnd_7082761 : Nat := 1212286917973156132904827

theorem tailTrace_7082761 : CollatzResearch.WordTrace tailWord_7082761 prefixEnd_7082761 1212286917973156132904827 := by
  unfold tailWord_7082761
  simp only [CollatzResearch.WordTrace]
  refine ⟨258329516293374011119608137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172219677528916007413072091 258329516293374011119608137)
  ·
    refine ⟨193747137220030508339706103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258329516293374011119608137 193747137220030508339706103)
    ·
      refine ⟨290620705830045762509559155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193747137220030508339706103 290620705830045762509559155)
      ·
        refine ⟨435931058745068643764338733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290620705830045762509559155 435931058745068643764338733)
        ·
          refine ⟨163474147029400741411627025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435931058745068643764338733 163474147029400741411627025)
          ·
            refine ⟨122605610272050556058720269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163474147029400741411627025 122605610272050556058720269)
            ·
              refine ⟨45977103852018958522020101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122605610272050556058720269 45977103852018958522020101)
              ·
                refine ⟨8620706972253554722878769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45977103852018958522020101 8620706972253554722878769)
                ·
                  refine ⟨6465530229190166042159077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8620706972253554722878769 6465530229190166042159077)
                  ·
                    refine ⟨1212286917973156132904827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465530229190166042159077 1212286917973156132904827)
                    ·
                      rfl

theorem cell23_7082761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_7082761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082761 prefixEnd_7082761 := by exact prefixLift 7082761
  have htrace : WordTrace (prefixWord ++ tailWord_7082761) baseStart_7082761 baseEnd_7082761 := by
    simpa [prefixWord, tailWord_7082761, baseEnd_7082761] using wordTrace_append hprefix tailTrace_7082761
  have hstable : (prefixWord ++ tailWord_7082761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082761).length < 2 ^ (prefixWord ++ tailWord_7082761).sum := by decide
  have hdescent : baseEnd_7082761 < baseStart_7082761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082764 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7082764 : Nat := 118140960795 + 7082764 * 2 ^ 59
def prefixEnd_7082764 : Nat := 4983230072969 + 3 ^ 40 * 7082764 * 2
def baseEnd_7082764 : Nat := 3636862294361431886976967

theorem tailTrace_7082764 : CollatzResearch.WordTrace tailWord_7082764 prefixEnd_7082764 3636862294361431886976967 := by
  unfold tailWord_7082764
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164812856181571315983673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172219750474908761754644897 129164812856181571315983673)
  ·
    refine ⟨96873609642136178486987755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129164812856181571315983673 96873609642136178486987755)
    ·
      refine ⟨145310414463204267730481633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96873609642136178486987755 145310414463204267730481633)
      ·
        refine ⟨108982810847403200797861225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145310414463204267730481633 108982810847403200797861225)
        ·
          refine ⟨81737108135552400598395919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108982810847403200797861225 81737108135552400598395919)
          ·
            refine ⟨122605662203328600897593879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81737108135552400598395919 122605662203328600897593879)
            ·
              refine ⟨183908493304992901346390819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122605662203328600897593879 183908493304992901346390819)
              ·
                refine ⟨275862739957489352019586229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183908493304992901346390819 275862739957489352019586229)
                ·
                  refine ⟨25862131871014626751836209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275862739957489352019586229 25862131871014626751836209)
                  ·
                    refine ⟨19396598903260970063877157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25862131871014626751836209 19396598903260970063877157)
                    ·
                      refine ⟨3636862294361431886976967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19396598903260970063877157 3636862294361431886976967)
                      ·
                        rfl

theorem cell23_7082764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7082764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082764 prefixEnd_7082764 := by exact prefixLift 7082764
  have htrace : WordTrace (prefixWord ++ tailWord_7082764) baseStart_7082764 baseEnd_7082764 := by
    simpa [prefixWord, tailWord_7082764, baseEnd_7082764] using wordTrace_append hprefix tailTrace_7082764
  have hstable : (prefixWord ++ tailWord_7082764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082764).length < 2 ^ (prefixWord ++ tailWord_7082764).sum := by decide
  have hdescent : baseEnd_7082764 < baseStart_7082764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082798 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7082798 : Nat := 118140960795 + 7082798 * 2 ^ 59
def prefixEnd_7082798 : Nat := 4983230072969 + 3 ^ 40 * 7082798 * 2
def baseEnd_7082798 : Nat := 3636879752703684753951811

theorem tailTrace_7082798 : CollatzResearch.WordTrace tailWord_7082798 prefixEnd_7082798 3636879752703684753951811 := by
  unfold tailWord_7082798
  simp only [CollatzResearch.WordTrace]
  refine ⟨32291358224279995804838131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172220577196159977625803365 32291358224279995804838131)
  ·
    refine ⟨48437037336419993707257197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32291358224279995804838131 48437037336419993707257197)
    ·
      refine ⟨18163889001157497640221449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48437037336419993707257197 18163889001157497640221449)
      ·
        refine ⟨13622916750868123230166087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18163889001157497640221449 13622916750868123230166087)
        ·
          refine ⟨20434375126302184845249131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13622916750868123230166087 20434375126302184845249131)
          ·
            refine ⟨30651562689453277267873697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20434375126302184845249131 30651562689453277267873697)
            ·
              refine ⟨22988672017089957950905273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30651562689453277267873697 22988672017089957950905273)
              ·
                refine ⟨17241504012817468463178955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22988672017089957950905273 17241504012817468463178955)
                ·
                  refine ⟨25862256019226202694768433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17241504012817468463178955 25862256019226202694768433)
                  ·
                    refine ⟨19396692014419652021076325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25862256019226202694768433 19396692014419652021076325)
                    ·
                      refine ⟨3636879752703684753951811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19396692014419652021076325 3636879752703684753951811)
                      ·
                        rfl

theorem cell23_7082798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7082798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082798 prefixEnd_7082798 := by exact prefixLift 7082798
  have htrace : WordTrace (prefixWord ++ tailWord_7082798) baseStart_7082798 baseEnd_7082798 := by
    simpa [prefixWord, tailWord_7082798, baseEnd_7082798] using wordTrace_append hprefix tailTrace_7082798
  have hstable : (prefixWord ++ tailWord_7082798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082798).length < 2 ^ (prefixWord ++ tailWord_7082798).sum := by decide
  have hdescent : baseEnd_7082798 < baseStart_7082798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082801 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_7082801 : Nat := 118140960795 + 7082801 * 2 ^ 59
def prefixEnd_7082801 : Nat := 4983230072969 + 3 ^ 40 * 7082801 * 2
def baseEnd_7082801 : Nat := 3636881293145648242214297

theorem tailTrace_7082801 : CollatzResearch.WordTrace tailWord_7082801 prefixEnd_7082801 3636881293145648242214297 := by
  unfold tailWord_7082801
  simp only [CollatzResearch.WordTrace]
  refine ⟨258330975213229097951064257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172220650142152731967376171 258330975213229097951064257)
  ·
    refine ⟨193748231409921823463298193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258330975213229097951064257 193748231409921823463298193)
    ·
      refine ⟨145311173557441367597473645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193748231409921823463298193 145311173557441367597473645)
      ·
        refine ⟨54491690084040512849052617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145311173557441367597473645 54491690084040512849052617)
        ·
          refine ⟨40868767563030384636789463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54491690084040512849052617 40868767563030384636789463)
          ·
            refine ⟨61303151344545576955184195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40868767563030384636789463 61303151344545576955184195)
            ·
              refine ⟨91954727016818365432776293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61303151344545576955184195 91954727016818365432776293)
              ·
                refine ⟨17241511315653443518645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91954727016818365432776293 17241511315653443518645555)
                ·
                  refine ⟨25862266973480165277968333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17241511315653443518645555 25862266973480165277968333)
                  ·
                    refine ⟨9698350115055061979238125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25862266973480165277968333 9698350115055061979238125)
                    ·
                      refine ⟨3636881293145648242214297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698350115055061979238125 3636881293145648242214297)
                      ·
                        rfl

theorem cell23_7082801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_7082801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082801 prefixEnd_7082801 := by exact prefixLift 7082801
  have htrace : WordTrace (prefixWord ++ tailWord_7082801) baseStart_7082801 baseEnd_7082801 := by
    simpa [prefixWord, tailWord_7082801, baseEnd_7082801] using wordTrace_append hprefix tailTrace_7082801
  have hstable : (prefixWord ++ tailWord_7082801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082801).length < 2 ^ (prefixWord ++ tailWord_7082801).sum := by decide
  have hdescent : baseEnd_7082801 < baseStart_7082801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082802 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_7082802 : Nat := 118140960795 + 7082802 * 2 ^ 59
def prefixEnd_7082802 : Nat := 4983230072969 + 3 ^ 40 * 7082802 * 2
def baseEnd_7082802 : Nat := 3636881806626302738301793

theorem tailTrace_7082802 : CollatzResearch.WordTrace tailWord_7082802 prefixEnd_7082802 3636881806626302738301793 := by
  unfold tailWord_7082802
  simp only [CollatzResearch.WordTrace]
  refine ⟨64582752921556368780462665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172220674457483650081233773 64582752921556368780462665)
  ·
    refine ⟨48437064691167276585346999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64582752921556368780462665 48437064691167276585346999)
    ·
      refine ⟨72655597036750914878020499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48437064691167276585346999 72655597036750914878020499)
      ·
        refine ⟨108983395555126372317030749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72655597036750914878020499 108983395555126372317030749)
        ·
          refine ⟨40868773333172389618886531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108983395555126372317030749 40868773333172389618886531)
          ·
            refine ⟨61303159999758584428329797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40868773333172389618886531 61303159999758584428329797)
            ·
              refine ⟨11494342499954734580311837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61303159999758584428329797 11494342499954734580311837)
              ·
                refine ⟨4310378437483025467616939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11494342499954734580311837 4310378437483025467616939)
                ·
                  refine ⟨6465567656224538201425409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310378437483025467616939 6465567656224538201425409)
                  ·
                    refine ⟨4849175742168403651069057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465567656224538201425409 4849175742168403651069057)
                    ·
                      refine ⟨3636881806626302738301793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849175742168403651069057 3636881806626302738301793)
                      ·
                        rfl

theorem cell23_7082802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_7082802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082802 prefixEnd_7082802 := by exact prefixLift 7082802
  have htrace : WordTrace (prefixWord ++ tailWord_7082802) baseStart_7082802 baseEnd_7082802 := by
    simpa [prefixWord, tailWord_7082802, baseEnd_7082802] using wordTrace_append hprefix tailTrace_7082802
  have hstable : (prefixWord ++ tailWord_7082802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082802).length < 2 ^ (prefixWord ++ tailWord_7082802).sum := by decide
  have hdescent : baseEnd_7082802 < baseStart_7082802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082805 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_7082805 : Nat := 118140960795 + 7082805 * 2 ^ 59
def prefixEnd_7082805 : Nat := 4983230072969 + 3 ^ 40 * 7082805 * 2
def baseEnd_7082805 : Nat := 3636883347068266226564279

theorem tailTrace_7082805 : CollatzResearch.WordTrace tailWord_7082805 prefixEnd_7082805 3636883347068266226564279 := by
  unfold tailWord_7082805
  simp only [CollatzResearch.WordTrace]
  refine ⟨258331121105214606634209869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172220747403476404422806579 258331121105214606634209869)
  ·
    refine ⟨96874170414455477487828701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258331121105214606634209869 96874170414455477487828701)
    ·
      refine ⟨36327813905420804057935763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96874170414455477487828701 36327813905420804057935763)
      ·
        refine ⟨54491720858131206086903645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36327813905420804057935763 54491720858131206086903645)
        ·
          refine ⟨20434395321799202282588867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54491720858131206086903645 20434395321799202282588867)
          ·
            refine ⟨30651592982698803423883301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20434395321799202282588867 30651592982698803423883301)
            ·
              refine ⟨5747173684256025641978119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30651592982698803423883301 5747173684256025641978119)
              ·
                refine ⟨8620760526384038462967179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747173684256025641978119 8620760526384038462967179)
                ·
                  refine ⟨12931140789576057694450769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620760526384038462967179 12931140789576057694450769)
                  ·
                    refine ⟨9698355592182043270838077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12931140789576057694450769 9698355592182043270838077)
                    ·
                      refine ⟨3636883347068266226564279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698355592182043270838077 3636883347068266226564279)
                      ·
                        rfl

theorem cell23_7082805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_7082805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082805 prefixEnd_7082805 := by exact prefixLift 7082805
  have htrace : WordTrace (prefixWord ++ tailWord_7082805) baseStart_7082805 baseEnd_7082805 := by
    simpa [prefixWord, tailWord_7082805, baseEnd_7082805] using wordTrace_append hprefix tailTrace_7082805
  have hstable : (prefixWord ++ tailWord_7082805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082805).length < 2 ^ (prefixWord ++ tailWord_7082805).sum := by decide
  have hdescent : baseEnd_7082805 < baseStart_7082805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082861 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7082861 : Nat := 118140960795 + 7082861 * 2 ^ 59
def prefixEnd_7082861 : Nat := 4983230072969 + 3 ^ 40 * 7082861 * 2
def baseEnd_7082861 : Nat := 3636912101984918007464021

theorem tailTrace_7082861 : CollatzResearch.WordTrace tailWord_7082861 prefixEnd_7082861 3636912101984918007464021 := by
  unfold tailWord_7082861
  simp only [CollatzResearch.WordTrace]
  refine ⟨258333163593011728198248437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172222109062007818798832291 258333163593011728198248437)
  ·
    refine ⟨24218734086844849518585791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258333163593011728198248437 24218734086844849518585791)
    ·
      refine ⟨36328101130267274277878687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24218734086844849518585791 36328101130267274277878687)
      ·
        refine ⟨54492151695400911416818031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36328101130267274277878687 54492151695400911416818031)
        ·
          refine ⟨81738227543101367125227047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54492151695400911416818031 81738227543101367125227047)
          ·
            refine ⟨122607341314652050687840571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81738227543101367125227047 122607341314652050687840571)
            ·
              refine ⟨183911011971978076031760857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122607341314652050687840571 183911011971978076031760857)
              ·
                refine ⟨137933258978983557023820643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183911011971978076031760857 137933258978983557023820643)
                ·
                  refine ⟨206899888468475335535730965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137933258978983557023820643 206899888468475335535730965)
                  ·
                    refine ⟨9698432271959781353237389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 206899888468475335535730965 9698432271959781353237389)
                    ·
                      refine ⟨3636912101984918007464021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698432271959781353237389 3636912101984918007464021)
                      ·
                        rfl

theorem cell23_7082861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7082861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082861 prefixEnd_7082861 := by exact prefixLift 7082861
  have htrace : WordTrace (prefixWord ++ tailWord_7082861) baseStart_7082861 baseEnd_7082861 := by
    simpa [prefixWord, tailWord_7082861, baseEnd_7082861] using wordTrace_append hprefix tailTrace_7082861
  have hstable : (prefixWord ++ tailWord_7082861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082861).length < 2 ^ (prefixWord ++ tailWord_7082861).sum := by decide
  have hdescent : baseEnd_7082861 < baseStart_7082861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082864 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 9]
def baseStart_7082864 : Nat := 118140960795 + 7082864 * 2 ^ 59
def prefixEnd_7082864 : Nat := 4983230072969 + 3 ^ 40 * 7082864 * 2
def baseEnd_7082864 : Nat := 404101515825209055080723

theorem tailTrace_7082864 : CollatzResearch.WordTrace tailWord_7082864 prefixEnd_7082864 404101515825209055080723 := by
  unfold tailWord_7082864
  simp only [CollatzResearch.WordTrace]
  refine ⟨129166636506000429855303823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172222182008000573140405097 129166636506000429855303823)
  ·
    refine ⟨193749954759000644782955735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129166636506000429855303823 193749954759000644782955735)
    ·
      refine ⟨290624932138500967174433603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193749954759000644782955735 290624932138500967174433603)
      ·
        refine ⟨435937398207751450761650405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290624932138500967174433603 435937398207751450761650405)
        ·
          refine ⟨81738262163953397017809451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435937398207751450761650405 81738262163953397017809451)
          ·
            refine ⟨122607393245930095526714177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81738262163953397017809451 122607393245930095526714177)
            ·
              refine ⟨91955544934447571645035633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122607393245930095526714177 91955544934447571645035633)
              ·
                refine ⟨68966658700835678733776725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91955544934447571645035633 68966658700835678733776725)
                ·
                  refine ⟨404101515825209055080723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68966658700835678733776725 404101515825209055080723)
                  ·
                    rfl

theorem cell23_7082864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_7082864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082864 prefixEnd_7082864 := by exact prefixLift 7082864
  have htrace : WordTrace (prefixWord ++ tailWord_7082864) baseStart_7082864 baseEnd_7082864 := by
    simpa [prefixWord, tailWord_7082864, baseEnd_7082864] using wordTrace_append hprefix tailTrace_7082864
  have hstable : (prefixWord ++ tailWord_7082864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082864).length < 2 ^ (prefixWord ++ tailWord_7082864).sum := by decide
  have hdescent : baseEnd_7082864 < baseStart_7082864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082874 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_7082874 : Nat := 118140960795 + 7082874 * 2 ^ 59
def prefixEnd_7082874 : Nat := 4983230072969 + 3 ^ 40 * 7082874 * 2
def baseEnd_7082874 : Nat := 3636918777233426456601461

theorem tailTrace_7082874 : CollatzResearch.WordTrace tailWord_7082874 prefixEnd_7082874 3636918777233426456601461 := by
  unfold tailWord_7082874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64583409435491157854617919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172222425161309754278981117 64583409435491157854617919)
  ·
    refine ⟨96875114153236736781926879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64583409435491157854617919 96875114153236736781926879)
    ·
      refine ⟨145312671229855105172890319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96875114153236736781926879 145312671229855105172890319)
      ·
        refine ⟨217969006844782657759335479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145312671229855105172890319 217969006844782657759335479)
        ·
          refine ⟨326953510267173986639003219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217969006844782657759335479 326953510267173986639003219)
          ·
            refine ⟨490430265400760979958504829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326953510267173986639003219 490430265400760979958504829)
            ·
              refine ⟨183911349525285367484439311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490430265400760979958504829 183911349525285367484439311)
              ·
                refine ⟨275867024287928051226658967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183911349525285367484439311 275867024287928051226658967)
                ·
                  refine ⟨413800536431892076839988451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275867024287928051226658967 413800536431892076839988451)
                  ·
                    refine ⟨620700804647838115259982677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 413800536431892076839988451 620700804647838115259982677)
                    ·
                      refine ⟨3636918777233426456601461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 620700804647838115259982677 3636918777233426456601461)
                      ·
                        rfl

theorem cell23_7082874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_7082874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082874 prefixEnd_7082874 := by exact prefixLift 7082874
  have htrace : WordTrace (prefixWord ++ tailWord_7082874) baseStart_7082874 baseEnd_7082874 := by
    simpa [prefixWord, tailWord_7082874, baseEnd_7082874] using wordTrace_append hprefix tailTrace_7082874
  have hstable : (prefixWord ++ tailWord_7082874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082874).length < 2 ^ (prefixWord ++ tailWord_7082874).sum := by decide
  have hdescent : baseEnd_7082874 < baseStart_7082874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082891 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3]
def baseStart_7082891 : Nat := 118140960795 + 7082891 * 2 ^ 59
def prefixEnd_7082891 : Nat := 4983230072969 + 3 ^ 40 * 7082891 * 2
def baseEnd_7082891 : Nat := 3636927506404552890088883

theorem tailTrace_7082891 : CollatzResearch.WordTrace tailWord_7082891 prefixEnd_7082891 3636927506404552890088883 := by
  unfold tailWord_7082891
  simp only [CollatzResearch.WordTrace]
  refine ⟨258334257782903043321840527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172222838521935362214560351 258334257782903043321840527)
  ·
    refine ⟨387501386674354564982760791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258334257782903043321840527 387501386674354564982760791)
    ·
      refine ⟨581252080011531847474141187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387501386674354564982760791 581252080011531847474141187)
      ·
        refine ⟨871878120017297771211211781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581252080011531847474141187 871878120017297771211211781)
        ·
          refine ⟨163477147503243332102102209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 871878120017297771211211781 163477147503243332102102209)
          ·
            refine ⟨122607860627432499076576657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163477147503243332102102209 122607860627432499076576657)
            ·
              refine ⟨91955895470574374307432493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122607860627432499076576657 91955895470574374307432493)
              ·
                refine ⟨34483460801465390365287185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91955895470574374307432493 34483460801465390365287185)
                ·
                  refine ⟨25862595601099042773965389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34483460801465390365287185 25862595601099042773965389)
                  ·
                    refine ⟨9698473350412141040237021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25862595601099042773965389 9698473350412141040237021)
                    ·
                      refine ⟨3636927506404552890088883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698473350412141040237021 3636927506404552890088883)
                      ·
                        rfl

theorem cell23_7082891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3].length) (baseStart_7082891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082891 prefixEnd_7082891 := by exact prefixLift 7082891
  have htrace : WordTrace (prefixWord ++ tailWord_7082891) baseStart_7082891 baseEnd_7082891 := by
    simpa [prefixWord, tailWord_7082891, baseEnd_7082891] using wordTrace_append hprefix tailTrace_7082891
  have hstable : (prefixWord ++ tailWord_7082891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082891).length < 2 ^ (prefixWord ++ tailWord_7082891).sum := by decide
  have hdescent : baseEnd_7082891 < baseStart_7082891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082892 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_7082892 : Nat := 118140960795 + 7082892 * 2 ^ 59
def prefixEnd_7082892 : Nat := 4983230072969 + 3 ^ 40 * 7082892 * 2
def baseEnd_7082892 : Nat := 3636928019885207386176379

theorem tailTrace_7082892 : CollatzResearch.WordTrace tailWord_7082892 prefixEnd_7082892 3636928019885207386176379 := by
  unfold tailWord_7082892
  simp only [CollatzResearch.WordTrace]
  refine ⟨129167147127949710246313465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172222862837266280328417953 129167147127949710246313465)
  ·
    refine ⟨96875360345962282684735099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129167147127949710246313465 96875360345962282684735099)
    ·
      refine ⟨145313040518943424027102649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96875360345962282684735099 145313040518943424027102649)
      ·
        refine ⟨108984780389207568020326987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145313040518943424027102649 108984780389207568020326987)
        ·
          refine ⟨163477170583811352030490481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108984780389207568020326987 163477170583811352030490481)
          ·
            refine ⟨122607877937858514022867861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163477170583811352030490481 122607877937858514022867861)
            ·
              refine ⟨5747244278337117844821931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122607877937858514022867861 5747244278337117844821931)
              ·
                refine ⟨8620866417505676767232897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747244278337117844821931 8620866417505676767232897)
                ·
                  refine ⟨6465649813129257575424673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8620866417505676767232897 6465649813129257575424673)
                  ·
                    refine ⟨4849237359846943181568505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6465649813129257575424673 4849237359846943181568505)
                    ·
                      refine ⟨3636928019885207386176379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849237359846943181568505 3636928019885207386176379)
                      ·
                        rfl

theorem cell23_7082892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_7082892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082892 prefixEnd_7082892 := by exact prefixLift 7082892
  have htrace : WordTrace (prefixWord ++ tailWord_7082892) baseStart_7082892 baseEnd_7082892 := by
    simpa [prefixWord, tailWord_7082892, baseEnd_7082892] using wordTrace_append hprefix tailTrace_7082892
  have hstable : (prefixWord ++ tailWord_7082892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082892).length < 2 ^ (prefixWord ++ tailWord_7082892).sum := by decide
  have hdescent : baseEnd_7082892 < baseStart_7082892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082931 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4]
def baseStart_7082931 : Nat := 118140960795 + 7082931 * 2 ^ 59
def prefixEnd_7082931 : Nat := 4983230072969 + 3 ^ 40 * 7082931 * 2
def baseEnd_7082931 : Nat := 3636948045630732733588699

theorem tailTrace_7082931 : CollatzResearch.WordTrace tailWord_7082931 prefixEnd_7082931 3636948045630732733588699 := by
  unfold tailWord_7082931
  simp only [CollatzResearch.WordTrace]
  refine ⟨258335716702758130153296647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172223811135172086768864431 258335716702758130153296647)
  ·
    refine ⟨387503575054137195229944971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258335716702758130153296647 387503575054137195229944971)
    ·
      refine ⟨581255362581205792844917457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387503575054137195229944971 581255362581205792844917457)
      ·
        refine ⟨435941521935904344633688093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581255362581205792844917457 435941521935904344633688093)
        ·
          refine ⟨163478070725964129237633035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435941521935904344633688093 163478070725964129237633035)
          ·
            refine ⟨245217106088946193856449553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163478070725964129237633035 245217106088946193856449553)
            ·
              refine ⟨183912829566709645392337165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245217106088946193856449553 183912829566709645392337165)
              ·
                refine ⟨68967311087516117022126437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183912829566709645392337165 68967311087516117022126437)
                ·
                  refine ⟨12931370828909271941648707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68967311087516117022126437 12931370828909271941648707)
                  ·
                    refine ⟨19397056243363907912473061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12931370828909271941648707 19397056243363907912473061)
                    ·
                      refine ⟨3636948045630732733588699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19397056243363907912473061 3636948045630732733588699)
                      ·
                        rfl

theorem cell23_7082931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_7082931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082931 prefixEnd_7082931 := by exact prefixLift 7082931
  have htrace : WordTrace (prefixWord ++ tailWord_7082931) baseStart_7082931 baseEnd_7082931 := by
    simpa [prefixWord, tailWord_7082931, baseEnd_7082931] using wordTrace_append hprefix tailTrace_7082931
  have hstable : (prefixWord ++ tailWord_7082931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082931).length < 2 ^ (prefixWord ++ tailWord_7082931).sum := by decide
  have hdescent : baseEnd_7082931 < baseStart_7082931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082932 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 5]
def baseStart_7082932 : Nat := 118140960795 + 7082932 * 2 ^ 59
def prefixEnd_7082932 : Nat := 4983230072969 + 3 ^ 40 * 7082932 * 2
def baseEnd_7082932 : Nat := 404105395456820803297355

theorem tailTrace_7082932 : CollatzResearch.WordTrace tailWord_7082932 prefixEnd_7082932 404105395456820803297355 := by
  unfold tailWord_7082932
  simp only [CollatzResearch.WordTrace]
  refine ⟨129167876587877253662041525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172223835450503004882722033 129167876587877253662041525)
  ·
    refine ⟨12109488430113492530816393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129167876587877253662041525 12109488430113492530816393)
    ·
      refine ⟨9082116322585119398112295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12109488430113492530816393 9082116322585119398112295)
      ·
        refine ⟨13623174483877679097168443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9082116322585119398112295 13623174483877679097168443)
        ·
          refine ⟨20434761725816518645752665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13623174483877679097168443 20434761725816518645752665)
          ·
            refine ⟨15326071294362388984314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20434761725816518645752665 15326071294362388984314499)
            ·
              refine ⟨22989106941543583476471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15326071294362388984314499 22989106941543583476471749)
              ·
                refine ⟨4310457551539421901838453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22989106941543583476471749 4310457551539421901838453)
                ·
                  refine ⟨404105395456820803297355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310457551539421901838453 404105395456820803297355)
                  ·
                    rfl

theorem cell23_7082932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_7082932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082932 prefixEnd_7082932 := by exact prefixLift 7082932
  have htrace : WordTrace (prefixWord ++ tailWord_7082932) baseStart_7082932 baseEnd_7082932 := by
    simpa [prefixWord, tailWord_7082932, baseEnd_7082932] using wordTrace_append hprefix tailTrace_7082932
  have hstable : (prefixWord ++ tailWord_7082932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082932).length < 2 ^ (prefixWord ++ tailWord_7082932).sum := by decide
  have hdescent : baseEnd_7082932 < baseStart_7082932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082958 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_7082958 : Nat := 118140960795 + 7082958 * 2 ^ 59
def prefixEnd_7082958 : Nat := 4983230072969 + 3 ^ 40 * 7082958 * 2
def baseEnd_7082958 : Nat := 1212320636536134709317025

theorem tailTrace_7082958 : CollatzResearch.WordTrace tailWord_7082958 prefixEnd_7082958 1212320636536134709317025 := by
  unfold tailWord_7082958
  simp only [CollatzResearch.WordTrace]
  refine ⟨32292087684207539220566191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172224467649106875843019685 32292087684207539220566191)
  ·
    refine ⟨48438131526311308830849287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32292087684207539220566191 48438131526311308830849287)
    ·
      refine ⟨72657197289466963246273931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48438131526311308830849287 72657197289466963246273931)
      ·
        refine ⟨108985795934200444869410897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72657197289466963246273931 108985795934200444869410897)
        ·
          refine ⟨81739346950650333652058173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108985795934200444869410897 81739346950650333652058173)
          ·
            refine ⟨30652255106493875119521815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81739346950650333652058173 30652255106493875119521815)
            ·
              refine ⟨45978382659740812679282723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30652255106493875119521815 45978382659740812679282723)
              ·
                refine ⟨68967573989611219018924085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45978382659740812679282723 68967573989611219018924085)
                ·
                  refine ⟨6465710061526051783024133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68967573989611219018924085 6465710061526051783024133)
                  ·
                    refine ⟨1212320636536134709317025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465710061526051783024133 1212320636536134709317025)
                    ·
                      rfl

theorem cell23_7082958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_7082958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082958 prefixEnd_7082958 := by exact prefixLift 7082958
  have htrace : WordTrace (prefixWord ++ tailWord_7082958) baseStart_7082958 baseEnd_7082958 := by
    simpa [prefixWord, tailWord_7082958, baseEnd_7082958] using wordTrace_append hprefix tailTrace_7082958
  have hstable : (prefixWord ++ tailWord_7082958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082958).length < 2 ^ (prefixWord ++ tailWord_7082958).sum := by decide
  have hdescent : baseEnd_7082958 < baseStart_7082958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082968 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_7082968 : Nat := 118140960795 + 7082968 * 2 ^ 59
def prefixEnd_7082968 : Nat := 4983230072969 + 3 ^ 40 * 7082968 * 2
def baseEnd_7082968 : Nat := 3636967044414949088826029

theorem tailTrace_7082968 : CollatzResearch.WordTrace tailWord_7082968 prefixEnd_7082968 3636967044414949088826029 := by
  unfold tailWord_7082968
  simp only [CollatzResearch.WordTrace]
  refine ⟨129168533101812042736196779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172224710802416056981595705 129168533101812042736196779)
  ·
    refine ⟨193752799652718064104295169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129168533101812042736196779 193752799652718064104295169)
    ·
      refine ⟨145314599739538548078221377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193752799652718064104295169 145314599739538548078221377)
      ·
        refine ⟨108985949804653911058666033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145314599739538548078221377 108985949804653911058666033)
        ·
          refine ⟨81739462353490433293999525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108985949804653911058666033 81739462353490433293999525)
          ·
            refine ⟨15326149191279456242624911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81739462353490433293999525 15326149191279456242624911)
            ·
              refine ⟨22989223786919184363937367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15326149191279456242624911 22989223786919184363937367)
              ·
                refine ⟨34483835680378776545906051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22989223786919184363937367 34483835680378776545906051)
                ·
                  refine ⟨51725753520568164818859077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34483835680378776545906051 51725753520568164818859077)
                  ·
                    refine ⟨9698578785106530903536077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51725753520568164818859077 9698578785106530903536077)
                    ·
                      refine ⟨3636967044414949088826029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698578785106530903536077 3636967044414949088826029)
                      ·
                        rfl

theorem cell23_7082968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_7082968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082968 prefixEnd_7082968 := by exact prefixLift 7082968
  have htrace : WordTrace (prefixWord ++ tailWord_7082968) baseStart_7082968 baseEnd_7082968 := by
    simpa [prefixWord, tailWord_7082968, baseEnd_7082968] using wordTrace_append hprefix tailTrace_7082968
  have hstable : (prefixWord ++ tailWord_7082968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082968).length < 2 ^ (prefixWord ++ tailWord_7082968).sum := by decide
  have hdescent : baseEnd_7082968 < baseStart_7082968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7082991 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_7082991 : Nat := 118140960795 + 7082991 * 2 ^ 59
def prefixEnd_7082991 : Nat := 4983230072969 + 3 ^ 40 * 7082991 * 2
def baseEnd_7082991 : Nat := 3636978854470002498838423

theorem tailTrace_7082991 : CollatzResearch.WordTrace tailWord_7082991 prefixEnd_7082991 3636978854470002498838423 := by
  unfold tailWord_7082991
  simp only [CollatzResearch.WordTrace]
  refine ⟨258337905082540760400480827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172225270055027173600320551 258337905082540760400480827)
  ·
    refine ⟨387506857623811140600721241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258337905082540760400480827 387506857623811140600721241)
    ·
      refine ⟨290630143217858355450540931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387506857623811140600721241 290630143217858355450540931)
      ·
        refine ⟨435945214826787533175811397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290630143217858355450540931 435945214826787533175811397)
        ·
          refine ⟨81739727780022662470464637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435945214826787533175811397 81739727780022662470464637)
          ·
            refine ⟨30652397917508498426424239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81739727780022662470464637 30652397917508498426424239)
            ·
              refine ⟨45978596876262747639636359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30652397917508498426424239 45978596876262747639636359)
              ·
                refine ⟨68967895314394121459454539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45978596876262747639636359 68967895314394121459454539)
                ·
                  refine ⟨103451842971591182189181809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68967895314394121459454539 103451842971591182189181809)
                  ·
                    refine ⟨77588882228693386641886357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103451842971591182189181809 77588882228693386641886357)
                    ·
                      refine ⟨3636978854470002498838423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77588882228693386641886357 3636978854470002498838423)
                      ·
                        rfl

theorem cell23_7082991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_7082991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7082991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7082991 prefixEnd_7082991 := by exact prefixLift 7082991
  have htrace : WordTrace (prefixWord ++ tailWord_7082991) baseStart_7082991 baseEnd_7082991 := by
    simpa [prefixWord, tailWord_7082991, baseEnd_7082991] using wordTrace_append hprefix tailTrace_7082991
  have hstable : (prefixWord ++ tailWord_7082991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7082991).length < 2 ^ (prefixWord ++ tailWord_7082991).sum := by decide
  have hdescent : baseEnd_7082991 < baseStart_7082991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7082991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083015 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_7083015 : Nat := 118140960795 + 7083015 * 2 ^ 59
def prefixEnd_7083015 : Nat := 4983230072969 + 3 ^ 40 * 7083015 * 2
def baseEnd_7083015 : Nat := 3636991178005710404938313

theorem tailTrace_7083015 : CollatzResearch.WordTrace tailWord_7083015 prefixEnd_7083015 3636991178005710404938313 := by
  unfold tailWord_7083015
  simp only [CollatzResearch.WordTrace]
  refine ⟨258338780434453812499354499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172225853622969208332902999 258338780434453812499354499)
  ·
    refine ⟨387508170651680718749031749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258338780434453812499354499 387508170651680718749031749)
    ·
      refine ⟨72657781997190134765443453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387508170651680718749031749 72657781997190134765443453)
      ·
        refine ⟨27246668248946300537041295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72657781997190134765443453 27246668248946300537041295)
        ·
          refine ⟨40870002373419450805561943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27246668248946300537041295 40870002373419450805561943)
          ·
            refine ⟨61305003560129176208342915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40870002373419450805561943 61305003560129176208342915)
            ·
              refine ⟨91957505340193764312514373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61305003560129176208342915 91957505340193764312514373)
              ·
                refine ⟨17242032251286330808596445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91957505340193764312514373 17242032251286330808596445)
                ·
                  refine ⟨6465762094232374053223667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17242032251286330808596445 6465762094232374053223667)
                  ·
                    refine ⟨9698643141348561079835501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6465762094232374053223667 9698643141348561079835501)
                    ·
                      refine ⟨3636991178005710404938313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698643141348561079835501 3636991178005710404938313)
                      ·
                        rfl

theorem cell23_7083015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_7083015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083015 prefixEnd_7083015 := by exact prefixLift 7083015
  have htrace : WordTrace (prefixWord ++ tailWord_7083015) baseStart_7083015 baseEnd_7083015 := by
    simpa [prefixWord, tailWord_7083015, baseEnd_7083015] using wordTrace_append hprefix tailTrace_7083015
  have hstable : (prefixWord ++ tailWord_7083015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083015).length < 2 ^ (prefixWord ++ tailWord_7083015).sum := by decide
  have hdescent : baseEnd_7083015 < baseStart_7083015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083042 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_7083042 : Nat := 118140960795 + 7083042 * 2 ^ 59
def prefixEnd_7083042 : Nat := 4983230072969 + 3 ^ 40 * 7083042 * 2
def baseEnd_7083042 : Nat := 3637005041983381799300689

theorem tailTrace_7083042 : CollatzResearch.WordTrace tailWord_7083042 prefixEnd_7083042 3637005041983381799300689 := by
  unfold tailWord_7083042
  simp only [CollatzResearch.WordTrace]
  refine ⟨64584941301338999027646845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172226510136903997407058253 64584941301338999027646845)
  ·
    refine ⟨24219352988002124635367567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64584941301338999027646845 24219352988002124635367567)
    ·
      refine ⟨36329029482003186953051351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24219352988002124635367567 36329029482003186953051351)
      ·
        refine ⟨54493544223004780429577027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36329029482003186953051351 54493544223004780429577027)
        ·
          refine ⟨81740316334507170644365541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54493544223004780429577027 81740316334507170644365541)
          ·
            refine ⟨15326309312720094495818539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81740316334507170644365541 15326309312720094495818539)
            ·
              refine ⟨22989463969080141743727809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15326309312720094495818539 22989463969080141743727809)
              ·
                refine ⟨17242097976810106307795857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22989463969080141743727809 17242097976810106307795857)
                ·
                  refine ⟨12931573482607579730846893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17242097976810106307795857 12931573482607579730846893)
                  ·
                    refine ⟨4849340055977842399067585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12931573482607579730846893 4849340055977842399067585)
                    ·
                      refine ⟨3637005041983381799300689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849340055977842399067585 3637005041983381799300689)
                      ·
                        rfl

theorem cell23_7083042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_7083042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083042 prefixEnd_7083042 := by exact prefixLift 7083042
  have htrace : WordTrace (prefixWord ++ tailWord_7083042) baseStart_7083042 baseEnd_7083042 := by
    simpa [prefixWord, tailWord_7083042, baseEnd_7083042] using wordTrace_append hprefix tailTrace_7083042
  have hstable : (prefixWord ++ tailWord_7083042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083042).length < 2 ^ (prefixWord ++ tailWord_7083042).sum := by decide
  have hdescent : baseEnd_7083042 < baseStart_7083042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083051 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_7083051 : Nat := 118140960795 + 7083051 * 2 ^ 59
def prefixEnd_7083051 : Nat := 4983230072969 + 3 ^ 40 * 7083051 * 2
def baseEnd_7083051 : Nat := 3637009663309272264088147

theorem tailTrace_7083051 : CollatzResearch.WordTrace tailWord_7083051 prefixEnd_7083051 3637009663309272264088147 := by
  unfold tailWord_7083051
  simp only [CollatzResearch.WordTrace]
  refine ⟨258340093462323390647665007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172226728974882260431776671 258340093462323390647665007)
  ·
    refine ⟨387510140193485085971497511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258340093462323390647665007 387510140193485085971497511)
    ·
      refine ⟨581265210290227628957246267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387510140193485085971497511 581265210290227628957246267)
      ·
        refine ⟨871897815435341443435869401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581265210290227628957246267 871897815435341443435869401)
        ·
          refine ⟨653923361576506082576902051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871897815435341443435869401 653923361576506082576902051)
          ·
            refine ⟨980885042364759123865353077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653923361576506082576902051 980885042364759123865353077)
            ·
              refine ⟨91957972721696167862376851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 980885042364759123865353077 91957972721696167862376851)
              ·
                refine ⟨137936959082544251793565277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91957972721696167862376851 137936959082544251793565277)
                ·
                  refine ⟨51726359655954094422586979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137936959082544251793565277 51726359655954094422586979)
                  ·
                    refine ⟨77589539483931141633880469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51726359655954094422586979 77589539483931141633880469)
                    ·
                      refine ⟨3637009663309272264088147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77589539483931141633880469 3637009663309272264088147)
                      ·
                        rfl

theorem cell23_7083051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_7083051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083051 prefixEnd_7083051 := by exact prefixLift 7083051
  have htrace : WordTrace (prefixWord ++ tailWord_7083051) baseStart_7083051 baseEnd_7083051 := by
    simpa [prefixWord, tailWord_7083051, baseEnd_7083051] using wordTrace_append hprefix tailTrace_7083051
  have hstable : (prefixWord ++ tailWord_7083051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083051).length < 2 ^ (prefixWord ++ tailWord_7083051).sum := by decide
  have hdescent : baseEnd_7083051 < baseStart_7083051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083058 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7083058 : Nat := 118140960795 + 7083058 * 2 ^ 59
def prefixEnd_7083058 : Nat := 4983230072969 + 3 ^ 40 * 7083058 * 2
def baseEnd_7083058 : Nat := 3637013257673853736700615

theorem tailTrace_7083058 : CollatzResearch.WordTrace tailWord_7083058 prefixEnd_7083058 3637013257673853736700615 := by
  unfold tailWord_7083058
  simp only [CollatzResearch.WordTrace]
  refine ⟨64585087193324507710792457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172226899182198687228779885 64585087193324507710792457)
  ·
    refine ⟨48438815394993380783094343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64585087193324507710792457 48438815394993380783094343)
    ·
      refine ⟨72658223092490071174641515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48438815394993380783094343 72658223092490071174641515)
      ·
        refine ⟨108987334638735106761962273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72658223092490071174641515 108987334638735106761962273)
        ·
          refine ⟨81740500979051330071471705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108987334638735106761962273 81740500979051330071471705)
          ·
            refine ⟨61305375734288497553603779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81740500979051330071471705 61305375734288497553603779)
            ·
              refine ⟨91958063601432746330405669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61305375734288497553603779 91958063601432746330405669)
              ·
                refine ⟨17242136925268639936951063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91958063601432746330405669 17242136925268639936951063)
                ·
                  refine ⟨25863205387902959905426595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17242136925268639936951063 25863205387902959905426595)
                  ·
                    refine ⟨38794808081854439858139893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25863205387902959905426595 38794808081854439858139893)
                    ·
                      refine ⟨3637013257673853736700615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38794808081854439858139893 3637013257673853736700615)
                      ·
                        rfl

theorem cell23_7083058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7083058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083058 prefixEnd_7083058 := by exact prefixLift 7083058
  have htrace : WordTrace (prefixWord ++ tailWord_7083058) baseStart_7083058 baseEnd_7083058 := by
    simpa [prefixWord, tailWord_7083058, baseEnd_7083058] using wordTrace_append hprefix tailTrace_7083058
  have hstable : (prefixWord ++ tailWord_7083058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083058).length < 2 ^ (prefixWord ++ tailWord_7083058).sum := by decide
  have hdescent : baseEnd_7083058 < baseStart_7083058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083068 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_7083068 : Nat := 118140960795 + 7083068 * 2 ^ 59
def prefixEnd_7083068 : Nat := 4983230072969 + 3 ^ 40 * 7083068 * 2
def baseEnd_7083068 : Nat := 3637018392480398697575569

theorem tailTrace_7083068 : CollatzResearch.WordTrace tailWord_7083068 prefixEnd_7083068 3637018392480398697575569 := by
  unfold tailWord_7083068
  simp only [CollatzResearch.WordTrace]
  refine ⟨129170356751630901275516929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172227142335507868367355905 129170356751630901275516929)
  ·
    refine ⟨96877767563723175956637697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129170356751630901275516929 96877767563723175956637697)
    ·
      refine ⟨72658325672792381967478273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96877767563723175956637697 72658325672792381967478273)
      ·
        refine ⟨54493744254594286475608705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72658325672792381967478273 54493744254594286475608705)
        ·
          refine ⟨40870308190945714856706529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54493744254594286475608705 40870308190945714856706529)
          ·
            refine ⟨30652731143209286142529897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40870308190945714856706529 30652731143209286142529897)
            ·
              refine ⟨22989548357406964606897423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30652731143209286142529897 22989548357406964606897423)
              ·
                refine ⟨34484322536110446910346135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22989548357406964606897423 34484322536110446910346135)
                ·
                  refine ⟨51726483804165670365519203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34484322536110446910346135 51726483804165670365519203)
                  ·
                    refine ⟨77589725706248505548278805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51726483804165670365519203 77589725706248505548278805)
                    ·
                      refine ⟨3637018392480398697575569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77589725706248505548278805 3637018392480398697575569)
                      ·
                        rfl

theorem cell23_7083068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_7083068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083068 prefixEnd_7083068 := by exact prefixLift 7083068
  have htrace : WordTrace (prefixWord ++ tailWord_7083068) baseStart_7083068 baseEnd_7083068 := by
    simpa [prefixWord, tailWord_7083068, baseEnd_7083068] using wordTrace_append hprefix tailTrace_7083068
  have hstable : (prefixWord ++ tailWord_7083068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083068).length < 2 ^ (prefixWord ++ tailWord_7083068).sum := by decide
  have hdescent : baseEnd_7083068 < baseStart_7083068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083085 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7083085 : Nat := 118140960795 + 7083085 * 2 ^ 59
def prefixEnd_7083085 : Nat := 4983230072969 + 3 ^ 40 * 7083085 * 2
def baseEnd_7083085 : Nat := 3637027121651525131062991

theorem tailTrace_7083085 : CollatzResearch.WordTrace tailWord_7083085 prefixEnd_7083085 3637027121651525131062991 := by
  unfold tailWord_7083085
  simp only [CollatzResearch.WordTrace]
  refine ⟨258341333544200214454402709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172227555696133476302935139 258341333544200214454402709)
  ·
    refine ⟨12109750009884385052550127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258341333544200214454402709 12109750009884385052550127)
    ·
      refine ⟨18164625014826577578825191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12109750009884385052550127 18164625014826577578825191)
      ·
        refine ⟨27246937522239866368237787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18164625014826577578825191 27246937522239866368237787)
        ·
          refine ⟨40870406283359799552356681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27246937522239866368237787 40870406283359799552356681)
          ·
            refine ⟨30652804712519849664267511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40870406283359799552356681 30652804712519849664267511)
            ·
              refine ⟨45979207068779774496401267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30652804712519849664267511 45979207068779774496401267)
              ·
                refine ⟨68968810603169661744601901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45979207068779774496401267 68968810603169661744601901)
                ·
                  refine ⟨25863303976188623154225713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68968810603169661744601901 25863303976188623154225713)
                  ·
                    refine ⟨19397477982141467365669285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25863303976188623154225713 19397477982141467365669285)
                    ·
                      refine ⟨3637027121651525131062991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19397477982141467365669285 3637027121651525131062991)
                      ·
                        rfl

theorem cell23_7083085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7083085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083085 prefixEnd_7083085 := by exact prefixLift 7083085
  have htrace : WordTrace (prefixWord ++ tailWord_7083085) baseStart_7083085 baseEnd_7083085 := by
    simpa [prefixWord, tailWord_7083085, baseEnd_7083085] using wordTrace_append hprefix tailTrace_7083085
  have hstable : (prefixWord ++ tailWord_7083085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083085).length < 2 ^ (prefixWord ++ tailWord_7083085).sum := by decide
  have hdescent : baseEnd_7083085 < baseStart_7083085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083091 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 9]
def baseStart_7083091 : Nat := 118140960795 + 7083091 * 2 ^ 59
def prefixEnd_7083091 : Nat := 4983230072969 + 3 ^ 40 * 7083091 * 2
def baseEnd_7083091 : Nat := 1212343400845150702529321

theorem tailTrace_7083091 : CollatzResearch.WordTrace tailWord_7083091 prefixEnd_7083091 1212343400845150702529321 := by
  unfold tailWord_7083091
  simp only [CollatzResearch.WordTrace]
  refine ⟨258341552382178477479121127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172227701588118984986080751 258341552382178477479121127)
  ·
    refine ⟨387512328573267716218681691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258341552382178477479121127 387512328573267716218681691)
    ·
      refine ⟨581268492859901574328022537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387512328573267716218681691 581268492859901574328022537)
      ·
        refine ⟨435951369644926180746016903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581268492859901574328022537 435951369644926180746016903)
        ·
          refine ⟨653927054467389271119025355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435951369644926180746016903 653927054467389271119025355)
          ·
            refine ⟨980890581701083906678538033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653927054467389271119025355 980890581701083906678538033)
            ·
              refine ⟨735667936275812930008903525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980890581701083906678538033 735667936275812930008903525)
              ·
                refine ⟨137937738051714924376669411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735667936275812930008903525 137937738051714924376669411)
                ·
                  refine ⟨206906607077572386565004117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137937738051714924376669411 206906607077572386565004117)
                  ·
                    refine ⟨1212343400845150702529321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206906607077572386565004117 1212343400845150702529321)
                    ·
                      rfl

theorem cell23_7083091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_7083091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083091 prefixEnd_7083091 := by exact prefixLift 7083091
  have htrace : WordTrace (prefixWord ++ tailWord_7083091) baseStart_7083091 baseEnd_7083091 := by
    simpa [prefixWord, tailWord_7083091, baseEnd_7083091] using wordTrace_append hprefix tailTrace_7083091
  have hstable : (prefixWord ++ tailWord_7083091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083091).length < 2 ^ (prefixWord ++ tailWord_7083091).sum := by decide
  have hdescent : baseEnd_7083091 < baseStart_7083091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083105 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_7083105 : Nat := 118140960795 + 7083105 * 2 ^ 59
def prefixEnd_7083105 : Nat := 4983230072969 + 3 ^ 40 * 7083105 * 2
def baseEnd_7083105 : Nat := 3637037391264615052812899

theorem tailTrace_7083105 : CollatzResearch.WordTrace tailWord_7083105 prefixEnd_7083105 3637037391264615052812899 := by
  unfold tailWord_7083105
  simp only [CollatzResearch.WordTrace]
  refine ⟨258342063004127757870130769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172228042002751838580087179 258342063004127757870130769)
  ·
    refine ⟨193756547253095818402598077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258342063004127757870130769 193756547253095818402598077)
    ·
      refine ⟨72658705219910931900974279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193756547253095818402598077 72658705219910931900974279)
      ·
        refine ⟨108988057829866397851461419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72658705219910931900974279 108988057829866397851461419)
        ·
          refine ⟨163482086744799596777192129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108988057829866397851461419 163482086744799596777192129)
          ·
            refine ⟨122611565058599697582894097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163482086744799596777192129 122611565058599697582894097)
            ·
              refine ⟨91958673793949773187170573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122611565058599697582894097 91958673793949773187170573)
              ·
                refine ⟨34484502672731164945188965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91958673793949773187170573 34484502672731164945188965)
                ·
                  refine ⟨6465844251137093427222931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34484502672731164945188965 6465844251137093427222931)
                  ·
                    refine ⟨9698766376705640140834397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6465844251137093427222931 9698766376705640140834397)
                    ·
                      refine ⟨3637037391264615052812899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698766376705640140834397 3637037391264615052812899)
                      ·
                        rfl

theorem cell23_7083105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_7083105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083105 prefixEnd_7083105 := by exact prefixLift 7083105
  have htrace : WordTrace (prefixWord ++ tailWord_7083105) baseStart_7083105 baseEnd_7083105 := by
    simpa [prefixWord, tailWord_7083105, baseEnd_7083105] using wordTrace_append hprefix tailTrace_7083105
  have hstable : (prefixWord ++ tailWord_7083105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083105).length < 2 ^ (prefixWord ++ tailWord_7083105).sum := by decide
  have hdescent : baseEnd_7083105 < baseStart_7083105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083112 : List Nat := [2, 1, 4, 4, 1, 2, 1, 8]
def baseStart_7083112 : Nat := 118140960795 + 7083112 * 2 ^ 59
def prefixEnd_7083112 : Nat := 4983230072969 + 3 ^ 40 * 7083112 * 2
def baseEnd_7083112 : Nat := 134705221689970241682421

theorem tailTrace_7083112 : CollatzResearch.WordTrace tailWord_7083112 prefixEnd_7083112 134705221689970241682421 := by
  unfold tailWord_7083112
  simp only [CollatzResearch.WordTrace]
  refine ⟨129171159157551199032817795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172228212210068265377090393 129171159157551199032817795)
  ·
    refine ⟨193756738736326798549226693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129171159157551199032817795 193756738736326798549226693)
    ·
      refine ⟨36329388513061274727980005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193756738736326798549226693 36329388513061274727980005)
      ·
        refine ⟨6811760346198989011496251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36329388513061274727980005 6811760346198989011496251)
        ·
          refine ⟨10217640519298483517244377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811760346198989011496251 10217640519298483517244377)
          ·
            refine ⟨7663230389473862637933283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10217640519298483517244377 7663230389473862637933283)
            ·
              refine ⟨11494845584210793956899925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663230389473862637933283 11494845584210793956899925)
              ·
                refine ⟨134705221689970241682421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11494845584210793956899925 134705221689970241682421)
                ·
                  rfl

theorem cell23_7083112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 8].length) (baseStart_7083112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083112 prefixEnd_7083112 := by exact prefixLift 7083112
  have htrace : WordTrace (prefixWord ++ tailWord_7083112) baseStart_7083112 baseEnd_7083112 := by
    simpa [prefixWord, tailWord_7083112, baseEnd_7083112] using wordTrace_append hprefix tailTrace_7083112
  have hstable : (prefixWord ++ tailWord_7083112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083112).length < 2 ^ (prefixWord ++ tailWord_7083112).sum := by decide
  have hdescent : baseEnd_7083112 < baseStart_7083112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083122 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7083122 : Nat := 118140960795 + 7083122 * 2 ^ 59
def prefixEnd_7083122 : Nat := 4983230072969 + 3 ^ 40 * 7083122 * 2
def baseEnd_7083122 : Nat := 3637046120435741486300321

theorem tailTrace_7083122 : CollatzResearch.WordTrace tailWord_7083122 prefixEnd_7083122 3637046120435741486300321 := by
  unfold tailWord_7083122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64585670761266542443374905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172228455363377446515666413 64585670761266542443374905)
  ·
    refine ⟨48439253070949906832531179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64585670761266542443374905 48439253070949906832531179)
    ·
      refine ⟨72658879606424860248796769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48439253070949906832531179 72658879606424860248796769)
      ·
        refine ⟨54494159704818645186597577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72658879606424860248796769 54494159704818645186597577)
        ·
          refine ⟨40870619778613983889948183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54494159704818645186597577 40870619778613983889948183)
          ·
            refine ⟨61305929667920975834922275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40870619778613983889948183 61305929667920975834922275)
            ·
              refine ⟨91958894501881463752383413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61305929667920975834922275 91958894501881463752383413)
              ·
                refine ⟨8621146359551387226785945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91958894501881463752383413 8621146359551387226785945)
                ·
                  refine ⟨6465859769663540420089459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8621146359551387226785945 6465859769663540420089459)
                  ·
                    refine ⟨9698789654495310630134189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6465859769663540420089459 9698789654495310630134189)
                    ·
                      refine ⟨3637046120435741486300321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698789654495310630134189 3637046120435741486300321)
                      ·
                        rfl

theorem cell23_7083122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7083122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083122 prefixEnd_7083122 := by exact prefixLift 7083122
  have htrace : WordTrace (prefixWord ++ tailWord_7083122) baseStart_7083122 baseEnd_7083122 := by
    simpa [prefixWord, tailWord_7083122, baseEnd_7083122] using wordTrace_append hprefix tailTrace_7083122
  have hstable : (prefixWord ++ tailWord_7083122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083122).length < 2 ^ (prefixWord ++ tailWord_7083122).sum := by decide
  have hdescent : baseEnd_7083122 < baseStart_7083122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083132 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_7083132 : Nat := 118140960795 + 7083132 * 2 ^ 59
def prefixEnd_7083132 : Nat := 4983230072969 + 3 ^ 40 * 7083132 * 2
def baseEnd_7083132 : Nat := 3637051255242286447175275

theorem tailTrace_7083132 : CollatzResearch.WordTrace tailWord_7083132 prefixEnd_7083132 3637051255242286447175275 := by
  unfold tailWord_7083132
  simp only [CollatzResearch.WordTrace]
  refine ⟨129171523887514970740681825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172228698516686627654242433 129171523887514970740681825)
  ·
    refine ⟨96878642915636228055511369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129171523887514970740681825 96878642915636228055511369)
    ·
      refine ⟨72658982186727171041633527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96878642915636228055511369 72658982186727171041633527)
      ·
        refine ⟨108988473280090756562450291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72658982186727171041633527 108988473280090756562450291)
        ·
          refine ⟨163482709920136134843675437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108988473280090756562450291 163482709920136134843675437)
          ·
            refine ⟨61306016220051050566378289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163482709920136134843675437 61306016220051050566378289)
            ·
              refine ⟨45979512165038287924783717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61306016220051050566378289 45979512165038287924783717)
              ·
                refine ⟨8621158530944678985896947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45979512165038287924783717 8621158530944678985896947)
                ·
                  refine ⟨12931737796417018478845421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621158530944678985896947 12931737796417018478845421)
                  ·
                    refine ⟨4849401673656381929567033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12931737796417018478845421 4849401673656381929567033)
                    ·
                      refine ⟨3637051255242286447175275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849401673656381929567033 3637051255242286447175275)
                      ·
                        rfl

theorem cell23_7083132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_7083132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083132 prefixEnd_7083132 := by exact prefixLift 7083132
  have htrace : WordTrace (prefixWord ++ tailWord_7083132) baseStart_7083132 baseEnd_7083132 := by
    simpa [prefixWord, tailWord_7083132, baseEnd_7083132] using wordTrace_append hprefix tailTrace_7083132
  have hstable : (prefixWord ++ tailWord_7083132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083132).length < 2 ^ (prefixWord ++ tailWord_7083132).sum := by decide
  have hdescent : baseEnd_7083132 < baseStart_7083132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083148 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7083148 : Nat := 118140960795 + 7083148 * 2 ^ 59
def prefixEnd_7083148 : Nat := 4983230072969 + 3 ^ 40 * 7083148 * 2
def baseEnd_7083148 : Nat := 3637059470932758384575201

theorem tailTrace_7083148 : CollatzResearch.WordTrace tailWord_7083148 prefixEnd_7083148 3637059470932758384575201 := by
  unfold tailWord_7083148
  simp only [CollatzResearch.WordTrace]
  refine ⟨129171815671485988106973049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172229087561981317475964065 129171815671485988106973049)
  ·
    refine ⟨96878861753614491080229787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129171815671485988106973049 96878861753614491080229787)
    ·
      refine ⟨145318292630421736620344681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96878861753614491080229787 145318292630421736620344681)
      ·
        refine ⟨108988719472816302465258511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145318292630421736620344681 108988719472816302465258511)
        ·
          refine ⟨163483079209224453697887767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108988719472816302465258511 163483079209224453697887767)
          ·
            refine ⟨245224618813836680546831651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163483079209224453697887767 245224618813836680546831651)
            ·
              refine ⟨367836928220755020820247477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245224618813836680546831651 367836928220755020820247477)
              ·
                refine ⟨34484712020695783201898201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367836928220755020820247477 34484712020695783201898201)
                ·
                  refine ⟨25863534015521837401423651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34484712020695783201898201 25863534015521837401423651)
                  ·
                    refine ⟨38795301023282756102135477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25863534015521837401423651 38795301023282756102135477)
                    ·
                      refine ⟨3637059470932758384575201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38795301023282756102135477 3637059470932758384575201)
                      ·
                        rfl

theorem cell23_7083148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7083148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083148 prefixEnd_7083148 := by exact prefixLift 7083148
  have htrace : WordTrace (prefixWord ++ tailWord_7083148) baseStart_7083148 baseEnd_7083148 := by
    simpa [prefixWord, tailWord_7083148, baseEnd_7083148] using wordTrace_append hprefix tailTrace_7083148
  have hstable : (prefixWord ++ tailWord_7083148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083148).length < 2 ^ (prefixWord ++ tailWord_7083148).sum := by decide
  have hdescent : baseEnd_7083148 < baseStart_7083148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083185 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 7]
def baseStart_7083185 : Nat := 118140960795 + 7083185 * 2 ^ 59
def prefixEnd_7083185 : Nat := 4983230072969 + 3 ^ 40 * 7083185 * 2
def baseEnd_7083185 : Nat := 404119829968552748868059

theorem tailTrace_7083185 : CollatzResearch.WordTrace tailWord_7083185 prefixEnd_7083185 404119829968552748868059 := by
  unfold tailWord_7083185
  simp only [CollatzResearch.WordTrace]
  refine ⟨258344980843837931533043009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172229987229225287688695339 258344980843837931533043009)
  ·
    refine ⟨193758735632878448649782257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258344980843837931533043009 193758735632878448649782257)
    ·
      refine ⟨145319051724658836487336693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193758735632878448649782257 145319051724658836487336693)
      ·
        refine ⟨13623661099186765920687815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145319051724658836487336693 13623661099186765920687815)
        ·
          refine ⟨20435491648780148881031723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13623661099186765920687815 20435491648780148881031723)
          ·
            refine ⟨30653237473170223321547585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20435491648780148881031723 30653237473170223321547585)
            ·
              refine ⟨22989928104877667491160689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30653237473170223321547585 22989928104877667491160689)
              ·
                refine ⟨17242446078658250618370517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22989928104877667491160689 17242446078658250618370517)
                ·
                  refine ⟨404119829968552748868059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17242446078658250618370517 404119829968552748868059)
                  ·
                    rfl

theorem cell23_7083185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_7083185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083185 prefixEnd_7083185 := by exact prefixLift 7083185
  have htrace : WordTrace (prefixWord ++ tailWord_7083185) baseStart_7083185 baseEnd_7083185 := by
    simpa [prefixWord, tailWord_7083185, baseEnd_7083185] using wordTrace_append hprefix tailTrace_7083185
  have hstable : (prefixWord ++ tailWord_7083185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083185).length < 2 ^ (prefixWord ++ tailWord_7083185).sum := by decide
  have hdescent : baseEnd_7083185 < baseStart_7083185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083205 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_7083205 : Nat := 118140960795 + 7083205 * 2 ^ 59
def prefixEnd_7083205 : Nat := 4983230072969 + 3 ^ 40 * 7083205 * 2
def baseEnd_7083205 : Nat := 3637088739330064661562439

theorem tailTrace_7083205 : CollatzResearch.WordTrace tailWord_7083205 prefixEnd_7083205 3637088739330064661562439 := by
  unfold tailWord_7083205
  simp only [CollatzResearch.WordTrace]
  refine ⟨258345710303765474948771069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172230473535843649965847379 258345710303765474948771069)
  ·
    refine ⟨96879641363912053105789151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258345710303765474948771069 96879641363912053105789151)
    ·
      refine ⟨145319462045868079658683727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96879641363912053105789151 145319462045868079658683727)
      ·
        refine ⟨217979193068802119488025591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145319462045868079658683727 217979193068802119488025591)
        ·
          refine ⟨326968789603203179232038387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217979193068802119488025591 326968789603203179232038387)
          ·
            refine ⟨490453184404804768848057581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326968789603203179232038387 490453184404804768848057581)
            ·
              refine ⟨183919944151801788318021593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490453184404804768848057581 183919944151801788318021593)
              ·
                refine ⟨137939958113851341238516195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183919944151801788318021593 137939958113851341238516195)
                ·
                  refine ⟨206909937170777011857774293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137939958113851341238516195 206909937170777011857774293)
                  ·
                    refine ⟨4849451652440086215416585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206909937170777011857774293 4849451652440086215416585)
                    ·
                      refine ⟨3637088739330064661562439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849451652440086215416585 3637088739330064661562439)
                      ·
                        rfl

theorem cell23_7083205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_7083205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083205 prefixEnd_7083205 := by exact prefixLift 7083205
  have htrace : WordTrace (prefixWord ++ tailWord_7083205) baseStart_7083205 baseEnd_7083205 := by
    simpa [prefixWord, tailWord_7083205, baseEnd_7083205] using wordTrace_append hprefix tailTrace_7083205
  have hstable : (prefixWord ++ tailWord_7083205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083205).length < 2 ^ (prefixWord ++ tailWord_7083205).sum := by decide
  have hdescent : baseEnd_7083205 < baseStart_7083205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083248 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_7083248 : Nat := 118140960795 + 7083248 * 2 ^ 59
def prefixEnd_7083248 : Nat := 4983230072969 + 3 ^ 40 * 7083248 * 2
def baseEnd_7083248 : Nat := 3637110818998207993324741

theorem tailTrace_7083248 : CollatzResearch.WordTrace tailWord_7083248 prefixEnd_7083248 3637110818998207993324741 := by
  unfold tailWord_7083248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129173639321304846646293199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172231519095073128861724265 129173639321304846646293199)
  ·
    refine ⟨193760458981957269969439799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129173639321304846646293199 193760458981957269969439799)
    ·
      refine ⟨290640688472935904954159699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193760458981957269969439799 290640688472935904954159699)
      ·
        refine ⟨435961032709403857431239549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290640688472935904954159699 435961032709403857431239549)
        ·
          refine ⟨163485387266026446536714831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435961032709403857431239549 163485387266026446536714831)
          ·
            refine ⟨245228080899039669805072247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163485387266026446536714831 245228080899039669805072247)
            ·
              refine ⟨367842121348559504707608371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245228080899039669805072247 367842121348559504707608371)
              ·
                refine ⟨551763182022839257061412557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367842121348559504707608371 551763182022839257061412557)
                ·
                  refine ⟨206911193258564721398029709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551763182022839257061412557 206911193258564721398029709)
                  ·
                    refine ⟨77591697471961770524261141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206911193258564721398029709 77591697471961770524261141)
                    ·
                      refine ⟨3637110818998207993324741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77591697471961770524261141 3637110818998207993324741)
                      ·
                        rfl

theorem cell23_7083248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_7083248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083248 prefixEnd_7083248 := by exact prefixLift 7083248
  have htrace : WordTrace (prefixWord ++ tailWord_7083248) baseStart_7083248 baseEnd_7083248 := by
    simpa [prefixWord, tailWord_7083248, baseEnd_7083248] using wordTrace_append hprefix tailTrace_7083248
  have hstable : (prefixWord ++ tailWord_7083248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083248).length < 2 ^ (prefixWord ++ tailWord_7083248).sum := by decide
  have hdescent : baseEnd_7083248 < baseStart_7083248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083255 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_7083255 : Nat := 118140960795 + 7083255 * 2 ^ 59
def prefixEnd_7083255 : Nat := 4983230072969 + 3 ^ 40 * 7083255 * 2
def baseEnd_7083255 : Nat := 3637114413362789465937209

theorem tailTrace_7083255 : CollatzResearch.WordTrace tailWord_7083255 prefixEnd_7083255 3637114413362789465937209 := by
  unfold tailWord_7083255
  simp only [CollatzResearch.WordTrace]
  refine ⟨258347533953584333488091219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172231689302389555658727479 258347533953584333488091219)
  ·
    refine ⟨387521300930376500232136829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258347533953584333488091219 387521300930376500232136829)
    ·
      refine ⟨145320487848891187587051311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387521300930376500232136829 145320487848891187587051311)
      ·
        refine ⟨217980731773336781380576967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145320487848891187587051311 217980731773336781380576967)
        ·
          refine ⟨326971097660005172070865451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217980731773336781380576967 326971097660005172070865451)
          ·
            refine ⟨490456646490007758106298177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326971097660005172070865451 490456646490007758106298177)
            ·
              refine ⟨367842484867505818579723633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490456646490007758106298177 367842484867505818579723633)
              ·
                refine ⟨275881863650629363934792725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367842484867505818579723633 275881863650629363934792725)
                ·
                  refine ⟨12931962358623251434443409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 275881863650629363934792725 12931962358623251434443409)
                  ·
                    refine ⟨9698971768967438575832557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12931962358623251434443409 9698971768967438575832557)
                    ·
                      refine ⟨3637114413362789465937209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9698971768967438575832557 3637114413362789465937209)
                      ·
                        rfl

theorem cell23_7083255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_7083255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083255 prefixEnd_7083255 := by exact prefixLift 7083255
  have htrace : WordTrace (prefixWord ++ tailWord_7083255) baseStart_7083255 baseEnd_7083255 := by
    simpa [prefixWord, tailWord_7083255, baseEnd_7083255] using wordTrace_append hprefix tailTrace_7083255
  have hstable : (prefixWord ++ tailWord_7083255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083255).length < 2 ^ (prefixWord ++ tailWord_7083255).sum := by decide
  have hdescent : baseEnd_7083255 < baseStart_7083255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083275 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 6]
def baseStart_7083275 : Nat := 118140960795 + 7083275 * 2 ^ 59
def prefixEnd_7083275 : Nat := 4983230072969 + 3 ^ 40 * 7083275 * 2
def baseEnd_7083275 : Nat := 404124964775097709743013

theorem tailTrace_7083275 : CollatzResearch.WordTrace tailWord_7083275 prefixEnd_7083275 404124964775097709743013 := by
  unfold tailWord_7083275
  simp only [CollatzResearch.WordTrace]
  refine ⟨258348263413511876903819279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172232175609007917935879519 258348263413511876903819279)
  ·
    refine ⟨387522395120267815355728919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258348263413511876903819279 387522395120267815355728919)
    ·
      refine ⟨581283592680401723033593379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387522395120267815355728919 581283592680401723033593379)
      ·
        refine ⟨871925389020602584550390069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581283592680401723033593379 871925389020602584550390069)
        ·
          refine ⟨81743005220681492301599069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 871925389020602584550390069 81743005220681492301599069)
          ·
            refine ⟨30653626957755559613099651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81743005220681492301599069 30653626957755559613099651)
            ·
              refine ⟨45980440436633339419649477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30653626957755559613099651 45980440436633339419649477)
              ·
                refine ⟨8621332581868751141184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45980440436633339419649477 8621332581868751141184277)
                ·
                  refine ⟨404124964775097709743013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8621332581868751141184277 404124964775097709743013)
                  ·
                    rfl

theorem cell23_7083275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 6].length) (baseStart_7083275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083275 prefixEnd_7083275 := by exact prefixLift 7083275
  have htrace : WordTrace (prefixWord ++ tailWord_7083275) baseStart_7083275 baseEnd_7083275 := by
    simpa [prefixWord, tailWord_7083275, baseEnd_7083275] using wordTrace_append hprefix tailTrace_7083275
  have hstable : (prefixWord ++ tailWord_7083275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083275).length < 2 ^ (prefixWord ++ tailWord_7083275).sum := by decide
  have hdescent : baseEnd_7083275 < baseStart_7083275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083285 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_7083285 : Nat := 118140960795 + 7083285 * 2 ^ 59
def prefixEnd_7083285 : Nat := 4983230072969 + 3 ^ 40 * 7083285 * 2
def baseEnd_7083285 : Nat := 3637129817782424348562071

theorem tailTrace_7083285 : CollatzResearch.WordTrace tailWord_7083285 prefixEnd_7083285 3637129817782424348562071 := by
  unfold tailWord_7083285
  simp only [CollatzResearch.WordTrace]
  refine ⟨258348628143475648611683309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172232418762317099074455539 258348628143475648611683309)
  ·
    refine ⟨96880735553803368229381241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258348628143475648611683309 96880735553803368229381241)
    ·
      refine ⟨72660551665352526172035931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96880735553803368229381241 72660551665352526172035931)
      ·
        refine ⟨108990827498028789258053897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72660551665352526172035931 108990827498028789258053897)
        ·
          refine ⟨81743120623521591943540423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108990827498028789258053897 81743120623521591943540423)
          ·
            refine ⟨122614680935282387915310635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81743120623521591943540423 122614680935282387915310635)
            ·
              refine ⟨183922021402923581872965953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122614680935282387915310635 183922021402923581872965953)
              ·
                refine ⟨137941516052192686404724465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183922021402923581872965953 137941516052192686404724465)
                ·
                  refine ⟨103456137039144514803543349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137941516052192686404724465 103456137039144514803543349)
                  ·
                    refine ⟨9699012847419798262832189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103456137039144514803543349 9699012847419798262832189)
                    ·
                      refine ⟨3637129817782424348562071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9699012847419798262832189 3637129817782424348562071)
                      ·
                        rfl

theorem cell23_7083285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_7083285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083285 prefixEnd_7083285 := by exact prefixLift 7083285
  have htrace : WordTrace (prefixWord ++ tailWord_7083285) baseStart_7083285 baseEnd_7083285 := by
    simpa [prefixWord, tailWord_7083285, baseEnd_7083285] using wordTrace_append hprefix tailTrace_7083285
  have hstable : (prefixWord ++ tailWord_7083285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083285).length < 2 ^ (prefixWord ++ tailWord_7083285).sum := by decide
  have hdescent : baseEnd_7083285 < baseStart_7083285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083306 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7083306 : Nat := 118140960795 + 7083306 * 2 ^ 59
def prefixEnd_7083306 : Nat := 4983230072969 + 3 ^ 40 * 7083306 * 2
def baseEnd_7083306 : Nat := 3637140600876168766399475

theorem tailTrace_7083306 : CollatzResearch.WordTrace tailWord_7083306 prefixEnd_7083306 3637140600876168766399475 := by
  unfold tailWord_7083306
  simp only [CollatzResearch.WordTrace]
  refine ⟨64587348519099892299549443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172232929384266379465465181 64587348519099892299549443)
  ·
    refine ⟨96881022778649838449324165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64587348519099892299549443 96881022778649838449324165)
    ·
      refine ⟨18165191770996844709248281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96881022778649838449324165 18165191770996844709248281)
      ·
        refine ⟨13623893828247633531936211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18165191770996844709248281 13623893828247633531936211)
        ·
          refine ⟨20435840742371450297904317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13623893828247633531936211 20435840742371450297904317)
          ·
            refine ⟨7663440278389293861714119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20435840742371450297904317 7663440278389293861714119)
            ·
              refine ⟨11495160417583940792571179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663440278389293861714119 11495160417583940792571179)
              ·
                refine ⟨17242740626375911188856769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495160417583940792571179 17242740626375911188856769)
                ·
                  refine ⟨12932055469781933391642577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17242740626375911188856769 12932055469781933391642577)
                  ·
                    refine ⟨9699041602336450043731933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12932055469781933391642577 9699041602336450043731933)
                    ·
                      refine ⟨3637140600876168766399475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9699041602336450043731933 3637140600876168766399475)
                      ·
                        rfl

theorem cell23_7083306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7083306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083306 prefixEnd_7083306 := by exact prefixLift 7083306
  have htrace : WordTrace (prefixWord ++ tailWord_7083306) baseStart_7083306 baseEnd_7083306 := by
    simpa [prefixWord, tailWord_7083306, baseEnd_7083306] using wordTrace_append hprefix tailTrace_7083306
  have hstable : (prefixWord ++ tailWord_7083306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083306).length < 2 ^ (prefixWord ++ tailWord_7083306).sum := by decide
  have hdescent : baseEnd_7083306 < baseStart_7083306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083312 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2]
def baseStart_7083312 : Nat := 118140960795 + 7083312 * 2 ^ 59
def prefixEnd_7083312 : Nat := 4983230072969 + 3 ^ 40 * 7083312 * 2
def baseEnd_7083312 : Nat := 3637143681760095742924447

theorem tailTrace_7083312 : CollatzResearch.WordTrace tailWord_7083312 prefixEnd_7083312 3637143681760095742924447 := by
  unfold tailWord_7083312
  simp only [CollatzResearch.WordTrace]
  refine ⟨129174806457188916111458095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172233075276251888148610793 129174806457188916111458095)
  ·
    refine ⟨193762209685783374167187143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129174806457188916111458095 193762209685783374167187143)
    ·
      refine ⟨290643314528675061250780715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193762209685783374167187143 290643314528675061250780715)
      ·
        refine ⟨435964971793012591876171073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290643314528675061250780715 435964971793012591876171073)
        ·
          refine ⟨326973728844759443907128305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435964971793012591876171073 326973728844759443907128305)
          ·
            refine ⟨245230296633569582930346229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326973728844759443907128305 245230296633569582930346229)
            ·
              refine ⟨22990340309397148399719959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245230296633569582930346229 22990340309397148399719959)
              ·
                refine ⟨34485510464095722599579939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22990340309397148399719959 34485510464095722599579939)
                ·
                  refine ⟨51728265696143583899369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34485510464095722599579939 51728265696143583899369909)
                  ·
                    refine ⟨4849524909013460990565929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51728265696143583899369909 4849524909013460990565929)
                    ·
                      refine ⟨3637143681760095742924447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849524909013460990565929 3637143681760095742924447)
                      ·
                        rfl

theorem cell23_7083312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2].length) (baseStart_7083312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083312 prefixEnd_7083312 := by exact prefixLift 7083312
  have htrace : WordTrace (prefixWord ++ tailWord_7083312) baseStart_7083312 baseEnd_7083312 := by
    simpa [prefixWord, tailWord_7083312, baseEnd_7083312] using wordTrace_append hprefix tailTrace_7083312
  have hstable : (prefixWord ++ tailWord_7083312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083312).length < 2 ^ (prefixWord ++ tailWord_7083312).sum := by decide
  have hdescent : baseEnd_7083312 < baseStart_7083312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083322 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_7083322 : Nat := 118140960795 + 7083322 * 2 ^ 59
def prefixEnd_7083322 : Nat := 4983230072969 + 3 ^ 40 * 7083322 * 2
def baseEnd_7083322 : Nat := 1212382938855546901266467

theorem tailTrace_7083322 : CollatzResearch.WordTrace tailWord_7083322 prefixEnd_7083322 1212382938855546901266467 := by
  unfold tailWord_7083322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64587494411085400982695055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172233318429561069287186813 64587494411085400982695055)
  ·
    refine ⟨96881241616628101474042583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64587494411085400982695055 96881241616628101474042583)
    ·
      refine ⟨145321862424942152211063875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96881241616628101474042583 145321862424942152211063875)
      ·
        refine ⟨217982793637413228316595813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145321862424942152211063875 217982793637413228316595813)
        ·
          refine ⟨40871773807014980309361715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217982793637413228316595813 40871773807014980309361715)
          ·
            refine ⟨61307660710522470464042573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40871773807014980309361715 61307660710522470464042573)
            ·
              refine ⟨22990372766445926424015965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61307660710522470464042573 22990372766445926424015965)
              ·
                refine ⟨8621389787417222409005987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22990372766445926424015965 8621389787417222409005987)
                ·
                  refine ⟨12932084681125833613508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621389787417222409005987 12932084681125833613508981)
                  ·
                    refine ⟨1212382938855546901266467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12932084681125833613508981 1212382938855546901266467)
                    ·
                      rfl

theorem cell23_7083322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_7083322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083322 prefixEnd_7083322 := by exact prefixLift 7083322
  have htrace : WordTrace (prefixWord ++ tailWord_7083322) baseStart_7083322 baseEnd_7083322 := by
    simpa [prefixWord, tailWord_7083322, baseEnd_7083322] using wordTrace_append hprefix tailTrace_7083322
  have hstable : (prefixWord ++ tailWord_7083322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083322).length < 2 ^ (prefixWord ++ tailWord_7083322).sum := by decide
  have hdescent : baseEnd_7083322 < baseStart_7083322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083362 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7083362 : Nat := 118140960795 + 7083362 * 2 ^ 59
def prefixEnd_7083362 : Nat := 4983230072969 + 3 ^ 40 * 7083362 * 2
def baseEnd_7083362 : Nat := 3637169355792820547299217

theorem tailTrace_7083362 : CollatzResearch.WordTrace tailWord_7083362 prefixEnd_7083362 3637169355792820547299217 := by
  unfold tailWord_7083362
  simp only [CollatzResearch.WordTrace]
  refine ⟨64587859141049172690559085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172234291042797793841490893 64587859141049172690559085)
  ·
    refine ⟨24220447177893439758959657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64587859141049172690559085 24220447177893439758959657)
    ·
      refine ⟨18165335383420079819219743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24220447177893439758959657 18165335383420079819219743)
      ·
        refine ⟨27248003075130119728829615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18165335383420079819219743 27248003075130119728829615)
        ·
          refine ⟨40872004612695179593244423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27248003075130119728829615 40872004612695179593244423)
          ·
            refine ⟨61308006919042769389866635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40872004612695179593244423 61308006919042769389866635)
            ·
              refine ⟨91962010378564154084799953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61308006919042769389866635 91962010378564154084799953)
              ·
                refine ⟨68971507783923115563599965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91962010378564154084799953 68971507783923115563599965)
                ·
                  refine ⟨25864315418971168336349987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68971507783923115563599965 25864315418971168336349987)
                  ·
                    refine ⟨38796473128456752504524981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25864315418971168336349987 38796473128456752504524981)
                    ·
                      refine ⟨3637169355792820547299217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38796473128456752504524981 3637169355792820547299217)
                      ·
                        rfl

theorem cell23_7083362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7083362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083362 prefixEnd_7083362 := by exact prefixLift 7083362
  have htrace : WordTrace (prefixWord ++ tailWord_7083362) baseStart_7083362 baseEnd_7083362 := by
    simpa [prefixWord, tailWord_7083362, baseEnd_7083362] using wordTrace_append hprefix tailTrace_7083362
  have hstable : (prefixWord ++ tailWord_7083362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083362).length < 2 ^ (prefixWord ++ tailWord_7083362).sum := by decide
  have hdescent : baseEnd_7083362 < baseStart_7083362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083365 : List Nat := [1, 3, 1, 3, 1, 2, 3, 9]
def baseStart_7083365 : Nat := 118140960795 + 7083365 * 2 ^ 59
def prefixEnd_7083365 : Nat := 4983230072969 + 3 ^ 40 * 7083365 * 2
def baseEnd_7083365 : Nat := 134710033193880890205989

theorem tailTrace_7083365 : CollatzResearch.WordTrace tailWord_7083365 prefixEnd_7083365 134710033193880890205989 := by
  unfold tailWord_7083365
  simp only [CollatzResearch.WordTrace]
  refine ⟨258351545983185822274595549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172234363988790548183063699 258351545983185822274595549)
  ·
    refine ⟨96881829743694683352973331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258351545983185822274595549 96881829743694683352973331)
    ·
      refine ⟨145322744615542025029459997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96881829743694683352973331 145322744615542025029459997)
      ·
        refine ⟨54496029230828259386047499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145322744615542025029459997 54496029230828259386047499)
        ·
          refine ⟨81744043846242389079071249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54496029230828259386047499 81744043846242389079071249)
          ·
            refine ⟨61308032884681791809303437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81744043846242389079071249 61308032884681791809303437)
            ·
              refine ⟨22990512331755671928488789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61308032884681791809303437 22990512331755671928488789)
              ·
                refine ⟨134710033193880890205989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22990512331755671928488789 134710033193880890205989)
                ·
                  rfl

theorem cell23_7083365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 9].length) (baseStart_7083365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083365 prefixEnd_7083365 := by exact prefixLift 7083365
  have htrace : WordTrace (prefixWord ++ tailWord_7083365) baseStart_7083365 baseEnd_7083365 := by
    simpa [prefixWord, tailWord_7083365, baseEnd_7083365] using wordTrace_append hprefix tailTrace_7083365
  have hstable : (prefixWord ++ tailWord_7083365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083365).length < 2 ^ (prefixWord ++ tailWord_7083365).sum := by decide
  have hdescent : baseEnd_7083365 < baseStart_7083365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083370 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7083370 : Nat := 118140960795 + 7083370 * 2 ^ 59
def prefixEnd_7083370 : Nat := 4983230072969 + 3 ^ 40 * 7083370 * 2
def baseEnd_7083370 : Nat := 3637173463638056515999181

theorem tailTrace_7083370 : CollatzResearch.WordTrace tailWord_7083370 prefixEnd_7083370 3637173463638056515999181 := by
  unfold tailWord_7083370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64587932087041927032131891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172234485565445138752351709 64587932087041927032131891)
  ·
    refine ⟨96881898130562890548197837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64587932087041927032131891 96881898130562890548197837)
    ·
      refine ⟨36330711798961083955574189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96881898130562890548197837 36330711798961083955574189)
      ·
        refine ⟨13624016924610406483340321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36330711798961083955574189 13624016924610406483340321)
        ·
          refine ⟨10218012693457804862505241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13624016924610406483340321 10218012693457804862505241)
          ·
            refine ⟨7663509520093353646878931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10218012693457804862505241 7663509520093353646878931)
            ·
              refine ⟨11495264280140030470318397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663509520093353646878931 11495264280140030470318397)
              ·
                refine ⟨4310724105052511426369399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11495264280140030470318397 4310724105052511426369399)
                ·
                  refine ⟨6466086157578767139554099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310724105052511426369399 6466086157578767139554099)
                  ·
                    refine ⟨9699129236368150709331149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6466086157578767139554099 9699129236368150709331149)
                    ·
                      refine ⟨3637173463638056515999181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9699129236368150709331149 3637173463638056515999181)
                      ·
                        rfl

theorem cell23_7083370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7083370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083370 prefixEnd_7083370 := by exact prefixLift 7083370
  have htrace : WordTrace (prefixWord ++ tailWord_7083370) baseStart_7083370 baseEnd_7083370 := by
    simpa [prefixWord, tailWord_7083370, baseEnd_7083370] using wordTrace_append hprefix tailTrace_7083370
  have hstable : (prefixWord ++ tailWord_7083370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083370).length < 2 ^ (prefixWord ++ tailWord_7083370).sum := by decide
  have hdescent : baseEnd_7083370 < baseStart_7083370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083409 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_7083409 : Nat := 118140960795 + 7083409 * 2 ^ 59
def prefixEnd_7083409 : Nat := 4983230072969 + 3 ^ 40 * 7083409 * 2
def baseEnd_7083409 : Nat := 3637193489383581863411501

theorem tailTrace_7083409 : CollatzResearch.WordTrace tailWord_7083409 prefixEnd_7083409 3637193489383581863411501 := by
  unfold tailWord_7083409
  simp only [CollatzResearch.WordTrace]
  refine ⟨258353150795026417789197281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172235433863350945192798187 258353150795026417789197281)
  ·
    refine ⟨193764863096269813341897961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258353150795026417789197281 193764863096269813341897961)
    ·
      refine ⟨145323647322202360006423471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193764863096269813341897961 145323647322202360006423471)
      ·
        refine ⟨217985470983303540009635207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145323647322202360006423471 217985470983303540009635207)
        ·
          refine ⟨326978206474955310014452811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217985470983303540009635207 326978206474955310014452811)
          ·
            refine ⟨490467309712432965021679217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326978206474955310014452811 490467309712432965021679217)
            ·
              refine ⟨367850482284324723766259413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490467309712432965021679217 367850482284324723766259413)
              ·
                refine ⟨8621495678538860713271705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367850482284324723766259413 8621495678538860713271705)
                ·
                  refine ⟨6466121758904145534953779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8621495678538860713271705 6466121758904145534953779)
                  ·
                    refine ⟨9699182638356218302430669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6466121758904145534953779 9699182638356218302430669)
                    ·
                      refine ⟨3637193489383581863411501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9699182638356218302430669 3637193489383581863411501)
                      ·
                        rfl

theorem cell23_7083409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_7083409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083409 prefixEnd_7083409 := by exact prefixLift 7083409
  have htrace : WordTrace (prefixWord ++ tailWord_7083409) baseStart_7083409 baseEnd_7083409 := by
    simpa [prefixWord, tailWord_7083409, baseEnd_7083409] using wordTrace_append hprefix tailTrace_7083409
  have hstable : (prefixWord ++ tailWord_7083409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083409).length < 2 ^ (prefixWord ++ tailWord_7083409).sum := by decide
  have hdescent : baseEnd_7083409 < baseStart_7083409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083410 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7083410 : Nat := 118140960795 + 7083410 * 2 ^ 59
def prefixEnd_7083410 : Nat := 4983230072969 + 3 ^ 40 * 7083410 * 2
def baseEnd_7083410 : Nat := 3637194002864236359498997

theorem tailTrace_7083410 : CollatzResearch.WordTrace tailWord_7083410 prefixEnd_7083410 3637194002864236359498997 := by
  unfold tailWord_7083410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588296817005698739995921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172235458178681863306655789 64588296817005698739995921)
  ·
    refine ⟨48441222612754274054996941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64588296817005698739995921 48441222612754274054996941)
    ·
      refine ⟨18165458479782852770623853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48441222612754274054996941 18165458479782852770623853)
      ·
        refine ⟨6812046929918569788983945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18165458479782852770623853 6812046929918569788983945)
        ·
          refine ⟨5109035197438927341737959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812046929918569788983945 5109035197438927341737959)
          ·
            refine ⟨7663552796158391012606939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109035197438927341737959 7663552796158391012606939)
            ·
              refine ⟨11495329194237586518910409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663552796158391012606939 11495329194237586518910409)
              ·
                refine ⟨8621496895678189889182807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11495329194237586518910409 8621496895678189889182807)
                ·
                  refine ⟨12932245343517284833774211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621496895678189889182807 12932245343517284833774211)
                  ·
                    refine ⟨19398368015275927250661317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12932245343517284833774211 19398368015275927250661317)
                    ·
                      refine ⟨3637194002864236359498997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19398368015275927250661317 3637194002864236359498997)
                      ·
                        rfl

theorem cell23_7083410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7083410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083410 prefixEnd_7083410 := by exact prefixLift 7083410
  have htrace : WordTrace (prefixWord ++ tailWord_7083410) baseStart_7083410 baseEnd_7083410 := by
    simpa [prefixWord, tailWord_7083410, baseEnd_7083410] using wordTrace_append hprefix tailTrace_7083410
  have hstable : (prefixWord ++ tailWord_7083410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083410).length < 2 ^ (prefixWord ++ tailWord_7083410).sum := by decide
  have hdescent : baseEnd_7083410 < baseStart_7083410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083415 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_7083415 : Nat := 118140960795 + 7083415 * 2 ^ 59
def prefixEnd_7083415 : Nat := 4983230072969 + 3 ^ 40 * 7083415 * 2
def baseEnd_7083415 : Nat := 3637196570267508839936473

theorem tailTrace_7083415 : CollatzResearch.WordTrace tailWord_7083415 prefixEnd_7083415 3637196570267508839936473 := by
  unfold tailWord_7083415
  simp only [CollatzResearch.WordTrace]
  refine ⟨258353369633004680813915699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172235579755336453875943799 258353369633004680813915699)
  ·
    refine ⟨387530054449507021220873549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258353369633004680813915699 387530054449507021220873549)
    ·
      refine ⟨145323770418565132957827581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387530054449507021220873549 145323770418565132957827581)
      ·
        refine ⟨54496413906961924859185343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145323770418565132957827581 54496413906961924859185343)
        ·
          refine ⟨81744620860442887288778015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54496413906961924859185343 81744620860442887288778015)
          ·
            refine ⟨122616931290664330933167023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81744620860442887288778015 122616931290664330933167023)
            ·
              refine ⟨183925396935996496399750535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122616931290664330933167023 183925396935996496399750535)
              ·
                refine ⟨275888095403994744599625803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183925396935996496399750535 275888095403994744599625803)
                ·
                  refine ⟨413832143105992116899438705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275888095403994744599625803 413832143105992116899438705)
                  ·
                    refine ⟨310374107329494087674579029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 413832143105992116899438705 310374107329494087674579029)
                    ·
                      refine ⟨3637196570267508839936473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310374107329494087674579029 3637196570267508839936473)
                      ·
                        rfl

theorem cell23_7083415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_7083415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083415 prefixEnd_7083415 := by exact prefixLift 7083415
  have htrace : WordTrace (prefixWord ++ tailWord_7083415) baseStart_7083415 baseEnd_7083415 := by
    simpa [prefixWord, tailWord_7083415, baseEnd_7083415] using wordTrace_append hprefix tailTrace_7083415
  have hstable : (prefixWord ++ tailWord_7083415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083415).length < 2 ^ (prefixWord ++ tailWord_7083415).sum := by decide
  have hdescent : baseEnd_7083415 < baseStart_7083415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083435 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_7083435 : Nat := 118140960795 + 7083435 * 2 ^ 59
def prefixEnd_7083435 : Nat := 4983230072969 + 3 ^ 40 * 7083435 * 2
def baseEnd_7083435 : Nat := 3637206839880598761686381

theorem tailTrace_7083435 : CollatzResearch.WordTrace tailWord_7083435 prefixEnd_7083435 3637206839880598761686381 := by
  unfold tailWord_7083435
  simp only [CollatzResearch.WordTrace]
  refine ⟨258354099092932224229643759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172236066061954816153095839 258354099092932224229643759)
  ·
    refine ⟨387531148639398336344465639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258354099092932224229643759 387531148639398336344465639)
    ·
      refine ⟨581296722959097504516698459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387531148639398336344465639 581296722959097504516698459)
      ·
        refine ⟨871945084438646256775047689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581296722959097504516698459 871945084438646256775047689)
        ·
          refine ⟨653958813328984692581285767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871945084438646256775047689 653958813328984692581285767)
          ·
            refine ⟨980938219993477038871928651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653958813328984692581285767 980938219993477038871928651)
            ·
              refine ⟨1471407329990215558307892977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980938219993477038871928651 1471407329990215558307892977)
              ·
                refine ⟨1103555497492661668730919733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471407329990215558307892977 1103555497492661668730919733)
                ·
                  refine ⟨103458327889937031443523725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1103555497492661668730919733 103458327889937031443523725)
                  ·
                    refine ⟨38796872958726386791321397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103458327889937031443523725 38796872958726386791321397)
                    ·
                      refine ⟨3637206839880598761686381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38796872958726386791321397 3637206839880598761686381)
                      ·
                        rfl

theorem cell23_7083435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_7083435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083435 prefixEnd_7083435 := by exact prefixLift 7083435
  have htrace : WordTrace (prefixWord ++ tailWord_7083435) baseStart_7083435 baseEnd_7083435 := by
    simpa [prefixWord, tailWord_7083435, baseEnd_7083435] using wordTrace_append hprefix tailTrace_7083435
  have hstable : (prefixWord ++ tailWord_7083435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083435).length < 2 ^ (prefixWord ++ tailWord_7083435).sum := by decide
  have hdescent : baseEnd_7083435 < baseStart_7083435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083455 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 11]
def baseStart_7083455 : Nat := 118140960795 + 7083455 * 2 ^ 59
def prefixEnd_7083455 : Nat := 4983230072969 + 3 ^ 40 * 7083455 * 2
def baseEnd_7083455 : Nat := 404135234388187631492921

theorem tailTrace_7083455 : CollatzResearch.WordTrace tailWord_7083455 prefixEnd_7083455 404135234388187631492921 := by
  unfold tailWord_7083455
  simp only [CollatzResearch.WordTrace]
  refine ⟨258354828552859767645371819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172236552368573178430247879 258354828552859767645371819)
  ·
    refine ⟨387532242829289651468057729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258354828552859767645371819 387532242829289651468057729)
    ·
      refine ⟨290649182121967238601043297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387532242829289651468057729 290649182121967238601043297)
      ·
        refine ⟨217986886591475428950782473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290649182121967238601043297 217986886591475428950782473)
        ·
          refine ⟨163490164943606571713086855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217986886591475428950782473 163490164943606571713086855)
          ·
            refine ⟨245235247415409857569630283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163490164943606571713086855 245235247415409857569630283)
            ·
              refine ⟨367852871123114786354445425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245235247415409857569630283 367852871123114786354445425)
              ·
                refine ⟨275889653342336089765834069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367852871123114786354445425 275889653342336089765834069)
                ·
                  refine ⟨404135234388187631492921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 275889653342336089765834069 404135234388187631492921)
                  ·
                    rfl

theorem cell23_7083455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 11].length) (baseStart_7083455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083455 prefixEnd_7083455 := by exact prefixLift 7083455
  have htrace : WordTrace (prefixWord ++ tailWord_7083455) baseStart_7083455 baseEnd_7083455 := by
    simpa [prefixWord, tailWord_7083455, baseEnd_7083455] using wordTrace_append hprefix tailTrace_7083455
  have hstable : (prefixWord ++ tailWord_7083455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083455).length < 2 ^ (prefixWord ++ tailWord_7083455).sum := by decide
  have hdescent : baseEnd_7083455 < baseStart_7083455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083466 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_7083466 : Nat := 118140960795 + 7083466 * 2 ^ 59
def prefixEnd_7083466 : Nat := 4983230072969 + 3 ^ 40 * 7083466 * 2
def baseEnd_7083466 : Nat := 3637222757780888140398739

theorem tailTrace_7083466 : CollatzResearch.WordTrace tailWord_7083466 prefixEnd_7083466 3637222757780888140398739 := by
  unfold tailWord_7083466
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588807438954979131005563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172236819837213277682681501 64588807438954979131005563)
  ·
    refine ⟨96883211158432468696508345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64588807438954979131005563 96883211158432468696508345)
    ·
      refine ⟨72662408368824351522381259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96883211158432468696508345 72662408368824351522381259)
      ·
        refine ⟨108993612553236527283571889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72662408368824351522381259 108993612553236527283571889)
        ·
          refine ⟨81745209414927395462678917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108993612553236527283571889 81745209414927395462678917)
          ·
            refine ⟨15327226765298886649252297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81745209414927395462678917 15327226765298886649252297)
            ·
              refine ⟨11495420073974164986939223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15327226765298886649252297 11495420073974164986939223)
              ·
                refine ⟨17243130110961247480408835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495420073974164986939223 17243130110961247480408835)
                ·
                  refine ⟨25864695166441871220613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17243130110961247480408835 25864695166441871220613253)
                  ·
                    refine ⟨4849630343707850853864985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25864695166441871220613253 4849630343707850853864985)
                    ·
                      refine ⟨3637222757780888140398739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849630343707850853864985 3637222757780888140398739)
                      ·
                        rfl

theorem cell23_7083466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_7083466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083466 prefixEnd_7083466 := by exact prefixLift 7083466
  have htrace : WordTrace (prefixWord ++ tailWord_7083466) baseStart_7083466 baseEnd_7083466 := by
    simpa [prefixWord, tailWord_7083466, baseEnd_7083466] using wordTrace_append hprefix tailTrace_7083466
  have hstable : (prefixWord ++ tailWord_7083466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083466).length < 2 ^ (prefixWord ++ tailWord_7083466).sum := by decide
  have hdescent : baseEnd_7083466 < baseStart_7083466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083489 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 5]
def baseStart_7083489 : Nat := 118140960795 + 7083489 * 2 ^ 59
def prefixEnd_7083489 : Nat := 4983230072969 + 3 ^ 40 * 7083489 * 2
def baseEnd_7083489 : Nat := 404137174203993505601237

theorem tailTrace_7083489 : CollatzResearch.WordTrace tailWord_7083489 prefixEnd_7083489 404137174203993505601237 := by
  unfold tailWord_7083489
  simp only [CollatzResearch.WordTrace]
  refine ⟨258356068634736591452109521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172237379089824394301406347 258356068634736591452109521)
  ·
    refine ⟨193767051476052443589082141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258356068634736591452109521 193767051476052443589082141)
    ·
      refine ⟨72662644303519666345905803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193767051476052443589082141 72662644303519666345905803)
      ·
        refine ⟨108993966455279499518858705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72662644303519666345905803 108993966455279499518858705)
        ·
          refine ⟨81745474841459624639144029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108993966455279499518858705 81745474841459624639144029)
          ·
            refine ⟨30654553065547359239679011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81745474841459624639144029 30654553065547359239679011)
            ·
              refine ⟨45981829598321038859518517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30654553065547359239679011 45981829598321038859518517)
              ·
                refine ⟨4310796524842597393079861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45981829598321038859518517 4310796524842597393079861)
                ·
                  refine ⟨404137174203993505601237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310796524842597393079861 404137174203993505601237)
                  ·
                    rfl

theorem cell23_7083489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 5].length) (baseStart_7083489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083489 prefixEnd_7083489 := by exact prefixLift 7083489
  have htrace : WordTrace (prefixWord ++ tailWord_7083489) baseStart_7083489 baseEnd_7083489 := by
    simpa [prefixWord, tailWord_7083489, baseEnd_7083489] using wordTrace_append hprefix tailTrace_7083489
  have hstable : (prefixWord ++ tailWord_7083489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083489).length < 2 ^ (prefixWord ++ tailWord_7083489).sum := by decide
  have hdescent : baseEnd_7083489 < baseStart_7083489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083506 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_7083506 : Nat := 118140960795 + 7083506 * 2 ^ 59
def prefixEnd_7083506 : Nat := 4983230072969 + 3 ^ 40 * 7083506 * 2
def baseEnd_7083506 : Nat := 404138144111896442655395

theorem tailTrace_7083506 : CollatzResearch.WordTrace tailWord_7083506 prefixEnd_7083506 404138144111896442655395 := by
  unfold tailWord_7083506
  simp only [CollatzResearch.WordTrace]
  refine ⟨64589172168918750838869593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172237792450450002236985581 64589172168918750838869593)
  ·
    refine ⟨48441879126689063129152195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64589172168918750838869593 48441879126689063129152195)
    ·
      refine ⟨72662818690033594693728293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48441879126689063129152195 72662818690033594693728293)
      ·
        refine ⟨13624278504381299005074055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72662818690033594693728293 13624278504381299005074055)
        ·
          refine ⟨20436417756571948507611083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13624278504381299005074055 20436417756571948507611083)
          ·
            refine ⟨30654626634857922761416625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20436417756571948507611083 30654626634857922761416625)
            ·
              refine ⟨22990969976143442071062469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30654626634857922761416625 22990969976143442071062469)
              ·
                refine ⟨4310806870526895388324213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22990969976143442071062469 4310806870526895388324213)
                ·
                  refine ⟨404138144111896442655395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310806870526895388324213 404138144111896442655395)
                  ·
                    rfl

theorem cell23_7083506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_7083506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083506 prefixEnd_7083506 := by exact prefixLift 7083506
  have htrace : WordTrace (prefixWord ++ tailWord_7083506) baseStart_7083506 baseEnd_7083506 := by
    simpa [prefixWord, tailWord_7083506, baseEnd_7083506] using wordTrace_append hprefix tailTrace_7083506
  have hstable : (prefixWord ++ tailWord_7083506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083506).length < 2 ^ (prefixWord ++ tailWord_7083506).sum := by decide
  have hdescent : baseEnd_7083506 < baseStart_7083506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083540 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 5]
def baseStart_7083540 : Nat := 118140960795 + 7083540 * 2 ^ 59
def prefixEnd_7083540 : Nat := 4983230072969 + 3 ^ 40 * 7083540 * 2
def baseEnd_7083540 : Nat := 404140083927702316763711

theorem tailTrace_7083540 : CollatzResearch.WordTrace tailWord_7083540 prefixEnd_7083540 404140083927702316763711 := by
  unfold tailWord_7083540
  simp only [CollatzResearch.WordTrace]
  refine ⟨129178964378775913581108037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172238619171701218108144049 129178964378775913581108037)
  ·
    refine ⟨24221055821020483796457757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129178964378775913581108037 24221055821020483796457757)
    ·
      refine ⟨9082895932882681423671659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24221055821020483796457757 9082895932882681423671659)
      ·
        refine ⟨13624343899324022135507489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9082895932882681423671659 13624343899324022135507489)
        ·
          refine ⟨10218257924493016601630617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13624343899324022135507489 10218257924493016601630617)
          ·
            refine ⟨7663693443369762451222963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10218257924493016601630617 7663693443369762451222963)
            ·
              refine ⟨11495540165054643676834445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663693443369762451222963 11495540165054643676834445)
              ·
                refine ⟨4310827561895491378812917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11495540165054643676834445 4310827561895491378812917)
                ·
                  refine ⟨404140083927702316763711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310827561895491378812917 404140083927702316763711)
                  ·
                    rfl

theorem cell23_7083540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_7083540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083540 prefixEnd_7083540 := by exact prefixLift 7083540
  have htrace : WordTrace (prefixWord ++ tailWord_7083540) baseStart_7083540 baseEnd_7083540 := by
    simpa [prefixWord, tailWord_7083540, baseEnd_7083540] using wordTrace_append hprefix tailTrace_7083540
  have hstable : (prefixWord ++ tailWord_7083540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083540).length < 2 ^ (prefixWord ++ tailWord_7083540).sum := by decide
  have hdescent : baseEnd_7083540 < baseStart_7083540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083590 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7083590 : Nat := 118140960795 + 7083590 * 2 ^ 59
def prefixEnd_7083590 : Nat := 4983230072969 + 3 ^ 40 * 7083590 * 2
def baseEnd_7083590 : Nat := 3637286429382045655248169

theorem tailTrace_7083590 : CollatzResearch.WordTrace tailWord_7083590 prefixEnd_7083590 3637286429382045655248169 := by
  unfold tailWord_7083590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8073742262730333928173007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172239834938247123801024149 8073742262730333928173007)
  ·
    refine ⟨12110613394095500892259511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8073742262730333928173007 12110613394095500892259511)
    ·
      refine ⟨18165920091143251338389267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12110613394095500892259511 18165920091143251338389267)
      ·
        refine ⟨27248880136714877007583901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18165920091143251338389267 27248880136714877007583901)
        ·
          refine ⟨10218330051268078877843963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27248880136714877007583901 10218330051268078877843963)
          ·
            refine ⟨15327495076902118316765945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10218330051268078877843963 15327495076902118316765945)
            ·
              refine ⟨11495621307676588737574459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15327495076902118316765945 11495621307676588737574459)
              ·
                refine ⟨17243431961514883106361689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495621307676588737574459 17243431961514883106361689)
                ·
                  refine ⟨12932573971136162329771267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17243431961514883106361689 12932573971136162329771267)
                  ·
                    refine ⟨19398860956704243494656901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12932573971136162329771267 19398860956704243494656901)
                    ·
                      refine ⟨3637286429382045655248169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19398860956704243494656901 3637286429382045655248169)
                      ·
                        rfl

theorem cell23_7083590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7083590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083590 prefixEnd_7083590 := by exact prefixLift 7083590
  have htrace : WordTrace (prefixWord ++ tailWord_7083590) baseStart_7083590 baseEnd_7083590 := by
    simpa [prefixWord, tailWord_7083590, baseEnd_7083590] using wordTrace_append hprefix tailTrace_7083590
  have hstable : (prefixWord ++ tailWord_7083590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083590).length < 2 ^ (prefixWord ++ tailWord_7083590).sum := by decide
  have hdescent : baseEnd_7083590 < baseStart_7083590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083609 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_7083609 : Nat := 118140960795 + 7083609 * 2 ^ 59
def prefixEnd_7083609 : Nat := 4983230072969 + 3 ^ 40 * 7083609 * 2
def baseEnd_7083609 : Nat := 1212432061838160360303527

theorem tailTrace_7083609 : CollatzResearch.WordTrace tailWord_7083609 prefixEnd_7083609 1212432061838160360303527 := by
  unfold tailWord_7083609
  simp only [CollatzResearch.WordTrace]
  refine ⟨258360445394301851946477881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172240296929534567964318587 258360445394301851946477881)
  ·
    refine ⟨193770334045726388959858411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258360445394301851946477881 193770334045726388959858411)
    ·
      refine ⟨290655501068589583439787617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193770334045726388959858411 290655501068589583439787617)
      ·
        refine ⟨217991625801442187579840713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290655501068589583439787617 217991625801442187579840713)
        ·
          refine ⟨163493719351081640684880535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217991625801442187579840713 163493719351081640684880535)
          ·
            refine ⟨245240579026622461027320803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163493719351081640684880535 245240579026622461027320803)
            ·
              refine ⟨367860868539933691540981205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245240579026622461027320803 367860868539933691540981205)
              ·
                refine ⟨8621739106404695895491747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367860868539933691540981205 8621739106404695895491747)
                ·
                  refine ⟨12932608659607043843237621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621739106404695895491747 12932608659607043843237621)
                  ·
                    refine ⟨1212432061838160360303527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12932608659607043843237621 1212432061838160360303527)
                    ·
                      rfl

theorem cell23_7083609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_7083609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083609 prefixEnd_7083609 := by exact prefixLift 7083609
  have htrace : WordTrace (prefixWord ++ tailWord_7083609) baseStart_7083609 baseEnd_7083609 := by
    simpa [prefixWord, tailWord_7083609, baseEnd_7083609] using wordTrace_append hprefix tailTrace_7083609
  have hstable : (prefixWord ++ tailWord_7083609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083609).length < 2 ^ (prefixWord ++ tailWord_7083609).sum := by decide
  have hdescent : baseEnd_7083609 < baseStart_7083609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083639 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 6, 4]
def baseStart_7083639 : Nat := 118140960795 + 7083639 * 2 ^ 59
def prefixEnd_7083639 : Nat := 4983230072969 + 3 ^ 40 * 7083639 * 2
def baseEnd_7083639 : Nat := 1212437196644705321178481

theorem tailTrace_7083639 : CollatzResearch.WordTrace tailWord_7083639 prefixEnd_7083639 1212437196644705321178481 := by
  unfold tailWord_7083639
  simp only [CollatzResearch.WordTrace]
  refine ⟨258361539584193167070069971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172241026389462111380046647 258361539584193167070069971)
  ·
    refine ⟨387542309376289750605104957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258361539584193167070069971 387542309376289750605104957)
    ·
      refine ⟨145328366016108656476914359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387542309376289750605104957 145328366016108656476914359)
      ·
        refine ⟨217992549024162984715371539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145328366016108656476914359 217992549024162984715371539)
        ·
          refine ⟨326988823536244477073057309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217992549024162984715371539 326988823536244477073057309)
          ·
            refine ⟨122620808826091678902396491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326988823536244477073057309 122620808826091678902396491)
            ·
              refine ⟨183931213239137518353594737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122620808826091678902396491 183931213239137518353594737)
              ·
                refine ⟨137948409929353138765196053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183931213239137518353594737 137948409929353138765196053)
                ·
                  refine ⟨6466331715438428379618565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137948409929353138765196053 6466331715438428379618565)
                  ·
                    refine ⟨1212437196644705321178481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466331715438428379618565 1212437196644705321178481)
                    ·
                      rfl

theorem cell23_7083639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_7083639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083639 prefixEnd_7083639 := by exact prefixLift 7083639
  have htrace : WordTrace (prefixWord ++ tailWord_7083639) baseStart_7083639 baseEnd_7083639 := by
    simpa [prefixWord, tailWord_7083639, baseEnd_7083639] using wordTrace_append hprefix tailTrace_7083639
  have hstable : (prefixWord ++ tailWord_7083639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083639).length < 2 ^ (prefixWord ++ tailWord_7083639).sum := by decide
  have hdescent : baseEnd_7083639 < baseStart_7083639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083659 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4]
def baseStart_7083659 : Nat := 118140960795 + 7083659 * 2 ^ 59
def prefixEnd_7083659 : Nat := 4983230072969 + 3 ^ 40 * 7083659 * 2
def baseEnd_7083659 : Nat := 3637321859547205885285351

theorem tailTrace_7083659 : CollatzResearch.WordTrace tailWord_7083659 prefixEnd_7083659 3637321859547205885285351 := by
  unfold tailWord_7083659
  simp only [CollatzResearch.WordTrace]
  refine ⟨258362269044120710485798031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172241512696080473657198687 258362269044120710485798031)
  ·
    refine ⟨387543403566181065728697047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258362269044120710485798031 387543403566181065728697047)
    ·
      refine ⟨581315105349271598593045571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387543403566181065728697047 581315105349271598593045571)
      ·
        refine ⟨871972658023907397889568357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581315105349271598593045571 871972658023907397889568357)
        ·
          refine ⟨163494873379482637104294067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 871972658023907397889568357 163494873379482637104294067)
          ·
            refine ⟨245242310069223955656441101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163494873379482637104294067 245242310069223955656441101)
            ·
              refine ⟨91965866275958983371165413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245242310069223955656441101 91965866275958983371165413)
              ·
                refine ⟨17243599926742309382093515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91965866275958983371165413 17243599926742309382093515)
                ·
                  refine ⟨25865399890113464073140273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17243599926742309382093515 25865399890113464073140273)
                  ·
                    refine ⟨19399049917585098054855205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25865399890113464073140273 19399049917585098054855205)
                    ·
                      refine ⟨3637321859547205885285351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19399049917585098054855205 3637321859547205885285351)
                      ·
                        rfl

theorem cell23_7083659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_7083659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083659 prefixEnd_7083659 := by exact prefixLift 7083659
  have htrace : WordTrace (prefixWord ++ tailWord_7083659) baseStart_7083659 baseEnd_7083659 := by
    simpa [prefixWord, tailWord_7083659, baseEnd_7083659] using wordTrace_append hprefix tailTrace_7083659
  have hstable : (prefixWord ++ tailWord_7083659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083659).length < 2 ^ (prefixWord ++ tailWord_7083659).sum := by decide
  have hdescent : baseEnd_7083659 < baseStart_7083659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083680 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2]
def baseStart_7083680 : Nat := 118140960795 + 7083680 * 2 ^ 59
def prefixEnd_7083680 : Nat := 4983230072969 + 3 ^ 40 * 7083680 * 2
def baseEnd_7083680 : Nat := 3637332642640950303122755

theorem tailTrace_7083680 : CollatzResearch.WordTrace tailWord_7083680 prefixEnd_7083680 3637332642640950303122755 := by
  unfold tailWord_7083680
  simp only [CollatzResearch.WordTrace]
  refine ⟨129181517488522315536156247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172242023318029754048208329 129181517488522315536156247)
  ·
    refine ⟨193772276232783473304234371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129181517488522315536156247 193772276232783473304234371)
    ·
      refine ⟨290658414349175209956351557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193772276232783473304234371 290658414349175209956351557)
      ·
        refine ⟨54498452690470351866815917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290658414349175209956351557 54498452690470351866815917)
        ·
          refine ⟨20436919758926381950055969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54498452690470351866815917 20436919758926381950055969)
          ·
            refine ⟨15327689819194786462541977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20436919758926381950055969 15327689819194786462541977)
            ·
              refine ⟨11495767364396089846906483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15327689819194786462541977 11495767364396089846906483)
              ·
                refine ⟨17243651046594134770359725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495767364396089846906483 17243651046594134770359725)
                ·
                  refine ⟨6466369142472800538884897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17243651046594134770359725 6466369142472800538884897)
                  ·
                    refine ⟨4849776856854600404163673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6466369142472800538884897 4849776856854600404163673)
                    ·
                      refine ⟨3637332642640950303122755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849776856854600404163673 3637332642640950303122755)
                      ·
                        rfl

theorem cell23_7083680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_7083680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083680 prefixEnd_7083680 := by exact prefixLift 7083680
  have htrace : WordTrace (prefixWord ++ tailWord_7083680) baseStart_7083680 baseEnd_7083680 := by
    simpa [prefixWord, tailWord_7083680, baseEnd_7083680] using wordTrace_append hprefix tailTrace_7083680
  have hstable : (prefixWord ++ tailWord_7083680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083680).length < 2 ^ (prefixWord ++ tailWord_7083680).sum := by decide
  have hdescent : baseEnd_7083680 < baseStart_7083680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083696 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_7083696 : Nat := 118140960795 + 7083696 * 2 ^ 59
def prefixEnd_7083696 : Nat := 4983230072969 + 3 ^ 40 * 7083696 * 2
def baseEnd_7083696 : Nat := 3637340858331422240522681

theorem tailTrace_7083696 : CollatzResearch.WordTrace tailWord_7083696 prefixEnd_7083696 3637340858331422240522681 := by
  unfold tailWord_7083696
  simp only [CollatzResearch.WordTrace]
  refine ⟨129181809272493332902447471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172242412363324443869929961 129181809272493332902447471)
  ·
    refine ⟨193772713908739999353671207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129181809272493332902447471 193772713908739999353671207)
    ·
      refine ⟨290659070863109999030506811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193772713908739999353671207 290659070863109999030506811)
      ·
        refine ⟨435988606294664998545760217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290659070863109999030506811 435988606294664998545760217)
        ·
          refine ⟨326991454720998748909320163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435988606294664998545760217 326991454720998748909320163)
          ·
            refine ⟨490487182081498123363980245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326991454720998748909320163 490487182081498123363980245)
            ·
              refine ⟨11495793330035112266343287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 490487182081498123363980245 11495793330035112266343287)
              ·
                refine ⟨17243689995052668399514931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495793330035112266343287 17243689995052668399514931)
                ·
                  refine ⟨25865534992579002599272397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17243689995052668399514931 25865534992579002599272397)
                  ·
                    refine ⟨9699575622217125974727149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25865534992579002599272397 9699575622217125974727149)
                    ·
                      refine ⟨3637340858331422240522681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9699575622217125974727149 3637340858331422240522681)
                      ·
                        rfl

theorem cell23_7083696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_7083696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083696 prefixEnd_7083696 := by exact prefixLift 7083696
  have htrace : WordTrace (prefixWord ++ tailWord_7083696) baseStart_7083696 baseEnd_7083696 := by
    simpa [prefixWord, tailWord_7083696, baseEnd_7083696] using wordTrace_append hprefix tailTrace_7083696
  have hstable : (prefixWord ++ tailWord_7083696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083696).length < 2 ^ (prefixWord ++ tailWord_7083696).sum := by decide
  have hdescent : baseEnd_7083696 < baseStart_7083696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083709 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7083709 : Nat := 118140960795 + 7083709 * 2 ^ 59
def prefixEnd_7083709 : Nat := 4983230072969 + 3 ^ 40 * 7083709 * 2
def baseEnd_7083709 : Nat := 3637347533579930689660121

theorem tailTrace_7083709 : CollatzResearch.WordTrace tailWord_7083709 prefixEnd_7083709 3637347533579930689660121 := by
  unfold tailWord_7083709
  simp only [CollatzResearch.WordTrace]
  refine ⟨258364092693939569025118181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172242728462626379350078787 258364092693939569025118181)
  ·
    refine ⟨48443267380113669192209659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258364092693939569025118181 48443267380113669192209659)
    ·
      refine ⟨72664901070170503788314489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48443267380113669192209659 72664901070170503788314489)
      ·
        refine ⟨54498675802627877841235867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72664901070170503788314489 54498675802627877841235867)
        ·
          refine ⟨81748013703941816761853801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54498675802627877841235867 81748013703941816761853801)
          ·
            refine ⟨61311010277956362571390351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81748013703941816761853801 61311010277956362571390351)
            ·
              refine ⟨91966515416934543857085527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61311010277956362571390351 91966515416934543857085527)
              ·
                refine ⟨137949773125401815785628291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91966515416934543857085527 137949773125401815785628291)
                ·
                  refine ⟨206924659688102723678442437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137949773125401815785628291 206924659688102723678442437)
                  ·
                    refine ⟨38798373691519260689707957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206924659688102723678442437 38798373691519260689707957)
                    ·
                      refine ⟨3637347533579930689660121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38798373691519260689707957 3637347533579930689660121)
                      ·
                        rfl

theorem cell23_7083709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7083709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083709 prefixEnd_7083709 := by exact prefixLift 7083709
  have htrace : WordTrace (prefixWord ++ tailWord_7083709) baseStart_7083709 baseEnd_7083709 := by
    simpa [prefixWord, tailWord_7083709, baseEnd_7083709] using wordTrace_append hprefix tailTrace_7083709
  have hstable : (prefixWord ++ tailWord_7083709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083709).length < 2 ^ (prefixWord ++ tailWord_7083709).sum := by decide
  have hdescent : baseEnd_7083709 < baseStart_7083709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083757 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7083757 : Nat := 118140960795 + 7083757 * 2 ^ 59
def prefixEnd_7083757 : Nat := 4983230072969 + 3 ^ 40 * 7083757 * 2
def baseEnd_7083757 : Nat := 3637372180651346501859901

theorem tailTrace_7083757 : CollatzResearch.WordTrace tailWord_7083757 prefixEnd_7083757 3637372180651346501859901 := by
  unfold tailWord_7083757
  simp only [CollatzResearch.WordTrace]
  refine ⟨258365843397765673222865525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172243895598510448815243683 258365843397765673222865525)
  ·
    refine ⟨24221797818540531864643643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258365843397765673222865525 24221797818540531864643643)
    ·
      refine ⟨36332696727810797796965465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24221797818540531864643643 36332696727810797796965465)
      ·
        refine ⟨27249522545858098347724099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36332696727810797796965465 27249522545858098347724099)
        ·
          refine ⟨40874283818787147521586149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27249522545858098347724099 40874283818787147521586149)
          ·
            refine ⟨7663928216022590160297403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40874283818787147521586149 7663928216022590160297403)
            ·
              refine ⟨11495892324033885240446105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663928216022590160297403 11495892324033885240446105)
              ·
                refine ⟨8621919243025413930334579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11495892324033885240446105 8621919243025413930334579)
                ·
                  refine ⟨12932878864538120895501869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621919243025413930334579 12932878864538120895501869)
                  ·
                    refine ⟨4849829574201795335813201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12932878864538120895501869 4849829574201795335813201)
                    ·
                      refine ⟨3637372180651346501859901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849829574201795335813201 3637372180651346501859901)
                      ·
                        rfl

theorem cell23_7083757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7083757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083757 prefixEnd_7083757 := by exact prefixLift 7083757
  have htrace : WordTrace (prefixWord ++ tailWord_7083757) baseStart_7083757 baseEnd_7083757 := by
    simpa [prefixWord, tailWord_7083757, baseEnd_7083757] using wordTrace_append hprefix tailTrace_7083757
  have hstable : (prefixWord ++ tailWord_7083757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083757).length < 2 ^ (prefixWord ++ tailWord_7083757).sum := by decide
  have hdescent : baseEnd_7083757 < baseStart_7083757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083759 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 9]
def baseStart_7083759 : Nat := 118140960795 + 7083759 * 2 ^ 59
def prefixEnd_7083759 : Nat := 4983230072969 + 3 ^ 40 * 7083759 * 2
def baseEnd_7083759 : Nat := 404152578623628388226099

theorem tailTrace_7083759 : CollatzResearch.WordTrace tailWord_7083759 prefixEnd_7083759 404152578623628388226099 := by
  unfold tailWord_7083759
  simp only [CollatzResearch.WordTrace]
  refine ⟨258365916343758427564438331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172243944229172285042958887 258365916343758427564438331)
  ·
    refine ⟨387548874515637641346657497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258365916343758427564438331 387548874515637641346657497)
    ·
      refine ⟨290661655886728231009993123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387548874515637641346657497 290661655886728231009993123)
      ·
        refine ⟨435992483830092346514989685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290661655886728231009993123 435992483830092346514989685)
        ·
          refine ⟨40874295359071157485780283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435992483830092346514989685 40874295359071157485780283)
          ·
            refine ⟨61311443038606736228670425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40874295359071157485780283 61311443038606736228670425)
            ·
              refine ⟨45983582278955052171502819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61311443038606736228670425 45983582278955052171502819)
              ·
                refine ⟨68975373418432578257254229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45983582278955052171502819 68975373418432578257254229)
                ·
                  refine ⟨404152578623628388226099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68975373418432578257254229 404152578623628388226099)
                  ·
                    rfl

theorem cell23_7083759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 9].length) (baseStart_7083759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083759 prefixEnd_7083759 := by exact prefixLift 7083759
  have htrace : WordTrace (prefixWord ++ tailWord_7083759) baseStart_7083759 baseEnd_7083759 := by
    simpa [prefixWord, tailWord_7083759, baseEnd_7083759] using wordTrace_append hprefix tailTrace_7083759
  have hstable : (prefixWord ++ tailWord_7083759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083759).length < 2 ^ (prefixWord ++ tailWord_7083759).sum := by decide
  have hdescent : baseEnd_7083759 < baseStart_7083759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083774 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_7083774 : Nat := 118140960795 + 7083774 * 2 ^ 59
def prefixEnd_7083774 : Nat := 4983230072969 + 3 ^ 40 * 7083774 * 2
def baseEnd_7083774 : Nat := 3637380909822472935347323

theorem tailTrace_7083774 : CollatzResearch.WordTrace tailWord_7083774 prefixEnd_7083774 3637380909822472935347323 := by
  unfold tailWord_7083774
  simp only [CollatzResearch.WordTrace]
  refine ⟨32295807929838010640779297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172244308959136056750822917 32295807929838010640779297)
  ·
    refine ⟨24221855947378507980584473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32295807929838010640779297 24221855947378507980584473)
    ·
      refine ⟨18166391960533880985438355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24221855947378507980584473 18166391960533880985438355)
      ·
        refine ⟨27249587940800821478157533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18166391960533880985438355 27249587940800821478157533)
        ·
          refine ⟨10218595477800308054309075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27249587940800821478157533 10218595477800308054309075)
          ·
            refine ⟨15327893216700462081463613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10218595477800308054309075 15327893216700462081463613)
            ·
              refine ⟨5747959956262673280548855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15327893216700462081463613 5747959956262673280548855)
              ·
                refine ⟨8621939934394009920823283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747959956262673280548855 8621939934394009920823283)
                ·
                  refine ⟨12932909901591014881234925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621939934394009920823283 12932909901591014881234925)
                  ·
                    refine ⟨4849841213096630580463097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12932909901591014881234925 4849841213096630580463097)
                    ·
                      refine ⟨3637380909822472935347323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849841213096630580463097 3637380909822472935347323)
                      ·
                        rfl

theorem cell23_7083774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_7083774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083774 prefixEnd_7083774 := by exact prefixLift 7083774
  have htrace : WordTrace (prefixWord ++ tailWord_7083774) baseStart_7083774 baseEnd_7083774 := by
    simpa [prefixWord, tailWord_7083774, baseEnd_7083774] using wordTrace_append hprefix tailTrace_7083774
  have hstable : (prefixWord ++ tailWord_7083774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083774).length < 2 ^ (prefixWord ++ tailWord_7083774).sum := by decide
  have hdescent : baseEnd_7083774 < baseStart_7083774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083843 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 2, 4, 2]
def baseStart_7083843 : Nat := 118140960795 + 7083843 * 2 ^ 59
def prefixEnd_7083843 : Nat := 4983230072969 + 3 ^ 40 * 7083843 * 2
def baseEnd_7083843 : Nat := 3637416339987633165384505

theorem tailTrace_7083843 : CollatzResearch.WordTrace tailWord_7083843 prefixEnd_7083843 3637416339987633165384505 := by
  unfold tailWord_7083843
  simp only [CollatzResearch.WordTrace]
  refine ⟨258368980075454109910496183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172245986716969406606997455 258368980075454109910496183)
  ·
    refine ⟨387553470113181164865744275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258368980075454109910496183 387553470113181164865744275)
    ·
      refine ⟨581330205169771747298616413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387553470113181164865744275 581330205169771747298616413)
      ·
        refine ⟨217998826938664405236981155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581330205169771747298616413 217998826938664405236981155)
        ·
          refine ⟨326998240407996607855471733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217998826938664405236981155 326998240407996607855471733)
          ·
            refine ⟨30656085038249681986450475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326998240407996607855471733 30656085038249681986450475)
            ·
              refine ⟨45984127557374522979675713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30656085038249681986450475 45984127557374522979675713)
              ·
                refine ⟨34488095668030892234756785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45984127557374522979675713 34488095668030892234756785)
                ·
                  refine ⟨25866071751023169176067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34488095668030892234756785 25866071751023169176067589)
                  ·
                    refine ⟨4849888453316844220512673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25866071751023169176067589 4849888453316844220512673)
                    ·
                      refine ⟨3637416339987633165384505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849888453316844220512673 3637416339987633165384505)
                      ·
                        rfl

theorem cell23_7083843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_7083843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083843 prefixEnd_7083843 := by exact prefixLift 7083843
  have htrace : WordTrace (prefixWord ++ tailWord_7083843) baseStart_7083843 baseEnd_7083843 := by
    simpa [prefixWord, tailWord_7083843, baseEnd_7083843] using wordTrace_append hprefix tailTrace_7083843
  have hstable : (prefixWord ++ tailWord_7083843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083843).length < 2 ^ (prefixWord ++ tailWord_7083843).sum := by decide
  have hdescent : baseEnd_7083843 < baseStart_7083843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083860 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_7083860 : Nat := 118140960795 + 7083860 * 2 ^ 59
def prefixEnd_7083860 : Nat := 4983230072969 + 3 ^ 40 * 7083860 * 2
def baseEnd_7083860 : Nat := 3637425069158759598871927

theorem tailTrace_7083860 : CollatzResearch.WordTrace tailWord_7083860 prefixEnd_7083860 3637425069158759598871927 := by
  unfold tailWord_7083860
  simp only [CollatzResearch.WordTrace]
  refine ⟨129184800058196260906932517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172246400077595014542576689 129184800058196260906932517)
  ·
    refine ⟨24222150010911798920049847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129184800058196260906932517 24222150010911798920049847)
    ·
      refine ⟨36333225016367698380074771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24222150010911798920049847 36333225016367698380074771)
      ·
        refine ⟨54499837524551547570112157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36333225016367698380074771 54499837524551547570112157)
        ·
          refine ⟨20437439071706830338792059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54499837524551547570112157 20437439071706830338792059)
          ·
            refine ⟨30656158607560245508188089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437439071706830338792059 30656158607560245508188089)
            ·
              refine ⟨22992118955670184131141067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30656158607560245508188089 22992118955670184131141067)
              ·
                refine ⟨34488178433505276196711601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22992118955670184131141067 34488178433505276196711601)
                ·
                  refine ⟨25866133825128957147533701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34488178433505276196711601 25866133825128957147533701)
                  ·
                    refine ⟨4849900092211679465162569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25866133825128957147533701 4849900092211679465162569)
                    ·
                      refine ⟨3637425069158759598871927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4849900092211679465162569 3637425069158759598871927)
                      ·
                        rfl

theorem cell23_7083860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_7083860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083860 prefixEnd_7083860 := by exact prefixLift 7083860
  have htrace : WordTrace (prefixWord ++ tailWord_7083860) baseStart_7083860 baseEnd_7083860 := by
    simpa [prefixWord, tailWord_7083860, baseEnd_7083860] using wordTrace_append hprefix tailTrace_7083860
  have hstable : (prefixWord ++ tailWord_7083860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083860).length < 2 ^ (prefixWord ++ tailWord_7083860).sum := by decide
  have hdescent : baseEnd_7083860 < baseStart_7083860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083916 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7083916 : Nat := 118140960795 + 7083916 * 2 ^ 59
def prefixEnd_7083916 : Nat := 4983230072969 + 3 ^ 40 * 7083916 * 2
def baseEnd_7083916 : Nat := 3637453824075411379771669

theorem tailTrace_7083916 : CollatzResearch.WordTrace tailWord_7083916 prefixEnd_7083916 3637453824075411379771669 := by
  unfold tailWord_7083916
  simp only [CollatzResearch.WordTrace]
  refine ⟨129185821302094821688951801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172247761736126428918602401 129185821302094821688951801)
  ·
    refine ⟨96889365976571116266713851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129185821302094821688951801 96889365976571116266713851)
    ·
      refine ⟨145334048964856674400070777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96889365976571116266713851 145334048964856674400070777)
      ·
        refine ⟨109000536723642505800053083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145334048964856674400070777 109000536723642505800053083)
        ·
          refine ⟨163500805085463758700079625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109000536723642505800053083 163500805085463758700079625)
          ·
            refine ⟨122625603814097819025059719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163500805085463758700079625 122625603814097819025059719)
            ·
              refine ⟨183938405721146728537589579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122625603814097819025059719 183938405721146728537589579)
              ·
                refine ⟨275907608581720092806384369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183938405721146728537589579 275907608581720092806384369)
                ·
                  refine ⟨206930706436290069604788277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275907608581720092806384369 206930706436290069604788277)
                  ·
                    refine ⟨19399753728402194025448901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206930706436290069604788277 19399753728402194025448901)
                    ·
                      refine ⟨3637453824075411379771669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19399753728402194025448901 3637453824075411379771669)
                      ·
                        rfl

theorem cell23_7083916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7083916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083916 prefixEnd_7083916 := by exact prefixLift 7083916
  have htrace : WordTrace (prefixWord ++ tailWord_7083916) baseStart_7083916 baseEnd_7083916 := by
    simpa [prefixWord, tailWord_7083916, baseEnd_7083916] using wordTrace_append hprefix tailTrace_7083916
  have hstable : (prefixWord ++ tailWord_7083916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083916).length < 2 ^ (prefixWord ++ tailWord_7083916).sum := by decide
  have hdescent : baseEnd_7083916 < baseStart_7083916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083930 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_7083930 : Nat := 118140960795 + 7083930 * 2 ^ 59
def prefixEnd_7083930 : Nat := 4983230072969 + 3 ^ 40 * 7083930 * 2
def baseEnd_7083930 : Nat := 1212487004268191441665535

theorem tailTrace_7083930 : CollatzResearch.WordTrace tailWord_7083930 prefixEnd_7083930 1212487004268191441665535 := by
  unfold tailWord_7083930
  simp only [CollatzResearch.WordTrace]
  refine ⟨64593038306534730942228311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172248102150759282512608829 64593038306534730942228311)
  ·
    refine ⟨96889557459802096413342467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64593038306534730942228311 96889557459802096413342467)
    ·
      refine ⟨145334336189703144620013701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96889557459802096413342467 145334336189703144620013701)
      ·
        refine ⟨27250188035569339616252569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145334336189703144620013701 27250188035569339616252569)
        ·
          refine ⟨20437641026677004712189427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27250188035569339616252569 20437641026677004712189427)
          ·
            refine ⟨30656461540015507068284141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437641026677004712189427 30656461540015507068284141)
            ·
              refine ⟨11496173077505815150606553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30656461540015507068284141 11496173077505815150606553)
              ·
                refine ⟨8622129808129361362954915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11496173077505815150606553 8622129808129361362954915)
                ·
                  refine ⟨12933194712194042044432373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8622129808129361362954915 12933194712194042044432373)
                  ·
                    refine ⟨1212487004268191441665535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12933194712194042044432373 1212487004268191441665535)
                    ·
                      rfl

theorem cell23_7083930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_7083930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083930 prefixEnd_7083930 := by exact prefixLift 7083930
  have htrace : WordTrace (prefixWord ++ tailWord_7083930) baseStart_7083930 baseEnd_7083930 := by
    simpa [prefixWord, tailWord_7083930, baseEnd_7083930] using wordTrace_append hprefix tailTrace_7083930
  have hstable : (prefixWord ++ tailWord_7083930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083930).length < 2 ^ (prefixWord ++ tailWord_7083930).sum := by decide
  have hdescent : baseEnd_7083930 < baseStart_7083930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083943 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 3, 6]
def baseStart_7083943 : Nat := 118140960795 + 7083943 * 2 ^ 59
def prefixEnd_7083943 : Nat := 4983230072969 + 3 ^ 40 * 7083943 * 2
def baseEnd_7083943 : Nat := 1212489229351027591378015

theorem tailTrace_7083943 : CollatzResearch.WordTrace tailWord_7083943 prefixEnd_7083943 1212489229351027591378015 := by
  unfold tailWord_7083943
  simp only [CollatzResearch.WordTrace]
  refine ⟨258372627375091826989136483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172248418250061217992757655 258372627375091826989136483)
  ·
    refine ⟨387558941062637740483704725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258372627375091826989136483 387558941062637740483704725)
    ·
      refine ⟨18166825362311144085173659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 387558941062637740483704725 18166825362311144085173659)
      ·
        refine ⟨27250238043466716127760489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18166825362311144085173659 27250238043466716127760489)
        ·
          refine ⟨20437678532600037095820367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27250238043466716127760489 20437678532600037095820367)
          ·
            refine ⟨30656517798900055643730551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437678532600037095820367 30656517798900055643730551)
            ·
              refine ⟨45984776698350083465595827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30656517798900055643730551 45984776698350083465595827)
              ·
                refine ⟨68977165047525125198393741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45984776698350083465595827 68977165047525125198393741)
                ·
                  refine ⟨25866436892821921949397653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68977165047525125198393741 25866436892821921949397653)
                  ·
                    refine ⟨1212489229351027591378015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25866436892821921949397653 1212489229351027591378015)
                    ·
                      rfl

theorem cell23_7083943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_7083943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083943 prefixEnd_7083943 := by exact prefixLift 7083943
  have htrace : WordTrace (prefixWord ++ tailWord_7083943) baseStart_7083943 baseEnd_7083943 := by
    simpa [prefixWord, tailWord_7083943, baseEnd_7083943] using wordTrace_append hprefix tailTrace_7083943
  have hstable : (prefixWord ++ tailWord_7083943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083943).length < 2 ^ (prefixWord ++ tailWord_7083943).sum := by decide
  have hdescent : baseEnd_7083943 < baseStart_7083943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083960 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_7083960 : Nat := 118140960795 + 7083960 * 2 ^ 59
def prefixEnd_7083960 : Nat := 4983230072969 + 3 ^ 40 * 7083960 * 2
def baseEnd_7083960 : Nat := 1212492139074736402540489

theorem tailTrace_7083960 : CollatzResearch.WordTrace tailWord_7083960 prefixEnd_7083960 1212492139074736402540489 := by
  unfold tailWord_7083960
  simp only [CollatzResearch.WordTrace]
  refine ⟨129186623708015119446252667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172248831610686825928336889 129186623708015119446252667)
  ·
    refine ⟨193779935562022679169379001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129186623708015119446252667 193779935562022679169379001)
    ·
      refine ⟨145334951671517009377034251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193779935562022679169379001 145334951671517009377034251)
      ·
        refine ⟨218002427507275514065551377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145334951671517009377034251 218002427507275514065551377)
        ·
          refine ⟨163501820630456635549163533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218002427507275514065551377 163501820630456635549163533)
          ·
            refine ⟨61313182736421238330936325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163501820630456635549163533 61313182736421238330936325)
            ·
              refine ⟨11496221763078982187050561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61313182736421238330936325 11496221763078982187050561)
              ·
                refine ⟨8622166322309236640287921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11496221763078982187050561 8622166322309236640287921)
                ·
                  refine ⟨6466624741731927480215941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8622166322309236640287921 6466624741731927480215941)
                  ·
                    refine ⟨1212492139074736402540489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466624741731927480215941 1212492139074736402540489)
                    ·
                      rfl

theorem cell23_7083960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_7083960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083960 prefixEnd_7083960 := by exact prefixLift 7083960
  have htrace : WordTrace (prefixWord ++ tailWord_7083960) baseStart_7083960 baseEnd_7083960 := by
    simpa [prefixWord, tailWord_7083960, baseEnd_7083960] using wordTrace_append hprefix tailTrace_7083960
  have hstable : (prefixWord ++ tailWord_7083960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083960).length < 2 ^ (prefixWord ++ tailWord_7083960).sum := by decide
  have hdescent : baseEnd_7083960 < baseStart_7083960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7083980 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7083980 : Nat := 118140960795 + 7083980 * 2 ^ 59
def prefixEnd_7083980 : Nat := 4983230072969 + 3 ^ 40 * 7083980 * 2
def baseEnd_7083980 : Nat := 3637486686837299129371375

theorem tailTrace_7083980 : CollatzResearch.WordTrace tailWord_7083980 prefixEnd_7083980 3637486686837299129371375 := by
  unfold tailWord_7083980
  simp only [CollatzResearch.WordTrace]
  refine ⟨129186988437978891154116697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172249317917305188205488929 129186988437978891154116697)
  ·
    refine ⟨96890241328484168365587523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129186988437978891154116697 96890241328484168365587523)
    ·
      refine ⟨145335361992726252548381285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96890241328484168365587523 145335361992726252548381285)
      ·
        refine ⟨27250380373636172352821491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145335361992726252548381285 27250380373636172352821491)
        ·
          refine ⟨40875570560454258529232237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27250380373636172352821491 40875570560454258529232237)
          ·
            refine ⟨15328338960170346948462089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40875570560454258529232237 15328338960170346948462089)
            ·
              refine ⟨11496254220127760211346567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15328338960170346948462089 11496254220127760211346567)
              ·
                refine ⟨17244381330191640317019851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496254220127760211346567 17244381330191640317019851)
                ·
                  refine ⟨25866571995287460475529777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17244381330191640317019851 25866571995287460475529777)
                  ·
                    refine ⟨19399928996465595356647333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25866571995287460475529777 19399928996465595356647333)
                    ·
                      refine ⟨3637486686837299129371375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19399928996465595356647333 3637486686837299129371375)
                      ·
                        rfl

theorem cell23_7083980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7083980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7083980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7083980 prefixEnd_7083980 := by exact prefixLift 7083980
  have htrace : WordTrace (prefixWord ++ tailWord_7083980) baseStart_7083980 baseEnd_7083980 := by
    simpa [prefixWord, tailWord_7083980, baseEnd_7083980] using wordTrace_append hprefix tailTrace_7083980
  have hstable : (prefixWord ++ tailWord_7083980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7083980).length < 2 ^ (prefixWord ++ tailWord_7083980).sum := by decide
  have hdescent : baseEnd_7083980 < baseStart_7083980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7083980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084017 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_7084017 : Nat := 118140960795 + 7084017 * 2 ^ 59
def prefixEnd_7084017 : Nat := 4983230072969 + 3 ^ 40 * 7084017 * 2
def baseEnd_7084017 : Nat := 3637505685621515484608705

theorem tailTrace_7084017 : CollatzResearch.WordTrace tailWord_7084017 prefixEnd_7084017 3637505685621515484608705 := by
  unfold tailWord_7084017
  simp only [CollatzResearch.WordTrace]
  refine ⟨258375326376823737627330305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172250217584549158418220203 258375326376823737627330305)
  ·
    refine ⟨193781494782617803220497729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258375326376823737627330305 193781494782617803220497729)
    ·
      refine ⟨145336121086963352415373297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193781494782617803220497729 145336121086963352415373297)
      ·
        refine ⟨109002090815222514311529973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145336121086963352415373297 109002090815222514311529973)
        ·
          refine ⟨10218946013927110716705935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109002090815222514311529973 10218946013927110716705935)
          ·
            refine ⟨15328419020890666075058903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10218946013927110716705935 15328419020890666075058903)
            ·
              refine ⟨22992628531335999112588355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15328419020890666075058903 22992628531335999112588355)
              ·
                refine ⟨34488942797003998668882533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22992628531335999112588355 34488942797003998668882533)
                ·
                  refine ⟨6466676774438249750415475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34488942797003998668882533 6466676774438249750415475)
                  ·
                    refine ⟨9700015161657374625623213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6466676774438249750415475 9700015161657374625623213)
                    ·
                      refine ⟨3637505685621515484608705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700015161657374625623213 3637505685621515484608705)
                      ·
                        rfl

theorem cell23_7084017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_7084017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084017 prefixEnd_7084017 := by exact prefixLift 7084017
  have htrace : WordTrace (prefixWord ++ tailWord_7084017) baseStart_7084017 baseEnd_7084017 := by
    simpa [prefixWord, tailWord_7084017, baseEnd_7084017] using wordTrace_append hprefix tailTrace_7084017
  have hstable : (prefixWord ++ tailWord_7084017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084017).length < 2 ^ (prefixWord ++ tailWord_7084017).sum := by decide
  have hdescent : baseEnd_7084017 < baseStart_7084017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084033 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7084033 : Nat := 118140960795 + 7084033 * 2 ^ 59
def prefixEnd_7084033 : Nat := 4983230072969 + 3 ^ 40 * 7084033 * 2
def baseEnd_7084033 : Nat := 1212504633770662474002877

theorem tailTrace_7084033 : CollatzResearch.WordTrace tailWord_7084033 prefixEnd_7084033 1212504633770662474002877 := by
  unfold tailWord_7084033
  simp only [CollatzResearch.WordTrace]
  refine ⟨258375909944765772359912753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172250606629843848239941835 258375909944765772359912753)
  ·
    refine ⟨193781932458574329269934565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258375909944765772359912753 193781932458574329269934565)
    ·
      refine ⟨36334112335982686738112731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193781932458574329269934565 36334112335982686738112731)
      ·
        refine ⟨54501168503974030107169097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36334112335982686738112731 54501168503974030107169097)
        ·
          refine ⟨40875876377980522580376823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54501168503974030107169097 40875876377980522580376823)
          ·
            refine ⟨61313814566970783870565235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40875876377980522580376823 61313814566970783870565235)
            ·
              refine ⟨91970721850456175805847853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61313814566970783870565235 91970721850456175805847853)
              ·
                refine ⟨34489020693921065927192945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91970721850456175805847853 34489020693921065927192945)
                ·
                  refine ⟨25866765520440799445394709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34489020693921065927192945 25866765520440799445394709)
                  ·
                    refine ⟨1212504633770662474002877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25866765520440799445394709 1212504633770662474002877)
                    ·
                      rfl

theorem cell23_7084033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7084033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084033 prefixEnd_7084033 := by exact prefixLift 7084033
  have htrace : WordTrace (prefixWord ++ tailWord_7084033) baseStart_7084033 baseEnd_7084033 := by
    simpa [prefixWord, tailWord_7084033, baseEnd_7084033] using wordTrace_append hprefix tailTrace_7084033
  have hstable : (prefixWord ++ tailWord_7084033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084033).length < 2 ^ (prefixWord ++ tailWord_7084033).sum := by decide
  have hdescent : baseEnd_7084033 < baseStart_7084033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084043 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_7084043 : Nat := 118140960795 + 7084043 * 2 ^ 59
def prefixEnd_7084043 : Nat := 4983230072969 + 3 ^ 40 * 7084043 * 2
def baseEnd_7084043 : Nat := 3637519036118532382883585

theorem tailTrace_7084043 : CollatzResearch.WordTrace tailWord_7084043 prefixEnd_7084043 3637519036118532382883585 := by
  unfold tailWord_7084043
  simp only [CollatzResearch.WordTrace]
  refine ⟨258376274674729544067776783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172250849783153029378517855 258376274674729544067776783)
  ·
    refine ⟨387564412012094316101665175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258376274674729544067776783 387564412012094316101665175)
    ·
      refine ⟨581346618018141474152497763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387564412012094316101665175 581346618018141474152497763)
      ·
        refine ⟨872019927027212211228746645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581346618018141474152497763 872019927027212211228746645)
        ·
          refine ⟨40875934079400572401347499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 872019927027212211228746645 40875934079400572401347499)
          ·
            refine ⟨61313901119100858602021249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40875934079400572401347499 61313901119100858602021249)
            ·
              refine ⟨45985425839325643951515937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61313901119100858602021249 45985425839325643951515937)
              ·
                refine ⟨34489069379494232963636953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45985425839325643951515937 34489069379494232963636953)
                ·
                  refine ⟨25866802034620674722727715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34489069379494232963636953 25866802034620674722727715)
                  ·
                    refine ⟨38800203051931012084091573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25866802034620674722727715 38800203051931012084091573)
                    ·
                      refine ⟨3637519036118532382883585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38800203051931012084091573 3637519036118532382883585)
                      ·
                        rfl

theorem cell23_7084043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_7084043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084043 prefixEnd_7084043 := by exact prefixLift 7084043
  have htrace : WordTrace (prefixWord ++ tailWord_7084043) baseStart_7084043 baseEnd_7084043 := by
    simpa [prefixWord, tailWord_7084043, baseEnd_7084043] using wordTrace_append hprefix tailTrace_7084043
  have hstable : (prefixWord ++ tailWord_7084043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084043).length < 2 ^ (prefixWord ++ tailWord_7084043).sum := by decide
  have hdescent : baseEnd_7084043 < baseStart_7084043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084052 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7084052 : Nat := 118140960795 + 7084052 * 2 ^ 59
def prefixEnd_7084052 : Nat := 4983230072969 + 3 ^ 40 * 7084052 * 2
def baseEnd_7084052 : Nat := 3637523657444422847671045

theorem tailTrace_7084052 : CollatzResearch.WordTrace tailWord_7084052 prefixEnd_7084052 3637523657444422847671045 := by
  unfold tailWord_7084052
  simp only [CollatzResearch.WordTrace]
  refine ⟨129188301465848469302427205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172251068621131292403236273 129188301465848469302427205)
  ·
    refine ⟨24222806524846587994205101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129188301465848469302427205 24222806524846587994205101)
    ·
      refine ⟨9083552446817470497826913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24222806524846587994205101 9083552446817470497826913)
      ·
        refine ⟨6812664335113102873370185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083552446817470497826913 6812664335113102873370185)
        ·
          refine ⟨5109498251334827155027639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812664335113102873370185 5109498251334827155027639)
          ·
            refine ⟨7664247377002240732541459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109498251334827155027639 7664247377002240732541459)
            ·
              refine ⟨11496371065503361098812189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664247377002240732541459 11496371065503361098812189)
              ·
                refine ⟨4311139149563760412054571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11496371065503361098812189 4311139149563760412054571)
                ·
                  refine ⟨6466708724345640618081857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311139149563760412054571 6466708724345640618081857)
                  ·
                    refine ⟨4850031543259230463561393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6466708724345640618081857 4850031543259230463561393)
                    ·
                      refine ⟨3637523657444422847671045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850031543259230463561393 3637523657444422847671045)
                      ·
                        rfl

theorem cell23_7084052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7084052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084052 prefixEnd_7084052 := by exact prefixLift 7084052
  have htrace : WordTrace (prefixWord ++ tailWord_7084052) baseStart_7084052 baseEnd_7084052 := by
    simpa [prefixWord, tailWord_7084052, baseEnd_7084052] using wordTrace_append hprefix tailTrace_7084052
  have hstable : (prefixWord ++ tailWord_7084052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084052).length < 2 ^ (prefixWord ++ tailWord_7084052).sum := by decide
  have hdescent : baseEnd_7084052 < baseStart_7084052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084060 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7084060 : Nat := 118140960795 + 7084060 * 2 ^ 59
def prefixEnd_7084060 : Nat := 4983230072969 + 3 ^ 40 * 7084060 * 2
def baseEnd_7084060 : Nat := 3637527765289658816371007

theorem tailTrace_7084060 : CollatzResearch.WordTrace tailWord_7084060 prefixEnd_7084060 3637527765289658816371007 := by
  unfold tailWord_7084060
  simp only [CollatzResearch.WordTrace]
  refine ⟨129188447357833977985572817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172251263143778637314097089 129188447357833977985572817)
  ·
    refine ⟨96891335518375483489179613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129188447357833977985572817 96891335518375483489179613)
    ·
      refine ⟨36334250819390806308442355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96891335518375483489179613 36334250819390806308442355)
      ·
        refine ⟨54501376229086209462663533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36334250819390806308442355 54501376229086209462663533)
        ·
          refine ⟨20438016085907328548498825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54501376229086209462663533 20438016085907328548498825)
          ·
            refine ⟨15328512064430496411374119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20438016085907328548498825 15328512064430496411374119)
            ·
              refine ⟨22992768096645744617061179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15328512064430496411374119 22992768096645744617061179)
              ·
                refine ⟨34489152144968616925591769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22992768096645744617061179 34489152144968616925591769)
                ·
                  refine ⟨25866864108726462694193827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34489152144968616925591769 25866864108726462694193827)
                  ·
                    refine ⟨38800296163089694041290741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25866864108726462694193827 38800296163089694041290741)
                    ·
                      refine ⟨3637527765289658816371007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38800296163089694041290741 3637527765289658816371007)
                      ·
                        rfl

theorem cell23_7084060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7084060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084060 prefixEnd_7084060 := by exact prefixLift 7084060
  have htrace : WordTrace (prefixWord ++ tailWord_7084060) baseStart_7084060 baseEnd_7084060 := by
    simpa [prefixWord, tailWord_7084060, baseEnd_7084060] using wordTrace_append hprefix tailTrace_7084060
  have hstable : (prefixWord ++ tailWord_7084060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084060).length < 2 ^ (prefixWord ++ tailWord_7084060).sum := by decide
  have hdescent : baseEnd_7084060 < baseStart_7084060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084074 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_7084074 : Nat := 118140960795 + 7084074 * 2 ^ 59
def prefixEnd_7084074 : Nat := 4983230072969 + 3 ^ 40 * 7084074 * 2
def baseEnd_7084074 : Nat := 3637534954018821761595943

theorem tailTrace_7084074 : CollatzResearch.WordTrace tailWord_7084074 prefixEnd_7084074 3637534954018821761595943 := by
  unfold tailWord_7084074
  simp only [CollatzResearch.WordTrace]
  refine ⟨64594351334404309090538819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172251603558411490908103517 64594351334404309090538819)
  ·
    refine ⟨96891527001606463635808229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64594351334404309090538819 96891527001606463635808229)
    ·
      refine ⟨18167161312801211931714043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96891527001606463635808229 18167161312801211931714043)
      ·
        refine ⟨27250741969201817897571065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18167161312801211931714043 27250741969201817897571065)
        ·
          refine ⟨20438056476901363423178299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27250741969201817897571065 20438056476901363423178299)
          ·
            refine ⟨30657084715352045134767449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20438056476901363423178299 30657084715352045134767449)
            ·
              refine ⟨22992813536514033851075587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30657084715352045134767449 22992813536514033851075587)
              ·
                refine ⟨34489220304771050776613381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22992813536514033851075587 34489220304771050776613381)
                ·
                  refine ⟨6466728807144572020615009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34489220304771050776613381 6466728807144572020615009)
                  ·
                    refine ⟨4850046605358429015461257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6466728807144572020615009 4850046605358429015461257)
                    ·
                      refine ⟨3637534954018821761595943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850046605358429015461257 3637534954018821761595943)
                      ·
                        rfl

theorem cell23_7084074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_7084074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084074 prefixEnd_7084074 := by exact prefixLift 7084074
  have htrace : WordTrace (prefixWord ++ tailWord_7084074) baseStart_7084074 baseEnd_7084074 := by
    simpa [prefixWord, tailWord_7084074, baseEnd_7084074] using wordTrace_append hprefix tailTrace_7084074
  have hstable : (prefixWord ++ tailWord_7084074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084074).length < 2 ^ (prefixWord ++ tailWord_7084074).sum := by decide
  have hdescent : baseEnd_7084074 < baseStart_7084074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084080 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 7]
def baseStart_7084080 : Nat := 118140960795 + 7084080 * 2 ^ 59
def prefixEnd_7084080 : Nat := 4983230072969 + 3 ^ 40 * 7084080 * 2
def baseEnd_7084080 : Nat := 404170892766972082013435

theorem tailTrace_7084080 : CollatzResearch.WordTrace tailWord_7084080 prefixEnd_7084080 404170892766972082013435 := by
  unfold tailWord_7084080
  simp only [CollatzResearch.WordTrace]
  refine ⟨129188812087797749693436847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172251749450396999591249129 129188812087797749693436847)
  ·
    refine ⟨193783218131696624540155271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129188812087797749693436847 193783218131696624540155271)
    ·
      refine ⟨290674827197544936810232907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193783218131696624540155271 290674827197544936810232907)
      ·
        refine ⟨436012240796317405215349361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290674827197544936810232907 436012240796317405215349361)
        ·
          refine ⟨327009180597238053911512021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436012240796317405215349361 327009180597238053911512021)
          ·
            refine ⟨7664277670247766888551063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 327009180597238053911512021 7664277670247766888551063)
            ·
              refine ⟨11496416505371650332826595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664277670247766888551063 11496416505371650332826595)
              ·
                refine ⟨17244624758057475499239893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496416505371650332826595 17244624758057475499239893)
                ·
                  refine ⟨404170892766972082013435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17244624758057475499239893 404170892766972082013435)
                  ·
                    rfl

theorem cell23_7084080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_7084080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084080 prefixEnd_7084080 := by exact prefixLift 7084080
  have htrace : WordTrace (prefixWord ++ tailWord_7084080) baseStart_7084080 baseEnd_7084080 := by
    simpa [prefixWord, tailWord_7084080, baseEnd_7084080] using wordTrace_append hprefix tailTrace_7084080
  have hstable : (prefixWord ++ tailWord_7084080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084080).length < 2 ^ (prefixWord ++ tailWord_7084080).sum := by decide
  have hdescent : baseEnd_7084080 < baseStart_7084080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084103 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_7084103 : Nat := 118140960795 + 7084103 * 2 ^ 59
def prefixEnd_7084103 : Nat := 4983230072969 + 3 ^ 40 * 7084103 * 2
def baseEnd_7084103 : Nat := 3637549844957802148133309

theorem tailTrace_7084103 : CollatzResearch.WordTrace tailWord_7084103 prefixEnd_7084103 3637549844957802148133309 := by
  unfold tailWord_7084103
  simp only [CollatzResearch.WordTrace]
  refine ⟨258378463054512174314960963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172252308703008116209973975 258378463054512174314960963)
  ·
    refine ⟨387567694581768261472441445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258378463054512174314960963 387567694581768261472441445)
    ·
      refine ⟨72668942734081549026082771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387567694581768261472441445 72668942734081549026082771)
      ·
        refine ⟨109003414101122323539124157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72668942734081549026082771 109003414101122323539124157)
        ·
          refine ⟨40876280287920871327171559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109003414101122323539124157 40876280287920871327171559)
          ·
            refine ⟨61314420431881306990757339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40876280287920871327171559 61314420431881306990757339)
            ·
              refine ⟨91971630647821960486136009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61314420431881306990757339 91971630647821960486136009)
              ·
                refine ⟨68978722985866470364602007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91971630647821960486136009 68978722985866470364602007)
                ·
                  refine ⟨103468084478799705546903011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68978722985866470364602007 103468084478799705546903011)
                  ·
                    refine ⟨155202126718199558320354517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103468084478799705546903011 155202126718199558320354517)
                    ·
                      refine ⟨3637549844957802148133309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155202126718199558320354517 3637549844957802148133309)
                      ·
                        rfl

theorem cell23_7084103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_7084103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084103 prefixEnd_7084103 := by exact prefixLift 7084103
  have htrace : WordTrace (prefixWord ++ tailWord_7084103) baseStart_7084103 baseEnd_7084103 := by
    simpa [prefixWord, tailWord_7084103, baseEnd_7084103] using wordTrace_append hprefix tailTrace_7084103
  have hstable : (prefixWord ++ tailWord_7084103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084103).length < 2 ^ (prefixWord ++ tailWord_7084103).sum := by decide
  have hdescent : baseEnd_7084103 < baseStart_7084103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084110 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_7084110 : Nat := 118140960795 + 7084110 * 2 ^ 59
def prefixEnd_7084110 : Nat := 4983230072969 + 3 ^ 40 * 7084110 * 2
def baseEnd_7084110 : Nat := 1212517813107461206915259

theorem tailTrace_7084110 : CollatzResearch.WordTrace tailWord_7084110 prefixEnd_7084110 1212517813107461206915259 := by
  unfold tailWord_7084110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32297339795685851813808223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172252478910324543006977189 32297339795685851813808223)
  ·
    refine ⟨48446009693528777720712335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32297339795685851813808223 48446009693528777720712335)
    ·
      refine ⟨72669014540293166581068503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48446009693528777720712335 72669014540293166581068503)
      ·
        refine ⟨109003521810439749871602755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72669014540293166581068503 109003521810439749871602755)
        ·
          refine ⟨163505282715659624807404133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109003521810439749871602755 163505282715659624807404133)
          ·
            refine ⟨30657240509186179651388275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163505282715659624807404133 30657240509186179651388275)
            ·
              refine ⟨45985860763779269477082413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30657240509186179651388275 45985860763779269477082413)
              ·
                refine ⟨17244697786417226053905905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45985860763779269477082413 17244697786417226053905905)
                ·
                  refine ⟨12933523339812919540429429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17244697786417226053905905 12933523339812919540429429)
                  ·
                    refine ⟨1212517813107461206915259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12933523339812919540429429 1212517813107461206915259)
                    ·
                      rfl

theorem cell23_7084110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_7084110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084110 prefixEnd_7084110 := by exact prefixLift 7084110
  have htrace : WordTrace (prefixWord ++ tailWord_7084110) baseStart_7084110 baseEnd_7084110 := by
    simpa [prefixWord, tailWord_7084110, baseEnd_7084110] using wordTrace_append hprefix tailTrace_7084110
  have hstable : (prefixWord ++ tailWord_7084110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084110).length < 2 ^ (prefixWord ++ tailWord_7084110).sum := by decide
  have hdescent : baseEnd_7084110 < baseStart_7084110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084157 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_7084157 : Nat := 118140960795 + 7084157 * 2 ^ 59
def prefixEnd_7084157 : Nat := 4983230072969 + 3 ^ 40 * 7084157 * 2
def baseEnd_7084157 : Nat := 1212525857637714978952687

theorem tailTrace_7084157 : CollatzResearch.WordTrace tailWord_7084157 prefixEnd_7084157 1212525857637714978952687 := by
  unfold tailWord_7084157
  simp only [CollatzResearch.WordTrace]
  refine ⟨258380432596316541537426725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172253621730877694358284483 258380432596316541537426725)
  ·
    refine ⟨48446331111809351538267511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258380432596316541537426725 48446331111809351538267511)
    ·
      refine ⟨72669496667714027307401267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48446331111809351538267511 72669496667714027307401267)
      ·
        refine ⟨109004245001571040961101901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72669496667714027307401267 109004245001571040961101901)
        ·
          refine ⟨40876591875589140360413213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109004245001571040961101901 40876591875589140360413213)
          ·
            refine ⟨15328721953345927635154955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40876591875589140360413213 15328721953345927635154955)
            ·
              refine ⟨22993082930018891452732433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15328721953345927635154955 22993082930018891452732433)
              ·
                refine ⟨17244812197514168589549325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22993082930018891452732433 17244812197514168589549325)
                ·
                  refine ⟨6466804574067813221080997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17244812197514168589549325 6466804574067813221080997)
                  ·
                    refine ⟨1212525857637714978952687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466804574067813221080997 1212525857637714978952687)
                    ·
                      rfl

theorem cell23_7084157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_7084157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084157 prefixEnd_7084157 := by exact prefixLift 7084157
  have htrace : WordTrace (prefixWord ++ tailWord_7084157) baseStart_7084157 baseEnd_7084157 := by
    simpa [prefixWord, tailWord_7084157, baseEnd_7084157] using wordTrace_append hprefix tailTrace_7084157
  have hstable : (prefixWord ++ tailWord_7084157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084157).length < 2 ^ (prefixWord ++ tailWord_7084157).sum := by decide
  have hdescent : baseEnd_7084157 < baseStart_7084157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084167 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_7084167 : Nat := 118140960795 + 7084167 * 2 ^ 59
def prefixEnd_7084167 : Nat := 4983230072969 + 3 ^ 40 * 7084167 * 2
def baseEnd_7084167 : Nat := 3637582707719689897733015

theorem tailTrace_7084167 : CollatzResearch.WordTrace tailWord_7084167 prefixEnd_7084167 3637582707719689897733015 := by
  unfold tailWord_7084167
  simp only [CollatzResearch.WordTrace]
  refine ⟨258380797326280313245290755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172253864884186875496860503 258380797326280313245290755)
  ·
    refine ⟨387571195989420469867936133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258380797326280313245290755 387571195989420469867936133)
    ·
      refine ⟨72669599248016338100238025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387571195989420469867936133 72669599248016338100238025)
      ·
        refine ⟨54502199436012253575178519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72669599248016338100238025 54502199436012253575178519)
        ·
          refine ⟨81753299154018380362767779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54502199436012253575178519 81753299154018380362767779)
          ·
            refine ⟨122629948731027570544151669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81753299154018380362767779 122629948731027570544151669)
            ·
              refine ⟨11496557693533834738514219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122629948731027570544151669 11496557693533834738514219)
              ·
                refine ⟨17244836540300752107771329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496557693533834738514219 17244836540300752107771329)
                ·
                  refine ⟨12933627405225564080828497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17244836540300752107771329 12933627405225564080828497)
                  ·
                    refine ⟨9700220553919173060621373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12933627405225564080828497 9700220553919173060621373)
                    ·
                      refine ⟨3637582707719689897733015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700220553919173060621373 3637582707719689897733015)
                      ·
                        rfl

theorem cell23_7084167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_7084167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084167 prefixEnd_7084167 := by exact prefixLift 7084167
  have htrace : WordTrace (prefixWord ++ tailWord_7084167) baseStart_7084167 baseEnd_7084167 := by
    simpa [prefixWord, tailWord_7084167, baseEnd_7084167] using wordTrace_append hprefix tailTrace_7084167
  have hstable : (prefixWord ++ tailWord_7084167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084167).length < 2 ^ (prefixWord ++ tailWord_7084167).sum := by decide
  have hdescent : baseEnd_7084167 < baseStart_7084167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084217 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_7084217 : Nat := 118140960795 + 7084217 * 2 ^ 59
def prefixEnd_7084217 : Nat := 4983230072969 + 3 ^ 40 * 7084217 * 2
def baseEnd_7084217 : Nat := 1212536127250804900702595

theorem tailTrace_7084217 : CollatzResearch.WordTrace tailWord_7084217 prefixEnd_7084217 1212536127250804900702595 := by
  unfold tailWord_7084217
  simp only [CollatzResearch.WordTrace]
  refine ⟨258382620976099171784610905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172255080650732781189740603 258382620976099171784610905)
  ·
    refine ⟨193786965732074378838458179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258382620976099171784610905 193786965732074378838458179)
    ·
      refine ⟨290680448598111568257687269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193786965732074378838458179 290680448598111568257687269)
      ·
        refine ⟨54502584112145919048316363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290680448598111568257687269 54502584112145919048316363)
        ·
          refine ⟨81753876168218878572474545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54502584112145919048316363 81753876168218878572474545)
          ·
            refine ⟨61315407126164158929355909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81753876168218878572474545 61315407126164158929355909)
            ·
              refine ⟨11496638836155779799254233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61315407126164158929355909 11496638836155779799254233)
              ·
                refine ⟨8622479127116834849440675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11496638836155779799254233 8622479127116834849440675)
                ·
                  refine ⟨12933718690675252274161013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8622479127116834849440675 12933718690675252274161013)
                  ·
                    refine ⟨1212536127250804900702595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12933718690675252274161013 1212536127250804900702595)
                    ·
                      rfl

theorem cell23_7084217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_7084217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084217 prefixEnd_7084217 := by exact prefixLift 7084217
  have htrace : WordTrace (prefixWord ++ tailWord_7084217) baseStart_7084217 baseEnd_7084217 := by
    simpa [prefixWord, tailWord_7084217, baseEnd_7084217] using wordTrace_append hprefix tailTrace_7084217
  have hstable : (prefixWord ++ tailWord_7084217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084217).length < 2 ^ (prefixWord ++ tailWord_7084217).sum := by decide
  have hdescent : baseEnd_7084217 < baseStart_7084217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084225 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7084225 : Nat := 118140960795 + 7084225 * 2 ^ 59
def prefixEnd_7084225 : Nat := 4983230072969 + 3 ^ 40 * 7084225 * 2
def baseEnd_7084225 : Nat := 1212537496532550223602583

theorem tailTrace_7084225 : CollatzResearch.WordTrace tailWord_7084225 prefixEnd_7084225 1212537496532550223602583 := by
  unfold tailWord_7084225
  simp only [CollatzResearch.WordTrace]
  refine ⟨258382912760070189150902129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172255275173380126100601419 258382912760070189150902129)
  ·
    refine ⟨193787184570052641863176597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258382912760070189150902129 193787184570052641863176597)
    ·
      refine ⟨9083774276721217587336403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193787184570052641863176597 9083774276721217587336403)
      ·
        refine ⟨13625661415081826381004605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9083774276721217587336403 13625661415081826381004605)
        ·
          refine ⟨5109623030655684892876727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13625661415081826381004605 5109623030655684892876727)
          ·
            refine ⟨7664434545983527339315091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109623030655684892876727 7664434545983527339315091)
            ·
              refine ⟨11496651818975291008972637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664434545983527339315091 11496651818975291008972637)
              ·
                refine ⟨4311244432115734128364739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11496651818975291008972637 4311244432115734128364739)
                ·
                  refine ⟨6466866648173601192547109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311244432115734128364739 6466866648173601192547109)
                  ·
                    refine ⟨1212537496532550223602583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466866648173601192547109 1212537496532550223602583)
                    ·
                      rfl

theorem cell23_7084225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7084225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084225 prefixEnd_7084225 := by exact prefixLift 7084225
  have htrace : WordTrace (prefixWord ++ tailWord_7084225) baseStart_7084225 baseEnd_7084225 := by
    simpa [prefixWord, tailWord_7084225, baseEnd_7084225] using wordTrace_append hprefix tailTrace_7084225
  have hstable : (prefixWord ++ tailWord_7084225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084225).length < 2 ^ (prefixWord ++ tailWord_7084225).sum := by decide
  have hdescent : baseEnd_7084225 < baseStart_7084225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084247 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 2, 4]
def baseStart_7084247 : Nat := 118140960795 + 7084247 * 2 ^ 59
def prefixEnd_7084247 : Nat := 4983230072969 + 3 ^ 40 * 7084247 * 2
def baseEnd_7084247 : Nat := 1212541262057349861577549

theorem tailTrace_7084247 : CollatzResearch.WordTrace tailWord_7084247 prefixEnd_7084247 1212541262057349861577549 := by
  unfold tailWord_7084247
  simp only [CollatzResearch.WordTrace]
  refine ⟨258383715165990486908202995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172255810110660324605468663 258383715165990486908202995)
  ·
    refine ⟨387575572748985730362304493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258383715165990486908202995 387575572748985730362304493)
    ·
      refine ⟨145340839780869648885864185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387575572748985730362304493 145340839780869648885864185)
      ·
        refine ⟨109005629835652236664398139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145340839780869648885864185 109005629835652236664398139)
        ·
          refine ⟨163508444753478354996597209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109005629835652236664398139 163508444753478354996597209)
          ·
            refine ⟨122631333565108766247447907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163508444753478354996597209 122631333565108766247447907)
            ·
              refine ⟨183947000347663149371171861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122631333565108766247447907 183947000347663149371171861)
              ·
                refine ⟨8622515641296710126773681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183947000347663149371171861 8622515641296710126773681)
                ·
                  refine ⟨6466886730972532595080261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8622515641296710126773681 6466886730972532595080261)
                  ·
                    refine ⟨1212541262057349861577549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466886730972532595080261 1212541262057349861577549)
                    ·
                      rfl

theorem cell23_7084247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_7084247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084247 prefixEnd_7084247 := by exact prefixLift 7084247
  have htrace : WordTrace (prefixWord ++ tailWord_7084247) baseStart_7084247 baseEnd_7084247 := by
    simpa [prefixWord, tailWord_7084247, baseEnd_7084247] using wordTrace_append hprefix tailTrace_7084247
  have hstable : (prefixWord ++ tailWord_7084247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084247).length < 2 ^ (prefixWord ++ tailWord_7084247).sum := by decide
  have hdescent : baseEnd_7084247 < baseStart_7084247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084248 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 1, 1, 3]
def baseStart_7084248 : Nat := 118140960795 + 7084248 * 2 ^ 59
def prefixEnd_7084248 : Nat := 4983230072969 + 3 ^ 40 * 7084248 * 2
def baseEnd_7084248 : Nat := 3637624299652704080820143

theorem tailTrace_7084248 : CollatzResearch.WordTrace tailWord_7084248 prefixEnd_7084248 3637624299652704080820143 := by
  unfold tailWord_7084248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129191875819493432039494699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172255834425991242719326265 129191875819493432039494699)
  ·
    refine ⟨193787813729240148059242049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129191875819493432039494699 193787813729240148059242049)
    ·
      refine ⟨145340860296930111044431537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193787813729240148059242049 145340860296930111044431537)
      ·
        refine ⟨109005645222697583283323653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145340860296930111044431537 109005645222697583283323653)
        ·
          refine ⟨20438558479255796865623185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109005645222697583283323653 20438558479255796865623185)
          ·
            refine ⟨15328918859441847649217389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20438558479255796865623185 15328918859441847649217389)
            ·
              refine ⟨5748344572290692868456521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15328918859441847649217389 5748344572290692868456521)
              ·
                refine ⟨4311258429218019651342391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748344572290692868456521 4311258429218019651342391)
                ·
                  refine ⟨6466887643827029477013587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311258429218019651342391 6466887643827029477013587)
                  ·
                    refine ⟨9700331465740544215520381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6466887643827029477013587 9700331465740544215520381)
                    ·
                      refine ⟨3637624299652704080820143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700331465740544215520381 3637624299652704080820143)
                      ·
                        rfl

theorem cell23_7084248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_7084248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084248 prefixEnd_7084248 := by exact prefixLift 7084248
  have htrace : WordTrace (prefixWord ++ tailWord_7084248) baseStart_7084248 baseEnd_7084248 := by
    simpa [prefixWord, tailWord_7084248, baseEnd_7084248] using wordTrace_append hprefix tailTrace_7084248
  have hstable : (prefixWord ++ tailWord_7084248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084248).length < 2 ^ (prefixWord ++ tailWord_7084248).sum := by decide
  have hdescent : baseEnd_7084248 < baseStart_7084248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084250 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_7084250 : Nat := 118140960795 + 7084250 * 2 ^ 59
def prefixEnd_7084250 : Nat := 4983230072969 + 3 ^ 40 * 7084250 * 2
def baseEnd_7084250 : Nat := 3637625326614013072995133

theorem tailTrace_7084250 : CollatzResearch.WordTrace tailWord_7084250 prefixEnd_7084250 3637625326614013072995133 := by
  unfold tailWord_7084250
  simp only [CollatzResearch.WordTrace]
  refine ⟨64595956146244904605140551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172255883056653078947041469 64595956146244904605140551)
  ·
    refine ⟨96893934219367356907710827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64595956146244904605140551 96893934219367356907710827)
    ·
      refine ⟨145340901329051035361566241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96893934219367356907710827 145340901329051035361566241)
      ·
        refine ⟨109005675996788276521174681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145340901329051035361566241 109005675996788276521174681)
        ·
          refine ⟨81754256997591207390881011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109005675996788276521174681 81754256997591207390881011)
          ·
            refine ⟨122631385496386811086321517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81754256997591207390881011 122631385496386811086321517)
            ·
              refine ⟨45986769561145054157370569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122631385496386811086321517 45986769561145054157370569)
              ·
                refine ⟨34490077170858790618027927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45986769561145054157370569 34490077170858790618027927)
                ·
                  refine ⟨51735115756288185927041891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34490077170858790618027927 51735115756288185927041891)
                  ·
                    refine ⟨77602673634432278890562837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51735115756288185927041891 77602673634432278890562837)
                    ·
                      refine ⟨3637625326614013072995133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77602673634432278890562837 3637625326614013072995133)
                      ·
                        rfl

theorem cell23_7084250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_7084250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084250 prefixEnd_7084250 := by exact prefixLift 7084250
  have htrace : WordTrace (prefixWord ++ tailWord_7084250) baseStart_7084250 baseEnd_7084250 := by
    simpa [prefixWord, tailWord_7084250, baseEnd_7084250] using wordTrace_append hprefix tailTrace_7084250
  have hstable : (prefixWord ++ tailWord_7084250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084250).length < 2 ^ (prefixWord ++ tailWord_7084250).sum := by decide
  have hdescent : baseEnd_7084250 < baseStart_7084250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084257 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_7084257 : Nat := 118140960795 + 7084257 * 2 ^ 59
def prefixEnd_7084257 : Nat := 4983230072969 + 3 ^ 40 * 7084257 * 2
def baseEnd_7084257 : Nat := 3637628920978594545607601

theorem tailTrace_7084257 : CollatzResearch.WordTrace tailWord_7084257 prefixEnd_7084257 3637628920978594545607601 := by
  unfold tailWord_7084257
  simp only [CollatzResearch.WordTrace]
  refine ⟨258384079895954258616067025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172256053263969505744044683 258384079895954258616067025)
  ·
    refine ⟨193788059921965693962050269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258384079895954258616067025 193788059921965693962050269)
    ·
      refine ⟨72670522470737135235768851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193788059921965693962050269 72670522470737135235768851)
      ·
        refine ⟨109005783706105702853653277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72670522470737135235768851 109005783706105702853653277)
        ·
          refine ⟨40877168889789638570119979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109005783706105702853653277 40877168889789638570119979)
          ·
            refine ⟨61315753334684457855179969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40877168889789638570119979 61315753334684457855179969)
            ·
              refine ⟨45986815001013343391384977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61315753334684457855179969 45986815001013343391384977)
              ·
                refine ⟨34490111250760007543538733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45986815001013343391384977 34490111250760007543538733)
                ·
                  refine ⟨12933791719035002828827025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34490111250760007543538733 12933791719035002828827025)
                  ·
                    refine ⟨9700343789276252121620269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12933791719035002828827025 9700343789276252121620269)
                    ·
                      refine ⟨3637628920978594545607601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700343789276252121620269 3637628920978594545607601)
                      ·
                        rfl

theorem cell23_7084257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_7084257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084257 prefixEnd_7084257 := by exact prefixLift 7084257
  have htrace : WordTrace (prefixWord ++ tailWord_7084257) baseStart_7084257 baseEnd_7084257 := by
    simpa [prefixWord, tailWord_7084257, baseEnd_7084257] using wordTrace_append hprefix tailTrace_7084257
  have hstable : (prefixWord ++ tailWord_7084257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084257).length < 2 ^ (prefixWord ++ tailWord_7084257).sum := by decide
  have hdescent : baseEnd_7084257 < baseStart_7084257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084264 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_7084264 : Nat := 118140960795 + 7084264 * 2 ^ 59
def prefixEnd_7084264 : Nat := 4983230072969 + 3 ^ 40 * 7084264 * 2
def baseEnd_7084264 : Nat := 1212544171781058672740023

theorem tailTrace_7084264 : CollatzResearch.WordTrace tailWord_7084264 prefixEnd_7084264 1212544171781058672740023 := by
  unfold tailWord_7084264
  simp only [CollatzResearch.WordTrace]
  refine ⟨129192167603464449405785923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172256223471285932541047897 129192167603464449405785923)
  ·
    refine ⟨193788251405196674108678885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129192167603464449405785923 193788251405196674108678885)
    ·
      refine ⟨36335297138474376395377291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193788251405196674108678885 36335297138474376395377291)
      ·
        refine ⟨54502945707711564593065937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36335297138474376395377291 54502945707711564593065937)
        ·
          refine ⟨40877209280783673444799453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54502945707711564593065937 40877209280783673444799453)
          ·
            refine ⟨15328953480293877541799795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40877209280783673444799453 15328953480293877541799795)
            ·
              refine ⟨22993430220440816312699693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15328953480293877541799795 22993430220440816312699693)
              ·
                refine ⟨8622536332665306117262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22993430220440816312699693 8622536332665306117262385)
                ·
                  refine ⟨6466902249498979587946789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8622536332665306117262385 6466902249498979587946789)
                  ·
                    refine ⟨1212544171781058672740023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466902249498979587946789 1212544171781058672740023)
                    ·
                      rfl

theorem cell23_7084264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_7084264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084264 prefixEnd_7084264 := by exact prefixLift 7084264
  have htrace : WordTrace (prefixWord ++ tailWord_7084264) baseStart_7084264 baseEnd_7084264 := by
    simpa [prefixWord, tailWord_7084264, baseEnd_7084264] using wordTrace_append hprefix tailTrace_7084264
  have hstable : (prefixWord ++ tailWord_7084264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084264).length < 2 ^ (prefixWord ++ tailWord_7084264).sum := by decide
  have hdescent : baseEnd_7084264 < baseStart_7084264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084274 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7084274 : Nat := 118140960795 + 7084274 * 2 ^ 59
def prefixEnd_7084274 : Nat := 4983230072969 + 3 ^ 40 * 7084274 * 2
def baseEnd_7084274 : Nat := 3637637650149720979095023

theorem tailTrace_7084274 : CollatzResearch.WordTrace tailWord_7084274 prefixEnd_7084274 3637637650149720979095023 := by
  unfold tailWord_7084274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64596174984223167629858969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172256466624595113679623917 64596174984223167629858969)
  ·
    refine ⟨48447131238167375722394227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64596174984223167629858969 48447131238167375722394227)
    ·
      refine ⟨72670696857251063583591341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48447131238167375722394227 72670696857251063583591341)
      ·
        refine ⟨27251511321469148843846753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72670696857251063583591341 27251511321469148843846753)
        ·
          refine ⟨20438633491101861632885065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27251511321469148843846753 20438633491101861632885065)
          ·
            refine ⟨15328975118326396224663799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20438633491101861632885065 15328975118326396224663799)
            ·
              refine ⟨22993462677489594336995699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15328975118326396224663799 22993462677489594336995699)
              ·
                refine ⟨34490194016234391505493549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22993462677489594336995699 34490194016234391505493549)
                ·
                  refine ⟨12933822756087896814560081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34490194016234391505493549 12933822756087896814560081)
                  ·
                    refine ⟨9700367067065922610920061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12933822756087896814560081 9700367067065922610920061)
                    ·
                      refine ⟨3637637650149720979095023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700367067065922610920061 3637637650149720979095023)
                      ·
                        rfl

theorem cell23_7084274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7084274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084274 prefixEnd_7084274 := by exact prefixLift 7084274
  have htrace : WordTrace (prefixWord ++ tailWord_7084274) baseStart_7084274 baseEnd_7084274 := by
    simpa [prefixWord, tailWord_7084274, baseEnd_7084274] using wordTrace_append hprefix tailTrace_7084274
  have hstable : (prefixWord ++ tailWord_7084274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084274).length < 2 ^ (prefixWord ++ tailWord_7084274).sum := by decide
  have hdescent : baseEnd_7084274 < baseStart_7084274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084287 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_7084287 : Nat := 118140960795 + 7084287 * 2 ^ 59
def prefixEnd_7084287 : Nat := 4983230072969 + 3 ^ 40 * 7084287 * 2
def baseEnd_7084287 : Nat := 3637644325398229428232463

theorem tailTrace_7084287 : CollatzResearch.WordTrace tailWord_7084287 prefixEnd_7084287 3637644325398229428232463 := by
  unfold tailWord_7084287
  simp only [CollatzResearch.WordTrace]
  refine ⟨258385174085845573739659115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172256782723897049159772743 258385174085845573739659115)
  ·
    refine ⟨387577761128768360609488673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258385174085845573739659115 387577761128768360609488673)
    ·
      refine ⟨290683320846576270457116505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387577761128768360609488673 290683320846576270457116505)
      ·
        refine ⟨218012490634932202842837379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290683320846576270457116505 218012490634932202842837379)
        ·
          refine ⟨327018735952398304264256069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218012490634932202842837379 327018735952398304264256069)
          ·
            refine ⟨61316012991074682049548013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327018735952398304264256069 61316012991074682049548013)
            ·
              refine ⟨22993504871653005768580505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61316012991074682049548013 22993504871653005768580505)
              ·
                refine ⟨17245128653739754326435379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22993504871653005768580505 17245128653739754326435379)
                ·
                  refine ⟨25867692980609631489653069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17245128653739754326435379 25867692980609631489653069)
                  ·
                    refine ⟨9700384867728611808619901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25867692980609631489653069 9700384867728611808619901)
                    ·
                      refine ⟨3637644325398229428232463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700384867728611808619901 3637644325398229428232463)
                      ·
                        rfl

theorem cell23_7084287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_7084287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084287 prefixEnd_7084287 := by exact prefixLift 7084287
  have htrace : WordTrace (prefixWord ++ tailWord_7084287) baseStart_7084287 baseEnd_7084287 := by
    simpa [prefixWord, tailWord_7084287, baseEnd_7084287] using wordTrace_append hprefix tailTrace_7084287
  have hstable : (prefixWord ++ tailWord_7084287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084287).length < 2 ^ (prefixWord ++ tailWord_7084287).sum := by decide
  have hdescent : baseEnd_7084287 < baseStart_7084287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084305 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 1, 2, 2]
def baseStart_7084305 : Nat := 118140960795 + 7084305 * 2 ^ 59
def prefixEnd_7084305 : Nat := 4983230072969 + 3 ^ 40 * 7084305 * 2
def baseEnd_7084305 : Nat := 3637653568050010357807381

theorem tailTrace_7084305 : CollatzResearch.WordTrace tailWord_7084305 prefixEnd_7084305 3637653568050010357807381 := by
  unfold tailWord_7084305
  simp only [CollatzResearch.WordTrace]
  refine ⟨258385830599780362813814369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172257220399853575209209579 258385830599780362813814369)
  ·
    refine ⟨193789372949835272110360777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258385830599780362813814369 193789372949835272110360777)
    ·
      refine ⟨145342029712376454082770583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193789372949835272110360777 145342029712376454082770583)
      ·
        refine ⟨218013044568564681124155875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145342029712376454082770583 218013044568564681124155875)
        ·
          refine ⟨327019566852847021686233813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218013044568564681124155875 327019566852847021686233813)
          ·
            refine ⟨7664521098113602070771105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 327019566852847021686233813 7664521098113602070771105)
            ·
              refine ⟨5748390823585201553078329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664521098113602070771105 5748390823585201553078329)
              ·
                refine ⟨4311293117688901164808747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748390823585201553078329 4311293117688901164808747)
                ·
                  refine ⟨6466939676533351747213121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311293117688901164808747 6466939676533351747213121)
                  ·
                    refine ⟨4850204757400013810409841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6466939676533351747213121 4850204757400013810409841)
                    ·
                      refine ⟨3637653568050010357807381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850204757400013810409841 3637653568050010357807381)
                      ·
                        rfl

theorem cell23_7084305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_7084305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084305 prefixEnd_7084305 := by exact prefixLift 7084305
  have htrace : WordTrace (prefixWord ++ tailWord_7084305) baseStart_7084305 baseEnd_7084305 := by
    simpa [prefixWord, tailWord_7084305, baseEnd_7084305] using wordTrace_append hprefix tailTrace_7084305
  have hstable : (prefixWord ++ tailWord_7084305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084305).length < 2 ^ (prefixWord ++ tailWord_7084305).sum := by decide
  have hdescent : baseEnd_7084305 < baseStart_7084305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084344 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_7084344 : Nat := 118140960795 + 7084344 * 2 ^ 59
def prefixEnd_7084344 : Nat := 4983230072969 + 3 ^ 40 * 7084344 * 2
def baseEnd_7084344 : Nat := 3637673593795535705219701

theorem tailTrace_7084344 : CollatzResearch.WordTrace tailWord_7084344 prefixEnd_7084344 3637673593795535705219701 := by
  unfold tailWord_7084344
  simp only [CollatzResearch.WordTrace]
  refine ⟨129193626523319536237242043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172258168697759381649656057 129193626523319536237242043)
  ·
    refine ⟨193790439784979304355863065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129193626523319536237242043 193790439784979304355863065)
    ·
      refine ⟨145342829838734478266897299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193790439784979304355863065 145342829838734478266897299)
      ·
        refine ⟨218014244758101717400345949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145342829838734478266897299 218014244758101717400345949)
        ·
          refine ⟨81755341784288144025129731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218014244758101717400345949 81755341784288144025129731)
          ·
            refine ⟨122633012676432216037694597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81755341784288144025129731 122633012676432216037694597)
            ·
              refine ⟨22993689876831040507067737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122633012676432216037694597 22993689876831040507067737)
              ·
                refine ⟨17245267407623280380300803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22993689876831040507067737 17245267407623280380300803)
                ·
                  refine ⟨25867901111434920570451205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17245267407623280380300803 25867901111434920570451205)
                  ·
                    refine ⟨4850231458394047606959601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25867901111434920570451205 4850231458394047606959601)
                    ·
                      refine ⟨3637673593795535705219701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850231458394047606959601 3637673593795535705219701)
                      ·
                        rfl

theorem cell23_7084344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_7084344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084344 prefixEnd_7084344 := by exact prefixLift 7084344
  have htrace : WordTrace (prefixWord ++ tailWord_7084344) baseStart_7084344 baseEnd_7084344 := by
    simpa [prefixWord, tailWord_7084344, baseEnd_7084344] using wordTrace_append hprefix tailTrace_7084344
  have hstable : (prefixWord ++ tailWord_7084344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084344).length < 2 ^ (prefixWord ++ tailWord_7084344).sum := by decide
  have hdescent : baseEnd_7084344 < baseStart_7084344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084397 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_7084397 : Nat := 118140960795 + 7084397 * 2 ^ 59
def prefixEnd_7084397 : Nat := 4983230072969 + 3 ^ 40 * 7084397 * 2
def baseEnd_7084397 : Nat := 1212566936090074665952319

theorem tailTrace_7084397 : CollatzResearch.WordTrace tailWord_7084397 prefixEnd_7084397 1212566936090074665952319 := by
  unfold tailWord_7084397
  simp only [CollatzResearch.WordTrace]
  refine ⟨258389186115447062526163445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172259457410298041684108963 258389186115447062526163445)
  ·
    refine ⟨24223986198323162111827823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258389186115447062526163445 24223986198323162111827823)
    ·
      refine ⟨36335979297484743167741735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24223986198323162111827823 36335979297484743167741735)
      ·
        refine ⟨54503968946227114751612603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36335979297484743167741735 54503968946227114751612603)
        ·
          refine ⟨81755953419340672127418905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54503968946227114751612603 81755953419340672127418905)
          ·
            refine ⟨61316965064505504095564179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81755953419340672127418905 61316965064505504095564179)
            ·
              refine ⟨91975447596758256143346269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61316965064505504095564179 91975447596758256143346269)
              ·
                refine ⟨34490792848784346053754851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91975447596758256143346269 34490792848784346053754851)
                ·
                  refine ⟨51736189273176519080632277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34490792848784346053754851 51736189273176519080632277)
                  ·
                    refine ⟨1212566936090074665952319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51736189273176519080632277 1212566936090074665952319)
                    ·
                      rfl

theorem cell23_7084397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_7084397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084397 prefixEnd_7084397 := by exact prefixLift 7084397
  have htrace : WordTrace (prefixWord ++ tailWord_7084397) baseStart_7084397 baseEnd_7084397 := by
    simpa [prefixWord, tailWord_7084397, baseEnd_7084397] using wordTrace_append hprefix tailTrace_7084397
  have hstable : (prefixWord ++ tailWord_7084397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084397).length < 2 ^ (prefixWord ++ tailWord_7084397).sum := by decide
  have hdescent : baseEnd_7084397 < baseStart_7084397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084418 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7084418 : Nat := 118140960795 + 7084418 * 2 ^ 59
def prefixEnd_7084418 : Nat := 4983230072969 + 3 ^ 40 * 7084418 * 2
def baseEnd_7084418 : Nat := 404190176818218712854929

theorem tailTrace_7084418 : CollatzResearch.WordTrace tailWord_7084418 prefixEnd_7084418 404190176818218712854929 := by
  unfold tailWord_7084418
  simp only [CollatzResearch.WordTrace]
  refine ⟨64597488012092745778169477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172259968032247322075118605 64597488012092745778169477)
  ·
    refine ⟨12112029002267389833406777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64597488012092745778169477 12112029002267389833406777)
    ·
      refine ⟨9084021751700542375055083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12112029002267389833406777 9084021751700542375055083)
      ·
        refine ⟨13626032627550813562582625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084021751700542375055083 13626032627550813562582625)
        ·
          refine ⟨10219524470663110171936969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13626032627550813562582625 10219524470663110171936969)
          ·
            refine ⟨7664643352997332628952727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10219524470663110171936969 7664643352997332628952727)
            ·
              refine ⟨11496965029495998943429091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664643352997332628952727 11496965029495998943429091)
              ·
                refine ⟨17245447544243998415143637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496965029495998943429091 17245447544243998415143637)
                ·
                  refine ⟨404190176818218712854929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17245447544243998415143637 404190176818218712854929)
                  ·
                    rfl

theorem cell23_7084418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7084418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084418 prefixEnd_7084418 := by exact prefixLift 7084418
  have htrace : WordTrace (prefixWord ++ tailWord_7084418) baseStart_7084418 baseEnd_7084418 := by
    simpa [prefixWord, tailWord_7084418, baseEnd_7084418] using wordTrace_append hprefix tailTrace_7084418
  have hstable : (prefixWord ++ tailWord_7084418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084418).length < 2 ^ (prefixWord ++ tailWord_7084418).sum := by decide
  have hdescent : baseEnd_7084418 < baseStart_7084418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084501 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7084501 : Nat := 118140960795 + 7084501 * 2 ^ 59
def prefixEnd_7084501 : Nat := 4983230072969 + 3 ^ 40 * 7084501 * 2
def baseEnd_7084501 : Nat := 3637754210258291590956479

theorem tailTrace_7084501 : CollatzResearch.WordTrace tailWord_7084501 prefixEnd_7084501 3637754210258291590956479 := by
  unfold tailWord_7084501
  simp only [CollatzResearch.WordTrace]
  refine ⟨258392979307070288287949357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172261986204713525525299571 258392979307070288287949357)
  ·
    refine ⟨96897367240151358107981009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258392979307070288287949357 96897367240151358107981009)
    ·
      refine ⟨72673025430113518580985757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96897367240151358107981009 72673025430113518580985757)
      ·
        refine ⟨27252384536292569467869659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72673025430113518580985757 27252384536292569467869659)
        ·
          refine ⟨40878576804438854201804489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252384536292569467869659 40878576804438854201804489)
          ·
            refine ⟨30658932603329140651353367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40878576804438854201804489 30658932603329140651353367)
            ·
              refine ⟨45988398904993710977030051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30658932603329140651353367 45988398904993710977030051)
              ·
                refine ⟨68982598357490566465545077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45988398904993710977030051 68982598357490566465545077)
                ·
                  refine ⟨6467118596014740606144851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68982598357490566465545077 6467118596014740606144851)
                  ·
                    refine ⟨9700677894022110909217277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6467118596014740606144851 9700677894022110909217277)
                    ·
                      refine ⟨3637754210258291590956479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700677894022110909217277 3637754210258291590956479)
                      ·
                        rfl

theorem cell23_7084501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7084501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084501 prefixEnd_7084501 := by exact prefixLift 7084501
  have htrace : WordTrace (prefixWord ++ tailWord_7084501) baseStart_7084501 baseEnd_7084501 := by
    simpa [prefixWord, tailWord_7084501, baseEnd_7084501] using wordTrace_append hprefix tailTrace_7084501
  have hstable : (prefixWord ++ tailWord_7084501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084501).length < 2 ^ (prefixWord ++ tailWord_7084501).sum := by decide
  have hdescent : baseEnd_7084501 < baseStart_7084501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084504 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_7084504 : Nat := 118140960795 + 7084504 * 2 ^ 59
def prefixEnd_7084504 : Nat := 4983230072969 + 3 ^ 40 * 7084504 * 2
def baseEnd_7084504 : Nat := 1212585250233418359739655

theorem tailTrace_7084504 : CollatzResearch.WordTrace tailWord_7084504 prefixEnd_7084504 1212585250233418359739655 := by
  unfold tailWord_7084504
  simp only [CollatzResearch.WordTrace]
  refine ⟨129196544363029709900154283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172262059150706279866872377 129196544363029709900154283)
  ·
    refine ⟨193794816544544564850231425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129196544363029709900154283 193794816544544564850231425)
    ·
      refine ⟨145346112408408423637673569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193794816544544564850231425 145346112408408423637673569)
      ·
        refine ⟨109009584306306317728255177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145346112408408423637673569 109009584306306317728255177)
        ·
          refine ⟨81757188229729738296191383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109009584306306317728255177 81757188229729738296191383)
          ·
            refine ⟨122635782344594607444287075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81757188229729738296191383 122635782344594607444287075)
            ·
              refine ⟨183953673516891911166430613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122635782344594607444287075 183953673516891911166430613)
              ·
                refine ⟨8622828446104308335926435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183953673516891911166430613 8622828446104308335926435)
                ·
                  refine ⟨12934242669156462503889653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8622828446104308335926435 12934242669156462503889653)
                  ·
                    refine ⟨1212585250233418359739655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12934242669156462503889653 1212585250233418359739655)
                    ·
                      rfl

theorem cell23_7084504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_7084504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084504 prefixEnd_7084504 := by exact prefixLift 7084504
  have htrace : WordTrace (prefixWord ++ tailWord_7084504) baseStart_7084504 baseEnd_7084504 := by
    simpa [prefixWord, tailWord_7084504, baseEnd_7084504] using wordTrace_append hprefix tailTrace_7084504
  have hstable : (prefixWord ++ tailWord_7084504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084504).length < 2 ^ (prefixWord ++ tailWord_7084504).sum := by decide
  have hdescent : baseEnd_7084504 < baseStart_7084504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084511 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 5, 2]
def baseStart_7084511 : Nat := 118140960795 + 7084511 * 2 ^ 59
def prefixEnd_7084511 : Nat := 4983230072969 + 3 ^ 40 * 7084511 * 2
def baseEnd_7084511 : Nat := 3637759345064836551831433

theorem tailTrace_7084511 : CollatzResearch.WordTrace tailWord_7084511 prefixEnd_7084511 3637759345064836551831433 := by
  unfold tailWord_7084511
  simp only [CollatzResearch.WordTrace]
  refine ⟨258393344037034059995813387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172262229358022706663875591 258393344037034059995813387)
  ·
    refine ⟨387590016055551089993720081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258393344037034059995813387 387590016055551089993720081)
    ·
      refine ⟨290692512041663317495290061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387590016055551089993720081 290692512041663317495290061)
      ·
        refine ⟨109009692015623744060733773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290692512041663317495290061 109009692015623744060733773)
        ·
          refine ⟨40878634505858904022775165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109009692015623744060733773 40878634505858904022775165)
          ·
            refine ⟨15329487939697089008540687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40878634505858904022775165 15329487939697089008540687)
            ·
              refine ⟨22994231909545633512811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329487939697089008540687 22994231909545633512811031)
              ·
                refine ⟨34491347864318450269216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22994231909545633512811031 34491347864318450269216547)
                ·
                  refine ⟨51737021796477675403824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34491347864318450269216547 51737021796477675403824821)
                  ·
                    refine ⟨4850345793419782069108577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51737021796477675403824821 4850345793419782069108577)
                    ·
                      refine ⟨3637759345064836551831433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850345793419782069108577 3637759345064836551831433)
                      ·
                        rfl

theorem cell23_7084511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_7084511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084511 prefixEnd_7084511 := by exact prefixLift 7084511
  have htrace : WordTrace (prefixWord ++ tailWord_7084511) baseStart_7084511 baseEnd_7084511 := by
    simpa [prefixWord, tailWord_7084511, baseEnd_7084511] using wordTrace_append hprefix tailTrace_7084511
  have hstable : (prefixWord ++ tailWord_7084511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084511).length < 2 ^ (prefixWord ++ tailWord_7084511).sum := by decide
  have hdescent : baseEnd_7084511 < baseStart_7084511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084547 : List Nat := [1, 1, 1, 3, 2, 1, 4, 10]
def baseStart_7084547 : Nat := 118140960795 + 7084547 * 2 ^ 59
def prefixEnd_7084547 : Nat := 4983230072969 + 3 ^ 40 * 7084547 * 2
def baseEnd_7084547 : Nat := 134732512235866607814121

theorem tailTrace_7084547 : CollatzResearch.WordTrace tailWord_7084547 prefixEnd_7084547 134732512235866607814121 := by
  unfold tailWord_7084547
  simp only [CollatzResearch.WordTrace]
  refine ⟨258394657064903638144123895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172263104709935758762749263 258394657064903638144123895)
  ·
    refine ⟨387591985597355457216185843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258394657064903638144123895 387591985597355457216185843)
    ·
      refine ⟨581387978396033185824278765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387591985597355457216185843 581387978396033185824278765)
      ·
        refine ⟨218020491898512444684104537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581387978396033185824278765 218020491898512444684104537)
        ·
          refine ⟨163515368923884333513078403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218020491898512444684104537 163515368923884333513078403)
          ·
            refine ⟨245273053385826500269617605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163515368923884333513078403 245273053385826500269617605)
            ·
              refine ⟨45988697509842468800553301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245273053385826500269617605 45988697509842468800553301)
              ·
                refine ⟨134732512235866607814121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45988697509842468800553301 134732512235866607814121)
                ·
                  rfl

theorem cell23_7084547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 10].length) (baseStart_7084547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084547 prefixEnd_7084547 := by exact prefixLift 7084547
  have htrace : WordTrace (prefixWord ++ tailWord_7084547) baseStart_7084547 baseEnd_7084547 := by
    simpa [prefixWord, tailWord_7084547, baseEnd_7084547] using wordTrace_append hprefix tailTrace_7084547
  have hstable : (prefixWord ++ tailWord_7084547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084547).length < 2 ^ (prefixWord ++ tailWord_7084547).sum := by decide
  have hdescent : baseEnd_7084547 < baseStart_7084547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084554 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_7084554 : Nat := 118140960795 + 7084554 * 2 ^ 59
def prefixEnd_7084554 : Nat := 4983230072969 + 3 ^ 40 * 7084554 * 2
def baseEnd_7084554 : Nat := 3637781424732979883593735

theorem tailTrace_7084554 : CollatzResearch.WordTrace tailWord_7084554 prefixEnd_7084554 3637781424732979883593735 := by
  unfold tailWord_7084554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64598728093969569584907179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172263274917252185559752477 64598728093969569584907179)
  ·
    refine ⟨96898092140954354377360769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64598728093969569584907179 96898092140954354377360769)
    ·
      refine ⟨72673569105715765783020577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96898092140954354377360769 72673569105715765783020577)
      ·
        refine ⟨54505176829286824337265433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72673569105715765783020577 54505176829286824337265433)
        ·
          refine ⟨40878882621965118252949075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54505176829286824337265433 40878882621965118252949075)
          ·
            refine ⟨61318323932947677379423613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40878882621965118252949075 61318323932947677379423613)
            ·
              refine ⟨22994371474855379017283855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61318323932947677379423613 22994371474855379017283855)
              ·
                refine ⟨34491557212283068525925783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22994371474855379017283855 34491557212283068525925783)
                ·
                  refine ⟨51737335818424602788888675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34491557212283068525925783 51737335818424602788888675)
                  ·
                    refine ⟨77606003727636904183333013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51737335818424602788888675 77606003727636904183333013)
                    ·
                      refine ⟨3637781424732979883593735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77606003727636904183333013 3637781424732979883593735)
                      ·
                        rfl

theorem cell23_7084554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_7084554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084554 prefixEnd_7084554 := by exact prefixLift 7084554
  have htrace : WordTrace (prefixWord ++ tailWord_7084554) baseStart_7084554 baseEnd_7084554 := by
    simpa [prefixWord, tailWord_7084554, baseEnd_7084554] using wordTrace_append hprefix tailTrace_7084554
  have hstable : (prefixWord ++ tailWord_7084554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084554).length < 2 ^ (prefixWord ++ tailWord_7084554).sum := by decide
  have hdescent : baseEnd_7084554 < baseStart_7084554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084558 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_7084558 : Nat := 118140960795 + 7084558 * 2 ^ 59
def prefixEnd_7084558 : Nat := 4983230072969 + 3 ^ 40 * 7084558 * 2
def baseEnd_7084558 : Nat := 3637783478655597867943717

theorem tailTrace_7084558 : CollatzResearch.WordTrace tailWord_7084558 prefixEnd_7084558 3637783478655597867943717 := by
  unfold tailWord_7084558
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299382283482973377846791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172263372178575858015182885 32299382283482973377846791)
  ·
    refine ⟨48449073425224460066770187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32299382283482973377846791 48449073425224460066770187)
    ·
      refine ⟨72673610137836690100155281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48449073425224460066770187 72673610137836690100155281)
      ·
        refine ⟨54505207603377517575116461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72673610137836690100155281 54505207603377517575116461)
        ·
          refine ⟨20439452851266569090668673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54505207603377517575116461 20439452851266569090668673)
          ·
            refine ⟨15329589638449926818001505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20439452851266569090668673 15329589638449926818001505)
            ·
              refine ⟨11497192228837445113501129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15329589638449926818001505 11497192228837445113501129)
              ·
                refine ⟨8622894171628083835125847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11497192228837445113501129 8622894171628083835125847)
                ·
                  refine ⟨12934341257442125752688771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8622894171628083835125847 12934341257442125752688771)
                  ·
                    refine ⟨19401511886163188629033157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12934341257442125752688771 19401511886163188629033157)
                    ·
                      refine ⟨3637783478655597867943717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19401511886163188629033157 3637783478655597867943717)
                      ·
                        rfl

theorem cell23_7084558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_7084558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084558 prefixEnd_7084558 := by exact prefixLift 7084558
  have htrace : WordTrace (prefixWord ++ tailWord_7084558) baseStart_7084558 baseEnd_7084558 := by
    simpa [prefixWord, tailWord_7084558, baseEnd_7084558] using wordTrace_append hprefix tailTrace_7084558
  have hstable : (prefixWord ++ tailWord_7084558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084558).length < 2 ^ (prefixWord ++ tailWord_7084558).sum := by decide
  have hdescent : baseEnd_7084558 < baseStart_7084558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084612 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7084612 : Nat := 118140960795 + 7084612 * 2 ^ 59
def prefixEnd_7084612 : Nat := 4983230072969 + 3 ^ 40 * 7084612 * 2
def baseEnd_7084612 : Nat := 3637811206610940656668469

theorem tailTrace_7084612 : CollatzResearch.WordTrace tailWord_7084612 prefixEnd_7084612 3637811206610940656668469 := by
  unfold tailWord_7084612
  simp only [CollatzResearch.WordTrace]
  refine ⟨129198513904834077122620045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172264685206445436163493393 129198513904834077122620045)
  ·
    refine ⟨48449442714312778920982517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129198513904834077122620045 48449442714312778920982517)
    ·
      refine ⟨4542135254466823023842111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48449442714312778920982517 4542135254466823023842111)
      ·
        refine ⟨6813202881700234535763167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542135254466823023842111 6813202881700234535763167)
        ·
          refine ⟨10219804322550351803644751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813202881700234535763167 10219804322550351803644751)
          ·
            refine ⟨15329706483825527705467127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10219804322550351803644751 15329706483825527705467127)
            ·
              refine ⟨22994559725738291558200691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329706483825527705467127 22994559725738291558200691)
              ·
                refine ⟨34491839588607437337301037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22994559725738291558200691 34491839588607437337301037)
                ·
                  refine ⟨12934439845727789001487889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34491839588607437337301037 12934439845727789001487889)
                  ·
                    refine ⟨9700829884295841751115917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12934439845727789001487889 9700829884295841751115917)
                    ·
                      refine ⟨3637811206610940656668469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9700829884295841751115917 3637811206610940656668469)
                      ·
                        rfl

theorem cell23_7084612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7084612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084612 prefixEnd_7084612 := by exact prefixLift 7084612
  have htrace : WordTrace (prefixWord ++ tailWord_7084612) baseStart_7084612 baseEnd_7084612 := by
    simpa [prefixWord, tailWord_7084612, baseEnd_7084612] using wordTrace_append hprefix tailTrace_7084612
  have hstable : (prefixWord ++ tailWord_7084612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084612).length < 2 ^ (prefixWord ++ tailWord_7084612).sum := by decide
  have hdescent : baseEnd_7084612 < baseStart_7084612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084618 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_7084618 : Nat := 118140960795 + 7084618 * 2 ^ 59
def prefixEnd_7084618 : Nat := 4983230072969 + 3 ^ 40 * 7084618 * 2
def baseEnd_7084618 : Nat := 3637814287494867633193441

theorem tailTrace_7084618 : CollatzResearch.WordTrace tailWord_7084618 prefixEnd_7084618 3637814287494867633193441 := by
  unfold tailWord_7084618
  simp only [CollatzResearch.WordTrace]
  refine ⟨64599311661911604317489627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172264831098430944846639005 64599311661911604317489627)
  ·
    refine ⟨96898967492867406476234441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64599311661911604317489627 96898967492867406476234441)
    ·
      refine ⟨72674225619650554857175831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96898967492867406476234441 72674225619650554857175831)
      ·
        refine ⟨109011338429475832285763747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72674225619650554857175831 109011338429475832285763747)
        ·
          refine ⟨163517007644213748428645621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109011338429475832285763747 163517007644213748428645621)
          ·
            refine ⟨15329719466645038915185527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163517007644213748428645621 15329719466645038915185527)
            ·
              refine ⟨22994579199967558372778291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329719466645038915185527 22994579199967558372778291)
              ·
                refine ⟨34491868799951337559167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22994579199967558372778291 34491868799951337559167437)
                ·
                  refine ⟨12934450799981751584687789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34491868799951337559167437 12934450799981751584687789)
                  ·
                    refine ⟨4850419049993156844257921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12934450799981751584687789 4850419049993156844257921)
                    ·
                      refine ⟨3637814287494867633193441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850419049993156844257921 3637814287494867633193441)
                      ·
                        rfl

theorem cell23_7084618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_7084618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084618 prefixEnd_7084618 := by exact prefixLift 7084618
  have htrace : WordTrace (prefixWord ++ tailWord_7084618) baseStart_7084618 baseEnd_7084618 := by
    simpa [prefixWord, tailWord_7084618, baseEnd_7084618] using wordTrace_append hprefix tailTrace_7084618
  have hstable : (prefixWord ++ tailWord_7084618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084618).length < 2 ^ (prefixWord ++ tailWord_7084618).sum := by decide
  have hdescent : baseEnd_7084618 < baseStart_7084618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084665 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 2, 2, 2]
def baseStart_7084665 : Nat := 118140960795 + 7084665 * 2 ^ 59
def prefixEnd_7084665 : Nat := 4983230072969 + 3 ^ 40 * 7084665 * 2
def baseEnd_7084665 : Nat := 3637838421085628949305725

theorem tailTrace_7084665 : CollatzResearch.WordTrace tailWord_7084665 prefixEnd_7084665 3637838421085628949305725 := by
  unfold tailWord_7084665
  simp only [CollatzResearch.WordTrace]
  refine ⟨258398960878476144296919449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172265973918984096197946299 258398960878476144296919449)
  ·
    refine ⟨193799220658857108222689587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258398960878476144296919449 193799220658857108222689587)
    ·
      refine ⟨290698830988285662334034381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193799220658857108222689587 290698830988285662334034381)
      ·
        refine ⟨109012061620607123375262893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290698830988285662334034381 109012061620607123375262893)
        ·
          refine ⟨40879523107727671265723585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109012061620607123375262893 40879523107727671265723585)
          ·
            refine ⟨30659642330795753449292689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40879523107727671265723585 30659642330795753449292689)
            ·
              refine ⟨22994731748096815086969517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30659642330795753449292689 22994731748096815086969517)
              ·
                refine ⟨8623024405536305657613569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22994731748096815086969517 8623024405536305657613569)
                ·
                  refine ⟨6467268304152229243210177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8623024405536305657613569 6467268304152229243210177)
                  ·
                    refine ⟨4850451228114171932407633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6467268304152229243210177 4850451228114171932407633)
                    ·
                      refine ⟨3637838421085628949305725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850451228114171932407633 3637838421085628949305725)
                      ·
                        rfl

theorem cell23_7084665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_7084665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084665 prefixEnd_7084665 := by exact prefixLift 7084665
  have htrace : WordTrace (prefixWord ++ tailWord_7084665) baseStart_7084665 baseEnd_7084665 := by
    simpa [prefixWord, tailWord_7084665, baseEnd_7084665] using wordTrace_append hprefix tailTrace_7084665
  have hstable : (prefixWord ++ tailWord_7084665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084665).length < 2 ^ (prefixWord ++ tailWord_7084665).sum := by decide
  have hdescent : baseEnd_7084665 < baseStart_7084665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084691 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 5, 2]
def baseStart_7084691 : Nat := 118140960795 + 7084691 * 2 ^ 59
def prefixEnd_7084691 : Nat := 4983230072969 + 3 ^ 40 * 7084691 * 2
def baseEnd_7084691 : Nat := 3637851771582645847580605

theorem tailTrace_7084691 : CollatzResearch.WordTrace tailWord_7084691 prefixEnd_7084691 3637851771582645847580605 := by
  unfold tailWord_7084691
  simp only [CollatzResearch.WordTrace]
  refine ⟨258399909176381950737365927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172266606117587967158243951 258399909176381950737365927)
  ·
    refine ⟨387599863764572926106048891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258399909176381950737365927 387599863764572926106048891)
    ·
      refine ⟨581399795646859389159073337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387599863764572926106048891 581399795646859389159073337)
      ·
        refine ⟨436049846735144541869305003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581399795646859389159073337 436049846735144541869305003)
        ·
          refine ⟨654074770102716812803957505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436049846735144541869305003 654074770102716812803957505)
          ·
            refine ⟨490556077577037609602968129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654074770102716812803957505 490556077577037609602968129)
            ·
              refine ⟨367917058182778207202226097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490556077577037609602968129 367917058182778207202226097)
              ·
                refine ⟨275937793637083655401669573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367917058182778207202226097 275937793637083655401669573)
                ·
                  refine ⟨51738336306953185387813045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275937793637083655401669573 51738336306953185387813045)
                  ·
                    refine ⟨4850469028776861130107473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51738336306953185387813045 4850469028776861130107473)
                    ·
                      refine ⟨3637851771582645847580605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850469028776861130107473 3637851771582645847580605)
                      ·
                        rfl

theorem cell23_7084691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5, 2].length) (baseStart_7084691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084691 prefixEnd_7084691 := by exact prefixLift 7084691
  have htrace : WordTrace (prefixWord ++ tailWord_7084691) baseStart_7084691 baseEnd_7084691 := by
    simpa [prefixWord, tailWord_7084691, baseEnd_7084691] using wordTrace_append hprefix tailTrace_7084691
  have hstable : (prefixWord ++ tailWord_7084691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084691).length < 2 ^ (prefixWord ++ tailWord_7084691).sum := by decide
  have hdescent : baseEnd_7084691 < baseStart_7084691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084701 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7084701 : Nat := 118140960795 + 7084701 * 2 ^ 59
def prefixEnd_7084701 : Nat := 4983230072969 + 3 ^ 40 * 7084701 * 2
def baseEnd_7084701 : Nat := 1212618968796396936151853

theorem tailTrace_7084701 : CollatzResearch.WordTrace tailWord_7084701 prefixEnd_7084701 1212618968796396936151853 := by
  unfold tailWord_7084701
  simp only [CollatzResearch.WordTrace]
  refine ⟨258400273906345722445229957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172266849270897148296819971 258400273906345722445229957)
  ·
    refine ⟨48450051357439822958480617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258400273906345722445229957 48450051357439822958480617)
    ·
      refine ⟨36337538518079867218860463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48450051357439822958480617 36337538518079867218860463)
      ·
        refine ⟨54506307777119800828290695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36337538518079867218860463 54506307777119800828290695)
        ·
          refine ⟨81759461665679701242436043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54506307777119800828290695 81759461665679701242436043)
          ·
            refine ⟨122639192498519551863654065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81759461665679701242436043 122639192498519551863654065)
            ·
              refine ⟨91979394373889663897740549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122639192498519551863654065 91979394373889663897740549)
              ·
                refine ⟨17246136445104311980826353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91979394373889663897740549 17246136445104311980826353)
                ·
                  refine ⟨12934602333828233985619765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17246136445104311980826353 12934602333828233985619765)
                  ·
                    refine ⟨1212618968796396936151853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12934602333828233985619765 1212618968796396936151853)
                    ·
                      rfl

theorem cell23_7084701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7084701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084701 prefixEnd_7084701 := by exact prefixLift 7084701
  have htrace : WordTrace (prefixWord ++ tailWord_7084701) baseStart_7084701 baseEnd_7084701 := by
    simpa [prefixWord, tailWord_7084701, baseEnd_7084701] using wordTrace_append hprefix tailTrace_7084701
  have hstable : (prefixWord ++ tailWord_7084701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084701).length < 2 ^ (prefixWord ++ tailWord_7084701).sum := by decide
  have hdescent : baseEnd_7084701 < baseStart_7084701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084718 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7084718 : Nat := 118140960795 + 7084718 * 2 ^ 59
def prefixEnd_7084718 : Nat := 4983230072969 + 3 ^ 40 * 7084718 * 2
def baseEnd_7084718 : Nat := 1212621878520105747314327

theorem tailTrace_7084718 : CollatzResearch.WordTrace tailWord_7084718 prefixEnd_7084718 1212621878520105747314327 := by
  unfold tailWord_7084718
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300111743410516793574851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172267262631522756232399205 32300111743410516793574851)
  ·
    refine ⟨48450167615115775190362277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32300111743410516793574851 48450167615115775190362277)
    ·
      refine ⟨9084406427834207848192927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48450167615115775190362277 9084406427834207848192927)
      ·
        refine ⟨13626609641751311772289391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084406427834207848192927 13626609641751311772289391)
        ·
          refine ⟨20439914462626967658434087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13626609641751311772289391 20439914462626967658434087)
          ·
            refine ⟨30659871693940451487651131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20439914462626967658434087 30659871693940451487651131)
            ·
              refine ⟨45989807540910677231476697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30659871693940451487651131 45989807540910677231476697)
              ·
                refine ⟨34492355655683007923607523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45989807540910677231476697 34492355655683007923607523)
                ·
                  refine ⟨51738533483524511885411285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34492355655683007923607523 51738533483524511885411285)
                  ·
                    refine ⟨1212621878520105747314327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51738533483524511885411285 1212621878520105747314327)
                    ·
                      rfl

theorem cell23_7084718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7084718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084718 prefixEnd_7084718 := by exact prefixLift 7084718
  have htrace : WordTrace (prefixWord ++ tailWord_7084718) baseStart_7084718 baseEnd_7084718 := by
    simpa [prefixWord, tailWord_7084718, baseEnd_7084718] using wordTrace_append hprefix tailTrace_7084718
  have hstable : (prefixWord ++ tailWord_7084718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084718).length < 2 ^ (prefixWord ++ tailWord_7084718).sum := by decide
  have hdescent : baseEnd_7084718 < baseStart_7084718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084761 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 6]
def baseStart_7084761 : Nat := 118140960795 + 7084761 * 2 ^ 59
def prefixEnd_7084761 : Nat := 4983230072969 + 3 ^ 40 * 7084761 * 2
def baseEnd_7084761 : Nat := 404209746136495619300587

theorem tailTrace_7084761 : CollatzResearch.WordTrace tailWord_7084761 prefixEnd_7084761 404209746136495619300587 := by
  unfold tailWord_7084761
  simp only [CollatzResearch.WordTrace]
  refine ⟨258402462286128352692414137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172268308190752235128276091 258402462286128352692414137)
  ·
    refine ⟨193801846714596264519310603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258402462286128352692414137 193801846714596264519310603)
    ·
      refine ⟨290702770071894396778965905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193801846714596264519310603 290702770071894396778965905)
      ·
        refine ⟨218027077553920797584224429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290702770071894396778965905 218027077553920797584224429)
        ·
          refine ⟨81760154082720299094084161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218027077553920797584224429 81760154082720299094084161)
          ·
            refine ⟨61320115562040224320563121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81760154082720299094084161 61320115562040224320563121)
            ·
              refine ⟨45990086671530168240422341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61320115562040224320563121 45990086671530168240422341)
              ·
                refine ⟨8623141250911906545079189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45990086671530168240422341 8623141250911906545079189)
                ·
                  refine ⟨404209746136495619300587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8623141250911906545079189 404209746136495619300587)
                  ·
                    rfl

theorem cell23_7084761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_7084761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084761 prefixEnd_7084761 := by exact prefixLift 7084761
  have htrace : WordTrace (prefixWord ++ tailWord_7084761) baseStart_7084761 baseEnd_7084761 := by
    simpa [prefixWord, tailWord_7084761, baseEnd_7084761] using wordTrace_append hprefix tailTrace_7084761
  have hstable : (prefixWord ++ tailWord_7084761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084761).length < 2 ^ (prefixWord ++ tailWord_7084761).sum := by decide
  have hdescent : baseEnd_7084761 < baseStart_7084761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084789 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7084789 : Nat := 118140960795 + 7084789 * 2 ^ 59
def prefixEnd_7084789 : Nat := 4983230072969 + 3 ^ 40 * 7084789 * 2
def baseEnd_7084789 : Nat := 3637902092686786464155155

theorem tailTrace_7084789 : CollatzResearch.WordTrace tailWord_7084789 prefixEnd_7084789 3637902092686786464155155 := by
  unfold tailWord_7084789
  simp only [CollatzResearch.WordTrace]
  refine ⟨258403483530026913474433421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172268989020017942316288947 258403483530026913474433421)
  ·
    refine ⟨96901306323760092552912533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258403483530026913474433421 96901306323760092552912533)
    ·
      refine ⟨4542248733926254338417775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96901306323760092552912533 4542248733926254338417775)
      ·
        refine ⟨6813373100889381507626663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542248733926254338417775 6813373100889381507626663)
        ·
          refine ⟨10220059651334072261439995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813373100889381507626663 10220059651334072261439995)
          ·
            refine ⟨15330089477001108392159993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220059651334072261439995 15330089477001108392159993)
            ·
              refine ⟨11497567107750831294119995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15330089477001108392159993 11497567107750831294119995)
              ·
                refine ⟨17246350661626246941179993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497567107750831294119995 17246350661626246941179993)
                ·
                  refine ⟨12934762996219685205884995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17246350661626246941179993 12934762996219685205884995)
                  ·
                    refine ⟨19402144494329527808827493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12934762996219685205884995 19402144494329527808827493)
                    ·
                      refine ⟨3637902092686786464155155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19402144494329527808827493 3637902092686786464155155)
                      ·
                        rfl

theorem cell23_7084789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7084789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084789 prefixEnd_7084789 := by exact prefixLift 7084789
  have htrace : WordTrace (prefixWord ++ tailWord_7084789) baseStart_7084789 baseEnd_7084789 := by
    simpa [prefixWord, tailWord_7084789, baseEnd_7084789] using wordTrace_append hprefix tailTrace_7084789
  have hstable : (prefixWord ++ tailWord_7084789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084789).length < 2 ^ (prefixWord ++ tailWord_7084789).sum := by decide
  have hdescent : baseEnd_7084789 < baseStart_7084789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084821 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_7084821 : Nat := 118140960795 + 7084821 * 2 ^ 59
def prefixEnd_7084821 : Nat := 4983230072969 + 3 ^ 40 * 7084821 * 2
def baseEnd_7084821 : Nat := 1212639508022576779651669

theorem tailTrace_7084821 : CollatzResearch.WordTrace tailWord_7084821 prefixEnd_7084821 1212639508022576779651669 := by
  unfold tailWord_7084821
  simp only [CollatzResearch.WordTrace]
  refine ⟨258404650665910982939598317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172269767110607321959732211 258404650665910982939598317)
  ·
    refine ⟨96901743999716618602349369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258404650665910982939598317 96901743999716618602349369)
    ·
      refine ⟨72676307999787463951762027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96901743999716618602349369 72676307999787463951762027)
      ·
        refine ⟨109014461999681195927643041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72676307999787463951762027 109014461999681195927643041)
        ·
          refine ⟨81760846499760896945732281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109014461999681195927643041 81760846499760896945732281)
          ·
            refine ⟨61320634874820672709299211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81760846499760896945732281 61320634874820672709299211)
            ·
              refine ⟨91980952312231009063948817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61320634874820672709299211 91980952312231009063948817)
              ·
                refine ⟨68985714234173256797961613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91980952312231009063948817 68985714234173256797961613)
                ·
                  refine ⟨25869642837814971299235605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68985714234173256797961613 25869642837814971299235605)
                  ·
                    refine ⟨1212639508022576779651669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25869642837814971299235605 1212639508022576779651669)
                    ·
                      rfl

theorem cell23_7084821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_7084821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084821 prefixEnd_7084821 := by exact prefixLift 7084821
  have htrace : WordTrace (prefixWord ++ tailWord_7084821) baseStart_7084821 baseEnd_7084821 := by
    simpa [prefixWord, tailWord_7084821, baseEnd_7084821] using wordTrace_append hprefix tailTrace_7084821
  have hstable : (prefixWord ++ tailWord_7084821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084821).length < 2 ^ (prefixWord ++ tailWord_7084821).sum := by decide
  have hdescent : baseEnd_7084821 < baseStart_7084821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084828 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7084828 : Nat := 118140960795 + 7084828 * 2 ^ 59
def prefixEnd_7084828 : Nat := 4983230072969 + 3 ^ 40 * 7084828 * 2
def baseEnd_7084828 : Nat := 3637922118432311811567475

theorem tailTrace_7084828 : CollatzResearch.WordTrace tailWord_7084828 prefixEnd_7084828 3637922118432311811567475 := by
  unfold tailWord_7084828
  simp only [CollatzResearch.WordTrace]
  refine ⟨129202452988442811567551569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172269937317923748756735425 129202452988442811567551569)
  ·
    refine ⟨96901839741332108675663677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129202452988442811567551569 96901839741332108675663677)
    ·
      refine ⟨36338189902999540753373879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96901839741332108675663677 36338189902999540753373879)
      ·
        refine ⟨54507284854499311130060819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36338189902999540753373879 54507284854499311130060819)
        ·
          refine ⟨81760927281748966695091229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54507284854499311130060819 81760927281748966695091229)
          ·
            refine ⟨30660347730655862510659211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81760927281748966695091229 30660347730655862510659211)
            ·
              refine ⟨45990521595983793765988817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30660347730655862510659211 45990521595983793765988817)
              ·
                refine ⟨34492891196987845324491613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45990521595983793765988817 34492891196987845324491613)
                ·
                  refine ⟨12934834198870441996684355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34492891196987845324491613 12934834198870441996684355)
                  ·
                    refine ⟨19402251298305662995026533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12934834198870441996684355 19402251298305662995026533)
                    ·
                      refine ⟨3637922118432311811567475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19402251298305662995026533 3637922118432311811567475)
                      ·
                        rfl

theorem cell23_7084828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7084828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084828 prefixEnd_7084828 := by exact prefixLift 7084828
  have htrace : WordTrace (prefixWord ++ tailWord_7084828) baseStart_7084828 baseEnd_7084828 := by
    simpa [prefixWord, tailWord_7084828, baseEnd_7084828] using wordTrace_append hprefix tailTrace_7084828
  have hstable : (prefixWord ++ tailWord_7084828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084828).length < 2 ^ (prefixWord ++ tailWord_7084828).sum := by decide
  have hdescent : baseEnd_7084828 < baseStart_7084828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_7084841 : Nat := 118140960795 + 7084841 * 2 ^ 59
def prefixEnd_7084841 : Nat := 4983230072969 + 3 ^ 40 * 7084841 * 2
def baseEnd_7084841 : Nat := 3637928793680820260704915

theorem tailTrace_7084841 : CollatzResearch.WordTrace tailWord_7084841 prefixEnd_7084841 3637928793680820260704915 := by
  unfold tailWord_7084841
  simp only [CollatzResearch.WordTrace]
  refine ⟨258405380125838526355326377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172270253417225684236884251 258405380125838526355326377)
  ·
    refine ⟨193804035094378894766494783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258405380125838526355326377 193804035094378894766494783)
    ·
      refine ⟨290706052641568342149742175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193804035094378894766494783 290706052641568342149742175)
      ·
        refine ⟨436059078962352513224613263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290706052641568342149742175 436059078962352513224613263)
        ·
          refine ⟨654088618443528769836919895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436059078962352513224613263 654088618443528769836919895)
          ·
            refine ⟨981132927665293154755379843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654088618443528769836919895 981132927665293154755379843)
            ·
              refine ⟨1471699391497939732133069765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981132927665293154755379843 1471699391497939732133069765)
              ·
                refine ⟨275943635905863699774950581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1471699391497939732133069765 275943635905863699774950581)
                ·
                  refine ⟨25869715866174721853901617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275943635905863699774950581 25869715866174721853901617)
                  ·
                    refine ⟨19402286899631041390426213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25869715866174721853901617 19402286899631041390426213)
                    ·
                      refine ⟨3637928793680820260704915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19402286899631041390426213 3637928793680820260704915)
                      ·
                        rfl

theorem cell23_7084841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_7084841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084841 prefixEnd_7084841 := by exact prefixLift 7084841
  have htrace : WordTrace (prefixWord ++ tailWord_7084841) baseStart_7084841 baseEnd_7084841 := by
    simpa [prefixWord, tailWord_7084841, baseEnd_7084841] using wordTrace_append hprefix tailTrace_7084841
  have hstable : (prefixWord ++ tailWord_7084841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084841).length < 2 ^ (prefixWord ++ tailWord_7084841).sum := by decide
  have hdescent : baseEnd_7084841 < baseStart_7084841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084862 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_7084862 : Nat := 118140960795 + 7084862 * 2 ^ 59
def prefixEnd_7084862 : Nat := 4983230072969 + 3 ^ 40 * 7084862 * 2
def baseEnd_7084862 : Nat := 3637939576774564678542319

theorem tailTrace_7084862 : CollatzResearch.WordTrace tailWord_7084862 prefixEnd_7084862 3637939576774564678542319 := by
  unfold tailWord_7084862
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300768257345305867730105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172270764039174964627893893 32300768257345305867730105)
  ·
    refine ⟨24225576193008979400797579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32300768257345305867730105 24225576193008979400797579)
    ·
      refine ⟨36338364289513469101196369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24225576193008979400797579 36338364289513469101196369)
      ·
        refine ⟨27253773217135101825897277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36338364289513469101196369 27253773217135101825897277)
        ·
          refine ⟨10220164956425663184711479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27253773217135101825897277 10220164956425663184711479)
          ·
            refine ⟨15330247434638494777067219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220164956425663184711479 15330247434638494777067219)
            ·
              refine ⟨22995371151957742165600829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15330247434638494777067219 22995371151957742165600829)
              ·
                refine ⟨8623264181984153312100311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22995371151957742165600829 8623264181984153312100311)
                ·
                  refine ⟨12934896272976229968150467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623264181984153312100311 12934896272976229968150467)
                  ·
                    refine ⟨19402344409464344952225701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12934896272976229968150467 19402344409464344952225701)
                    ·
                      refine ⟨3637939576774564678542319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19402344409464344952225701 3637939576774564678542319)
                      ·
                        rfl

theorem cell23_7084862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_7084862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084862 prefixEnd_7084862 := by exact prefixLift 7084862
  have htrace : WordTrace (prefixWord ++ tailWord_7084862) baseStart_7084862 baseEnd_7084862 := by
    simpa [prefixWord, tailWord_7084862, baseEnd_7084862] using wordTrace_append hprefix tailTrace_7084862
  have hstable : (prefixWord ++ tailWord_7084862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084862).length < 2 ^ (prefixWord ++ tailWord_7084862).sum := by decide
  have hdescent : baseEnd_7084862 < baseStart_7084862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084871 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_7084871 : Nat := 118140960795 + 7084871 * 2 ^ 59
def prefixEnd_7084871 : Nat := 4983230072969 + 3 ^ 40 * 7084871 * 2
def baseEnd_7084871 : Nat := 3637944198100455143329777

theorem tailTrace_7084871 : CollatzResearch.WordTrace tailWord_7084871 prefixEnd_7084871 3637944198100455143329777 := by
  unfold tailWord_7084871
  simp only [CollatzResearch.WordTrace]
  refine ⟨258406474315729841478918467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172270982877153227652612311 258406474315729841478918467)
  ·
    refine ⟨387609711473594762218377701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258406474315729841478918467 387609711473594762218377701)
    ·
      refine ⟨72676820901299017915945819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387609711473594762218377701 72676820901299017915945819)
      ·
        refine ⟨109015231351948526873918729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72676820901299017915945819 109015231351948526873918729)
        ·
          refine ⟨81761423513961395155439047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109015231351948526873918729 81761423513961395155439047)
          ·
            refine ⟨122642135270942092733158571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81761423513961395155439047 122642135270942092733158571)
            ·
              refine ⟨183963202906413139099737857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122642135270942092733158571 183963202906413139099737857)
              ·
                refine ⟨137972402179809854324803393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183963202906413139099737857 137972402179809854324803393)
                ·
                  refine ⟨103479301634857390743602545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137972402179809854324803393 103479301634857390743602545)
                  ·
                    refine ⟨77609476226143043057701909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103479301634857390743602545 77609476226143043057701909)
                    ·
                      refine ⟨3637944198100455143329777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77609476226143043057701909 3637944198100455143329777)
                      ·
                        rfl

theorem cell23_7084871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_7084871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084871 prefixEnd_7084871 := by exact prefixLift 7084871
  have htrace : WordTrace (prefixWord ++ tailWord_7084871) baseStart_7084871 baseEnd_7084871 := by
    simpa [prefixWord, tailWord_7084871, baseEnd_7084871] using wordTrace_append hprefix tailTrace_7084871
  have hstable : (prefixWord ++ tailWord_7084871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084871).length < 2 ^ (prefixWord ++ tailWord_7084871).sum := by decide
  have hdescent : baseEnd_7084871 < baseStart_7084871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084878 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_7084878 : Nat := 118140960795 + 7084878 * 2 ^ 59
def prefixEnd_7084878 : Nat := 4983230072969 + 3 ^ 40 * 7084878 * 2
def baseEnd_7084878 : Nat := 3637947792465036615942245

theorem tailTrace_7084878 : CollatzResearch.WordTrace tailWord_7084878 prefixEnd_7084878 3637947792465036615942245 := by
  unfold tailWord_7084878
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300841203338060209302911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172271153084469654449615525 32300841203338060209302911)
  ·
    refine ⟨48451261805007090313954367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32300841203338060209302911 48451261805007090313954367)
    ·
      refine ⟨72676892707510635470931551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48451261805007090313954367 72676892707510635470931551)
      ·
        refine ⟨109015339061265953206397327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72676892707510635470931551 109015339061265953206397327)
        ·
          refine ⟨163523008591898929809595991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109015339061265953206397327 163523008591898929809595991)
          ·
            refine ⟨245284512887848394714393987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163523008591898929809595991 245284512887848394714393987)
            ·
              refine ⟨367926769331772592071590981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245284512887848394714393987 367926769331772592071590981)
              ·
                refine ⟨68986269249707361013423309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367926769331772592071590981 68986269249707361013423309)
                ·
                  refine ⟨25869850968640260380033741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68986269249707361013423309 25869850968640260380033741)
                  ·
                    refine ⟨9701194113240097642512653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25869850968640260380033741 9701194113240097642512653)
                    ·
                      refine ⟨3637947792465036615942245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9701194113240097642512653 3637947792465036615942245)
                      ·
                        rfl

theorem cell23_7084878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_7084878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084878 prefixEnd_7084878 := by exact prefixLift 7084878
  have htrace : WordTrace (prefixWord ++ tailWord_7084878) baseStart_7084878 baseEnd_7084878 := by
    simpa [prefixWord, tailWord_7084878, baseEnd_7084878] using wordTrace_append hprefix tailTrace_7084878
  have hstable : (prefixWord ++ tailWord_7084878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084878).length < 2 ^ (prefixWord ++ tailWord_7084878).sum := by decide
  have hdescent : baseEnd_7084878 < baseStart_7084878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084892 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7084892 : Nat := 118140960795 + 7084892 * 2 ^ 59
def prefixEnd_7084892 : Nat := 4983230072969 + 3 ^ 40 * 7084892 * 2
def baseEnd_7084892 : Nat := 3637954981194199561167181

theorem tailTrace_7084892 : CollatzResearch.WordTrace tailWord_7084892 prefixEnd_7084892 3637954981194199561167181 := by
  unfold tailWord_7084892
  simp only [CollatzResearch.WordTrace]
  refine ⟨129203620124326881032716465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172271493499102508043621953 129203620124326881032716465)
  ·
    refine ⟨96902715093245160774537349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129203620124326881032716465 96902715093245160774537349)
    ·
      refine ⟨18169259079983467645225753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96902715093245160774537349 18169259079983467645225753)
      ·
        refine ⟨13626944309987600733919315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18169259079983467645225753 13626944309987600733919315)
        ·
          refine ⟨20440416464981401100878973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13626944309987600733919315 20440416464981401100878973)
          ·
            refine ⟨7665156174368025412829615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20440416464981401100878973 7665156174368025412829615)
            ·
              refine ⟨11497734261552038119244423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665156174368025412829615 11497734261552038119244423)
              ·
                refine ⟨17246601392328057178866635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497734261552038119244423 17246601392328057178866635)
                ·
                  refine ⟨25869902088492085768299953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17246601392328057178866635 25869902088492085768299953)
                  ·
                    refine ⟨19402426566369064326224965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25869902088492085768299953 19402426566369064326224965)
                    ·
                      refine ⟨3637954981194199561167181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19402426566369064326224965 3637954981194199561167181)
                      ·
                        rfl

theorem cell23_7084892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7084892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084892 prefixEnd_7084892 := by exact prefixLift 7084892
  have htrace : WordTrace (prefixWord ++ tailWord_7084892) baseStart_7084892 baseEnd_7084892 := by
    simpa [prefixWord, tailWord_7084892, baseEnd_7084892] using wordTrace_append hprefix tailTrace_7084892
  have hstable : (prefixWord ++ tailWord_7084892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084892).length < 2 ^ (prefixWord ++ tailWord_7084892).sum := by decide
  have hdescent : baseEnd_7084892 < baseStart_7084892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084911 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 8]
def baseStart_7084911 : Nat := 118140960795 + 7084911 * 2 ^ 59
def prefixEnd_7084911 : Nat := 4983230072969 + 3 ^ 40 * 7084911 * 2
def baseEnd_7084911 : Nat := 1212654912442211662276531

theorem tailTrace_7084911 : CollatzResearch.WordTrace tailWord_7084911 prefixEnd_7084911 1212654912442211662276531 := by
  unfold tailWord_7084911
  simp only [CollatzResearch.WordTrace]
  refine ⟨258407933235584928310374587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172271955490389952206916391 258407933235584928310374587)
  ·
    refine ⟨387611899853377392465561881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258407933235584928310374587 387611899853377392465561881)
    ·
      refine ⟨290708924890033044349171411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387611899853377392465561881 290708924890033044349171411)
      ·
        refine ⟨436063387335049566523757117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290708924890033044349171411 436063387335049566523757117)
        ·
          refine ⟨163523770250643587446408919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436063387335049566523757117 163523770250643587446408919)
          ·
            refine ⟨245285655375965381169613379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163523770250643587446408919 245285655375965381169613379)
            ·
              refine ⟨367928483063948071754420069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245285655375965381169613379 367928483063948071754420069)
              ·
                refine ⟨68986590574490263453953763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367928483063948071754420069 68986590574490263453953763)
                ·
                  refine ⟨103479885861735395180930645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68986590574490263453953763 103479885861735395180930645)
                  ·
                    refine ⟨1212654912442211662276531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103479885861735395180930645 1212654912442211662276531)
                    ·
                      rfl

theorem cell23_7084911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_7084911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084911 prefixEnd_7084911 := by exact prefixLift 7084911
  have htrace : WordTrace (prefixWord ++ tailWord_7084911) baseStart_7084911 baseEnd_7084911 := by
    simpa [prefixWord, tailWord_7084911, baseEnd_7084911] using wordTrace_append hprefix tailTrace_7084911
  have hstable : (prefixWord ++ tailWord_7084911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084911).length < 2 ^ (prefixWord ++ tailWord_7084911).sum := by decide
  have hdescent : baseEnd_7084911 < baseStart_7084911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084930 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7084930 : Nat := 118140960795 + 7084930 * 2 ^ 59
def prefixEnd_7084930 : Nat := 4983230072969 + 3 ^ 40 * 7084930 * 2
def baseEnd_7084930 : Nat := 3637974493459070412492007

theorem tailTrace_7084930 : CollatzResearch.WordTrace tailWord_7084930 prefixEnd_7084930 3637974493459070412492007 := by
  unfold tailWord_7084930
  simp only [CollatzResearch.WordTrace]
  refine ⟨64602156555629023638829061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172272417481677396370210829 64602156555629023638829061)
  ·
    refine ⟨12112904354180441932280449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64602156555629023638829061 12112904354180441932280449)
    ·
      refine ⟨9084678265635331449210337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12112904354180441932280449 9084678265635331449210337)
      ·
        refine ⟨6813508699226498586907753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9084678265635331449210337 6813508699226498586907753)
        ·
          refine ⟨5110131524419873940180815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813508699226498586907753 5110131524419873940180815)
          ·
            refine ⟨7665197286629810910271223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110131524419873940180815 7665197286629810910271223)
            ·
              refine ⟨11497795929944716365406835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665197286629810910271223 11497795929944716365406835)
              ·
                refine ⟨17246693894917074548110253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497795929944716365406835 17246693894917074548110253)
                ·
                  refine ⟨6467510210593902955541345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17246693894917074548110253 6467510210593902955541345)
                  ·
                    refine ⟨4850632657945427216656009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6467510210593902955541345 4850632657945427216656009)
                    ·
                      refine ⟨3637974493459070412492007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850632657945427216656009 3637974493459070412492007)
                      ·
                        rfl

theorem cell23_7084930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7084930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084930 prefixEnd_7084930 := by exact prefixLift 7084930
  have htrace : WordTrace (prefixWord ++ tailWord_7084930) baseStart_7084930 baseEnd_7084930 := by
    simpa [prefixWord, tailWord_7084930, baseEnd_7084930] using wordTrace_append hprefix tailTrace_7084930
  have hstable : (prefixWord ++ tailWord_7084930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084930).length < 2 ^ (prefixWord ++ tailWord_7084930).sum := by decide
  have hdescent : baseEnd_7084930 < baseStart_7084930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084956 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7084956 : Nat := 118140960795 + 7084956 * 2 ^ 59
def prefixEnd_7084956 : Nat := 4983230072969 + 3 ^ 40 * 7084956 * 2
def baseEnd_7084956 : Nat := 3637987843956087310766887

theorem tailTrace_7084956 : CollatzResearch.WordTrace tailWord_7084956 prefixEnd_7084956 3637987843956087310766887 := by
  unfold tailWord_7084956
  simp only [CollatzResearch.WordTrace]
  refine ⟨129204787260210950497881361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172273049680281267330508481 129204787260210950497881361)
  ·
    refine ⟨96903590445158212873411021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129204787260210950497881361 96903590445158212873411021)
    ·
      refine ⟨36338846416934329827529133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96903590445158212873411021 36338846416934329827529133)
      ·
        refine ⟨13627067406350373685323425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36338846416934329827529133 13627067406350373685323425)
        ·
          refine ⟨10220300554762780263992569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13627067406350373685323425 10220300554762780263992569)
          ·
            refine ⟨7665225416072085197994427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10220300554762780263992569 7665225416072085197994427)
            ·
              refine ⟨11497838124108127796991641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665225416072085197994427 11497838124108127796991641)
              ·
                refine ⟨8623378593081095847743731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11497838124108127796991641 8623378593081095847743731)
                ·
                  refine ⟨12935067889621643771615597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623378593081095847743731 12935067889621643771615597)
                  ·
                    refine ⟨4850650458608116414355849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12935067889621643771615597 4850650458608116414355849)
                    ·
                      refine ⟨3637987843956087310766887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850650458608116414355849 3637987843956087310766887)
                      ·
                        rfl

theorem cell23_7084956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7084956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084956 prefixEnd_7084956 := by exact prefixLift 7084956
  have htrace : WordTrace (prefixWord ++ tailWord_7084956) baseStart_7084956 baseEnd_7084956 := by
    simpa [prefixWord, tailWord_7084956, baseEnd_7084956] using wordTrace_append hprefix tailTrace_7084956
  have hstable : (prefixWord ++ tailWord_7084956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084956).length < 2 ^ (prefixWord ++ tailWord_7084956).sum := by decide
  have hdescent : baseEnd_7084956 < baseStart_7084956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084973 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7084973 : Nat := 118140960795 + 7084973 * 2 ^ 59
def prefixEnd_7084973 : Nat := 4983230072969 + 3 ^ 40 * 7084973 * 2
def baseEnd_7084973 : Nat := 3637996573127213744254309

theorem tailTrace_7084973 : CollatzResearch.WordTrace tailWord_7084973 prefixEnd_7084973 3637996573127213744254309 := by
  unfold tailWord_7084973
  simp only [CollatzResearch.WordTrace]
  refine ⟨258410194561360312899131573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172273463040906875266087715 258410194561360312899131573)
  ·
    refine ⟨24225955740127529334293585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258410194561360312899131573 24225955740127529334293585)
    ·
      refine ⟨18169466805095647000720189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24225955740127529334293585 18169466805095647000720189)
      ·
        refine ⟨6813550051910867625270071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18169466805095647000720189 6813550051910867625270071)
        ·
          refine ⟨10220325077866301437905107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813550051910867625270071 10220325077866301437905107)
          ·
            refine ⟨15330487616799452156857661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220325077866301437905107 15330487616799452156857661)
            ·
              refine ⟨5748932856299794558821623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15330487616799452156857661 5748932856299794558821623)
              ·
                refine ⟨8623399284449691838232435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748932856299794558821623 8623399284449691838232435)
                ·
                  refine ⟨12935098926674537757348653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623399284449691838232435 12935098926674537757348653)
                  ·
                    refine ⟨4850662097502951659005745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12935098926674537757348653 4850662097502951659005745)
                    ·
                      refine ⟨3637996573127213744254309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850662097502951659005745 3637996573127213744254309)
                      ·
                        rfl

theorem cell23_7084973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7084973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084973 prefixEnd_7084973 := by exact prefixLift 7084973
  have htrace : WordTrace (prefixWord ++ tailWord_7084973) baseStart_7084973 baseEnd_7084973 := by
    simpa [prefixWord, tailWord_7084973, baseEnd_7084973] using wordTrace_append hprefix tailTrace_7084973
  have hstable : (prefixWord ++ tailWord_7084973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084973).length < 2 ^ (prefixWord ++ tailWord_7084973).sum := by decide
  have hdescent : baseEnd_7084973 < baseStart_7084973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7084992 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 5]
def baseStart_7084992 : Nat := 118140960795 + 7084992 * 2 ^ 59
def prefixEnd_7084992 : Nat := 4983230072969 + 3 ^ 40 * 7084992 * 2
def baseEnd_7084992 : Nat := 404222925473294352212969

theorem tailTrace_7084992 : CollatzResearch.WordTrace tailWord_7084992 prefixEnd_7084992 404222925473294352212969 := by
  unfold tailWord_7084992
  simp only [CollatzResearch.WordTrace]
  refine ⟨129205443774145739572036615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172273925032194319429382153 129205443774145739572036615)
  ·
    refine ⟨193808165661218609358054923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129205443774145739572036615 193808165661218609358054923)
    ·
      refine ⟨290712248491827914037082385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193808165661218609358054923 290712248491827914037082385)
      ·
        refine ⟨218034186368870935527811789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290712248491827914037082385 218034186368870935527811789)
        ·
          refine ⟨81762819888326600822929421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218034186368870935527811789 81762819888326600822929421)
          ·
            refine ⟨30661057458122475308598533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81762819888326600822929421 30661057458122475308598533)
            ·
              refine ⟨5748948273397964120362225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30661057458122475308598533 5748948273397964120362225)
              ·
                refine ⟨4311711205048473090271669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748948273397964120362225 4311711205048473090271669)
                ·
                  refine ⟨404222925473294352212969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4311711205048473090271669 404222925473294352212969)
                  ·
                    rfl

theorem cell23_7084992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 5].length) (baseStart_7084992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7084992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7084992 prefixEnd_7084992 := by exact prefixLift 7084992
  have htrace : WordTrace (prefixWord ++ tailWord_7084992) baseStart_7084992 baseEnd_7084992 := by
    simpa [prefixWord, tailWord_7084992, baseEnd_7084992] using wordTrace_append hprefix tailTrace_7084992
  have hstable : (prefixWord ++ tailWord_7084992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7084992).length < 2 ^ (prefixWord ++ tailWord_7084992).sum := by decide
  have hdescent : baseEnd_7084992 < baseStart_7084992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7084992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085008 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_7085008 : Nat := 118140960795 + 7085008 * 2 ^ 59
def prefixEnd_7085008 : Nat := 4983230072969 + 3 ^ 40 * 7085008 * 2
def baseEnd_7085008 : Nat := 3638014544950121107316647

theorem tailTrace_7085008 : CollatzResearch.WordTrace tailWord_7085008 prefixEnd_7085008 3638014544950121107316647 := by
  unfold tailWord_7085008
  simp only [CollatzResearch.WordTrace]
  refine ⟨129205735558116756938327839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172274314077489009251103785 129205735558116756938327839)
  ·
    refine ⟨193808603337175135407491759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129205735558116756938327839 193808603337175135407491759)
    ·
      refine ⟨290712905005762703111237639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193808603337175135407491759 290712905005762703111237639)
      ·
        refine ⟨436069357508644054666856459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290712905005762703111237639 436069357508644054666856459)
        ·
          refine ⟨654104036262966082000284689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436069357508644054666856459 654104036262966082000284689)
          ·
            refine ⟨490578027197224561500213517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654104036262966082000284689 490578027197224561500213517)
            ·
              refine ⟨183966760198959210562580069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490578027197224561500213517 183966760198959210562580069)
              ·
                refine ⟨34493767537304851980483763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183966760198959210562580069 34493767537304851980483763)
                ·
                  refine ⟨51740651305957277970725645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34493767537304851980483763 51740651305957277970725645)
                  ·
                    refine ⟨19402744239733979239022117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51740651305957277970725645 19402744239733979239022117)
                    ·
                      refine ⟨3638014544950121107316647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19402744239733979239022117 3638014544950121107316647)
                      ·
                        rfl

theorem cell23_7085008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_7085008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085008 prefixEnd_7085008 := by exact prefixLift 7085008
  have htrace : WordTrace (prefixWord ++ tailWord_7085008) baseStart_7085008 baseEnd_7085008 := by
    simpa [prefixWord, tailWord_7085008, baseEnd_7085008] using wordTrace_append hprefix tailTrace_7085008
  have hstable : (prefixWord ++ tailWord_7085008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085008).length < 2 ^ (prefixWord ++ tailWord_7085008).sum := by decide
  have hdescent : baseEnd_7085008 < baseStart_7085008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085025 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_7085025 : Nat := 118140960795 + 7085025 * 2 ^ 59
def prefixEnd_7085025 : Nat := 4983230072969 + 3 ^ 40 * 7085025 * 2
def baseEnd_7085025 : Nat := 3638023274121247540804069

theorem tailTrace_7085025 : CollatzResearch.WordTrace tailWord_7085025 prefixEnd_7085025 3638023274121247540804069 := by
  unfold tailWord_7085025
  simp only [CollatzResearch.WordTrace]
  refine ⟨258412091157171925780024529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172274727438114617186683019 258412091157171925780024529)
  ·
    refine ⟨193809068367878944335018397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258412091157171925780024529 193809068367878944335018397)
    ·
      refine ⟨72678400637954604125631899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193809068367878944335018397 72678400637954604125631899)
      ·
        refine ⟨109017600956931906188447849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72678400637954604125631899 109017600956931906188447849)
        ·
          refine ⟨81763200717698929641335887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109017600956931906188447849 81763200717698929641335887)
          ·
            refine ⟨122644801076548394462003831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81763200717698929641335887 122644801076548394462003831)
            ·
              refine ⟨183967201614822591693005747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122644801076548394462003831 183967201614822591693005747)
              ·
                refine ⟨275950802422233887539508621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183967201614822591693005747 275950802422233887539508621)
                ·
                  refine ⟨103481550908337707827315733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275950802422233887539508621 103481550908337707827315733)
                  ·
                    refine ⟨4850697698828330054405425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103481550908337707827315733 4850697698828330054405425)
                    ·
                      refine ⟨3638023274121247540804069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850697698828330054405425 3638023274121247540804069)
                      ·
                        rfl

theorem cell23_7085025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_7085025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085025 prefixEnd_7085025 := by exact prefixLift 7085025
  have htrace : WordTrace (prefixWord ++ tailWord_7085025) baseStart_7085025 baseEnd_7085025 := by
    simpa [prefixWord, tailWord_7085025, baseEnd_7085025] using wordTrace_append hprefix tailTrace_7085025
  have hstable : (prefixWord ++ tailWord_7085025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085025).length < 2 ^ (prefixWord ++ tailWord_7085025).sum := by decide
  have hdescent : baseEnd_7085025 < baseStart_7085025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085028 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_7085028 : Nat := 118140960795 + 7085028 * 2 ^ 59
def prefixEnd_7085028 : Nat := 4983230072969 + 3 ^ 40 * 7085028 * 2
def baseEnd_7085028 : Nat := 3638024814563211029066555

theorem tailTrace_7085028 : CollatzResearch.WordTrace tailWord_7085028 prefixEnd_7085028 3638024814563211029066555 := by
  unfold tailWord_7085028
  simp only [CollatzResearch.WordTrace]
  refine ⟨129206100288080528646191869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172274800384107371528255825 129206100288080528646191869)
  ·
    refine ⟨48452287608030198242321951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129206100288080528646191869 48452287608030198242321951)
    ·
      refine ⟨72678431412045297363482927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48452287608030198242321951 72678431412045297363482927)
      ·
        refine ⟨109017647118067946045224391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72678431412045297363482927 109017647118067946045224391)
        ·
          refine ⟨163526470677101919067836587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109017647118067946045224391 163526470677101919067836587)
          ·
            refine ⟨245289706015652878601754881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163526470677101919067836587 245289706015652878601754881)
            ·
              refine ⟨183967279511739658951316161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245289706015652878601754881 183967279511739658951316161)
              ·
                refine ⟨137975459633804744213487121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183967279511739658951316161 137975459633804744213487121)
                ·
                  refine ⟨103481594725353558160115341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137975459633804744213487121 103481594725353558160115341)
                  ·
                    refine ⟨38805598022007584310043253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103481594725353558160115341 38805598022007584310043253)
                    ·
                      refine ⟨3638024814563211029066555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38805598022007584310043253 3638024814563211029066555)
                      ·
                        rfl

theorem cell23_7085028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_7085028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085028 prefixEnd_7085028 := by exact prefixLift 7085028
  have htrace : WordTrace (prefixWord ++ tailWord_7085028) baseStart_7085028 baseEnd_7085028 := by
    simpa [prefixWord, tailWord_7085028, baseEnd_7085028] using wordTrace_append hprefix tailTrace_7085028
  have hstable : (prefixWord ++ tailWord_7085028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085028).length < 2 ^ (prefixWord ++ tailWord_7085028).sum := by decide
  have hdescent : baseEnd_7085028 < baseStart_7085028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085052 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_7085052 : Nat := 118140960795 + 7085052 * 2 ^ 59
def prefixEnd_7085052 : Nat := 4983230072969 + 3 ^ 40 * 7085052 * 2
def baseEnd_7085052 : Nat := 1212679046032972978388815

theorem tailTrace_7085052 : CollatzResearch.WordTrace tailWord_7085052 prefixEnd_7085052 1212679046032972978388815 := by
  unfold tailWord_7085052
  simp only [CollatzResearch.WordTrace]
  refine ⟨129206537964037054695628705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172275383952049406260838273 129206537964037054695628705)
  ·
    refine ⟨96904903473027791021721529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129206537964037054695628705 96904903473027791021721529)
    ·
      refine ⟨72678677604770843266291147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96904903473027791021721529 72678677604770843266291147)
      ·
        refine ⟨109018016407156264899436721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72678677604770843266291147 109018016407156264899436721)
        ·
          refine ⟨81763512305367198674577541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109018016407156264899436721 81763512305367198674577541)
          ·
            refine ⟨15330658557256349751483289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81763512305367198674577541 15330658557256349751483289)
            ·
              refine ⟨11497993917942262313612467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15330658557256349751483289 11497993917942262313612467)
              ·
                refine ⟨17246990876913393470418701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497993917942262313612467 17246990876913393470418701)
                ·
                  refine ⟨6467621578842522551407013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17246990876913393470418701 6467621578842522551407013)
                  ·
                    refine ⟨1212679046032972978388815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467621578842522551407013 1212679046032972978388815)
                    ·
                      rfl

theorem cell23_7085052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_7085052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085052 prefixEnd_7085052 := by exact prefixLift 7085052
  have htrace : WordTrace (prefixWord ++ tailWord_7085052) baseStart_7085052 baseEnd_7085052 := by
    simpa [prefixWord, tailWord_7085052, baseEnd_7085052] using wordTrace_append hprefix tailTrace_7085052
  have hstable : (prefixWord ++ tailWord_7085052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085052).length < 2 ^ (prefixWord ++ tailWord_7085052).sum := by decide
  have hdescent : baseEnd_7085052 < baseStart_7085052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085159 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 2, 4]
def baseStart_7085159 : Nat := 118140960795 + 7085159 * 2 ^ 59
def prefixEnd_7085159 : Nat := 4983230072969 + 3 ^ 40 * 7085159 * 2
def baseEnd_7085159 : Nat := 1212697360176316672176151

theorem tailTrace_7085159 : CollatzResearch.WordTrace tailWord_7085159 prefixEnd_7085159 1212697360176316672176151 := by
  unfold tailWord_7085159
  simp only [CollatzResearch.WordTrace]
  refine ⟨258416978538686466665402531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172277985692457644443601687 258416978538686466665402531)
  ·
    refine ⟨387625467808029699998103797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258416978538686466665402531 387625467808029699998103797)
    ·
      refine ⟨36339887607002784374822231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387625467808029699998103797 36339887607002784374822231)
      ·
        refine ⟨54509831410504176562233347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36339887607002784374822231 54509831410504176562233347)
        ·
          refine ⟨81764747115756264843350021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54509831410504176562233347 81764747115756264843350021)
          ·
            refine ⟨15330890084204299658128129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81764747115756264843350021 15330890084204299658128129)
            ·
              refine ⟨11498167563153224743596097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15330890084204299658128129 11498167563153224743596097)
              ·
                refine ⟨8623625672364918557697073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11498167563153224743596097 8623625672364918557697073)
                ·
                  refine ⟨6467719254273688918272805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8623625672364918557697073 6467719254273688918272805)
                  ·
                    refine ⟨1212697360176316672176151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467719254273688918272805 1212697360176316672176151)
                    ·
                      rfl

theorem cell23_7085159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_7085159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085159 prefixEnd_7085159 := by exact prefixLift 7085159
  have htrace : WordTrace (prefixWord ++ tailWord_7085159) baseStart_7085159 baseEnd_7085159 := by
    simpa [prefixWord, tailWord_7085159, baseEnd_7085159] using wordTrace_append hprefix tailTrace_7085159
  have hstable : (prefixWord ++ tailWord_7085159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085159).length < 2 ^ (prefixWord ++ tailWord_7085159).sum := by decide
  have hdescent : baseEnd_7085159 < baseStart_7085159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085205 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7085205 : Nat := 118140960795 + 7085205 * 2 ^ 59
def prefixEnd_7085205 : Nat := 4983230072969 + 3 ^ 40 * 7085205 * 2
def baseEnd_7085205 : Nat := 3638115700639056836553241

theorem tailTrace_7085205 : CollatzResearch.WordTrace tailWord_7085205 prefixEnd_7085205 3638115700639056836553241 := by
  unfold tailWord_7085205
  simp only [CollatzResearch.WordTrace]
  refine ⟨258418656296519816521577069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172279104197679877681051379 258418656296519816521577069)
  ·
    refine ⟨96906996111194931195591401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258418656296519816521577069 96906996111194931195591401)
    ·
      refine ⟨72680247083396198396693551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96906996111194931195591401 72680247083396198396693551)
      ·
        refine ⟨109020370625094297595040327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72680247083396198396693551 109020370625094297595040327)
        ·
          refine ⟨163530555937641446392560491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109020370625094297595040327 163530555937641446392560491)
          ·
            refine ⟨245295833906462169588840737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163530555937641446392560491 245295833906462169588840737)
            ·
              refine ⟨183971875429846627191630553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245295833906462169588840737 183971875429846627191630553)
              ·
                refine ⟨137978906572384970393722915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183971875429846627191630553 137978906572384970393722915)
                ·
                  refine ⟨206968359858577455590584373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137978906572384970393722915 206968359858577455590584373)
                  ·
                    refine ⟨19403283736741636461617285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206968359858577455590584373 19403283736741636461617285)
                    ·
                      refine ⟨3638115700639056836553241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19403283736741636461617285 3638115700639056836553241)
                      ·
                        rfl

theorem cell23_7085205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7085205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085205 prefixEnd_7085205 := by exact prefixLift 7085205
  have htrace : WordTrace (prefixWord ++ tailWord_7085205) baseStart_7085205 baseEnd_7085205 := by
    simpa [prefixWord, tailWord_7085205, baseEnd_7085205] using wordTrace_append hprefix tailTrace_7085205
  have hstable : (prefixWord ++ tailWord_7085205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085205).length < 2 ^ (prefixWord ++ tailWord_7085205).sum := by decide
  have hdescent : baseEnd_7085205 < baseStart_7085205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085233 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7085233 : Nat := 118140960795 + 7085233 * 2 ^ 59
def prefixEnd_7085233 : Nat := 4983230072969 + 3 ^ 40 * 7085233 * 2
def baseEnd_7085233 : Nat := 3638130078097382727003113

theorem tailTrace_7085233 : CollatzResearch.WordTrace tailWord_7085233 prefixEnd_7085233 3638130078097382727003113 := by
  unfold tailWord_7085233
  simp only [CollatzResearch.WordTrace]
  refine ⟨258419677540418377303596353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172279785026945584869064235 258419677540418377303596353)
  ·
    refine ⟨193814758155313782977697265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258419677540418377303596353 193814758155313782977697265)
    ·
      refine ⟨145361068616485337233272949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193814758155313782977697265 145361068616485337233272949)
      ·
        refine ⟨13627600182795500365619339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145361068616485337233272949 13627600182795500365619339)
        ·
          refine ⟨20441400274193250548429009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13627600182795500365619339 20441400274193250548429009)
          ·
            refine ⟨15331050205644937911321757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20441400274193250548429009 15331050205644937911321757)
            ·
              refine ⟨5749143827116851716745659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15331050205644937911321757 5749143827116851716745659)
              ·
                refine ⟨8623715740675277575118489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749143827116851716745659 8623715740675277575118489)
                ·
                  refine ⟨6467786805506458181338867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8623715740675277575118489 6467786805506458181338867)
                  ·
                    refine ⟨9701680208259687272008301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6467786805506458181338867 9701680208259687272008301)
                    ·
                      refine ⟨3638130078097382727003113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9701680208259687272008301 3638130078097382727003113)
                      ·
                        rfl

theorem cell23_7085233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7085233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085233 prefixEnd_7085233 := by exact prefixLift 7085233
  have htrace : WordTrace (prefixWord ++ tailWord_7085233) baseStart_7085233 baseEnd_7085233 := by
    simpa [prefixWord, tailWord_7085233, baseEnd_7085233] using wordTrace_append hprefix tailTrace_7085233
  have hstable : (prefixWord ++ tailWord_7085233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085233).length < 2 ^ (prefixWord ++ tailWord_7085233).sum := by decide
  have hdescent : baseEnd_7085233 < baseStart_7085233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085290 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_7085290 : Nat := 118140960795 + 7085290 * 2 ^ 59
def prefixEnd_7085290 : Nat := 4983230072969 + 3 ^ 40 * 7085290 * 2
def baseEnd_7085290 : Nat := 3638159346494689003990351

theorem tailTrace_7085290 : CollatzResearch.WordTrace tailWord_7085290 prefixEnd_7085290 3638159346494689003990351 := by
  unfold tailWord_7085290
  simp only [CollatzResearch.WordTrace]
  refine ⟨64605439125302969009605331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172281171000807917358947549 64605439125302969009605331)
  ·
    refine ⟨96908158687954453514407997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64605439125302969009605331 96908158687954453514407997)
    ·
      refine ⟨36340559507982920067902999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96908158687954453514407997 36340559507982920067902999)
      ·
        refine ⟨54510839261974380101854499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36340559507982920067902999 54510839261974380101854499)
        ·
          refine ⟨81766258892961570152781749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54510839261974380101854499 81766258892961570152781749)
          ·
            refine ⟨7665586771215147201823289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81766258892961570152781749 7665586771215147201823289)
            ·
              refine ⟨5749190078411360401367467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7665586771215147201823289 5749190078411360401367467)
              ·
                refine ⟨8623785117617040602051201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749190078411360401367467 8623785117617040602051201)
                ·
                  refine ⟨6467838838212780451538401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8623785117617040602051201 6467838838212780451538401)
                  ·
                    refine ⟨4850879128659585338653801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6467838838212780451538401 4850879128659585338653801)
                    ·
                      refine ⟨3638159346494689003990351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850879128659585338653801 3638159346494689003990351)
                      ·
                        rfl

theorem cell23_7085290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_7085290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085290 prefixEnd_7085290 := by exact prefixLift 7085290
  have htrace : WordTrace (prefixWord ++ tailWord_7085290) baseStart_7085290 baseEnd_7085290 := by
    simpa [prefixWord, tailWord_7085290, baseEnd_7085290] using wordTrace_append hprefix tailTrace_7085290
  have hstable : (prefixWord ++ tailWord_7085290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085290).length < 2 ^ (prefixWord ++ tailWord_7085290).sum := by decide
  have hdescent : baseEnd_7085290 < baseStart_7085290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085302 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7085302 : Nat := 118140960795 + 7085302 * 2 ^ 59
def prefixEnd_7085302 : Nat := 4983230072969 + 3 ^ 40 * 7085302 * 2
def baseEnd_7085302 : Nat := 3638165508262542957040295

theorem tailTrace_7085302 : CollatzResearch.WordTrace tailWord_7085302 prefixEnd_7085302 3638165508262542957040295 := by
  unfold tailWord_7085302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151387136073025130491135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172281462784778934725238773 16151387136073025130491135)
  ·
    refine ⟨24227080704109537695736703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16151387136073025130491135 24227080704109537695736703)
    ·
      refine ⟨36340621056164306543605055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24227080704109537695736703 36340621056164306543605055)
      ·
        refine ⟨54510931584246459815407583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36340621056164306543605055 54510931584246459815407583)
        ·
          refine ⟨81766397376369689723111375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54510931584246459815407583 81766397376369689723111375)
          ·
            refine ⟨122649596064554534584667063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81766397376369689723111375 122649596064554534584667063)
            ·
              refine ⟨183974394096831801877000595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122649596064554534584667063 183974394096831801877000595)
              ·
                refine ⟨275961591145247702815500893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183974394096831801877000595 275961591145247702815500893)
                ·
                  refine ⟨103485596679467888555812835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275961591145247702815500893 103485596679467888555812835)
                  ·
                    refine ⟨155228395019201832833719253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103485596679467888555812835 155228395019201832833719253)
                    ·
                      refine ⟨3638165508262542957040295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155228395019201832833719253 3638165508262542957040295)
                      ·
                        rfl

theorem cell23_7085302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7085302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085302 prefixEnd_7085302 := by exact prefixLift 7085302
  have htrace : WordTrace (prefixWord ++ tailWord_7085302) baseStart_7085302 baseEnd_7085302 := by
    simpa [prefixWord, tailWord_7085302, baseEnd_7085302] using wordTrace_append hprefix tailTrace_7085302
  have hstable : (prefixWord ++ tailWord_7085302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085302).length < 2 ^ (prefixWord ++ tailWord_7085302).sum := by decide
  have hdescent : baseEnd_7085302 < baseStart_7085302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085329 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_7085329 : Nat := 118140960795 + 7085329 * 2 ^ 59
def prefixEnd_7085329 : Nat := 4983230072969 + 3 ^ 40 * 7085329 * 2
def baseEnd_7085329 : Nat := 3638179372240214351402671

theorem tailTrace_7085329 : CollatzResearch.WordTrace tailWord_7085329 prefixEnd_7085329 3638179372240214351402671 := by
  unfold tailWord_7085329
  simp only [CollatzResearch.WordTrace]
  refine ⟨258423178948070585699091041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172282119298713723799394027 258423178948070585699091041)
  ·
    refine ⟨193817384211052939274318281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258423178948070585699091041 193817384211052939274318281)
    ·
      refine ⟨145363038158289704455738711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193817384211052939274318281 145363038158289704455738711)
      ·
        refine ⟨218044557237434556683608067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145363038158289704455738711 218044557237434556683608067)
        ·
          refine ⟨327066835856151835025412101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218044557237434556683608067 327066835856151835025412101)
          ·
            refine ⟨61325031723028469067264769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327066835856151835025412101 61325031723028469067264769)
            ·
              refine ⟨45993773792271351800448577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61325031723028469067264769 45993773792271351800448577)
              ·
                refine ⟨34495330344203513850336433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45993773792271351800448577 34495330344203513850336433)
                ·
                  refine ⟨25871497758152635387752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34495330344203513850336433 25871497758152635387752325)
                  ·
                    refine ⟨4850905829653619135203561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25871497758152635387752325 4850905829653619135203561)
                    ·
                      refine ⟨3638179372240214351402671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4850905829653619135203561 3638179372240214351402671)
                      ·
                        rfl

theorem cell23_7085329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_7085329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085329 prefixEnd_7085329 := by exact prefixLift 7085329
  have htrace : WordTrace (prefixWord ++ tailWord_7085329) baseStart_7085329 baseEnd_7085329 := by
    simpa [prefixWord, tailWord_7085329, baseEnd_7085329] using wordTrace_append hprefix tailTrace_7085329
  have hstable : (prefixWord ++ tailWord_7085329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085329).length < 2 ^ (prefixWord ++ tailWord_7085329).sum := by decide
  have hdescent : baseEnd_7085329 < baseStart_7085329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085379 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 3]
def baseStart_7085379 : Nat := 118140960795 + 7085379 * 2 ^ 59
def prefixEnd_7085379 : Nat := 4983230072969 + 3 ^ 40 * 7085379 * 2
def baseEnd_7085379 : Nat := 3638205046272939155777441

theorem tailTrace_7085379 : CollatzResearch.WordTrace tailWord_7085379 prefixEnd_7085379 3638205046272939155777441 := by
  unfold tailWord_7085379
  simp only [CollatzResearch.WordTrace]
  refine ⟨258425002597889444238411191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172283335065259629492274127 258425002597889444238411191)
  ·
    refine ⟨387637503896834166357616787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258425002597889444238411191 387637503896834166357616787)
    ·
      refine ⟨581456255845251249536425181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387637503896834166357616787 581456255845251249536425181)
      ·
        refine ⟨218046095941969218576159443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581456255845251249536425181 218046095941969218576159443)
        ·
          refine ⟨327069143912953827864239165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218046095941969218576159443 327069143912953827864239165)
          ·
            refine ⟨122650928967357685449089687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327069143912953827864239165 122650928967357685449089687)
            ·
              refine ⟨183976393451036528173634531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122650928967357685449089687 183976393451036528173634531)
              ·
                refine ⟨275964590176554792260451797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183976393451036528173634531 275964590176554792260451797)
                ·
                  refine ⟨6467920082263002943604339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 275964590176554792260451797 6467920082263002943604339)
                  ·
                    refine ⟨9701880123394504415406509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6467920082263002943604339 9701880123394504415406509)
                    ·
                      refine ⟨3638205046272939155777441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9701880123394504415406509 3638205046272939155777441)
                      ·
                        rfl

theorem cell23_7085379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_7085379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085379 prefixEnd_7085379 := by exact prefixLift 7085379
  have htrace : WordTrace (prefixWord ++ tailWord_7085379) baseStart_7085379 baseEnd_7085379 := by
    simpa [prefixWord, tailWord_7085379, baseEnd_7085379] using wordTrace_append hprefix tailTrace_7085379
  have hstable : (prefixWord ++ tailWord_7085379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085379).length < 2 ^ (prefixWord ++ tailWord_7085379).sum := by decide
  have hdescent : baseEnd_7085379 < baseStart_7085379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085543 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7085543 : Nat := 118140960795 + 7085543 * 2 ^ 59
def prefixEnd_7085543 : Nat := 4983230072969 + 3 ^ 40 * 7085543 * 2
def baseEnd_7085543 : Nat := 3638289257100276514126687

theorem tailTrace_7085543 : CollatzResearch.WordTrace tailWord_7085543 prefixEnd_7085543 3638289257100276514126687 := by
  unfold tailWord_7085543
  simp only [CollatzResearch.WordTrace]
  refine ⟨258430984169295300247381283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172287322779530200164920855 258430984169295300247381283)
  ·
    refine ⟨387646476253942950371071925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258430984169295300247381283 387646476253942950371071925)
    ·
      refine ⟨36341857148807151597287993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387646476253942950371071925 36341857148807151597287993)
      ·
        refine ⟨27256392861605363697965995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36341857148807151597287993 27256392861605363697965995)
        ·
          refine ⟨40884589292408045546948993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27256392861605363697965995 40884589292408045546948993)
          ·
            refine ⟨30663441969306034160211745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40884589292408045546948993 30663441969306034160211745)
            ·
              refine ⟨22997581476979525620158809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30663441969306034160211745 22997581476979525620158809)
              ·
                refine ⟨17248186107734644215119107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22997581476979525620158809 17248186107734644215119107)
                ·
                  refine ⟨25872279161601966322678661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17248186107734644215119107 25872279161601966322678661)
                  ·
                    refine ⟨4851052342800368685502249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25872279161601966322678661 4851052342800368685502249)
                    ·
                      refine ⟨3638289257100276514126687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851052342800368685502249 3638289257100276514126687)
                      ·
                        rfl

theorem cell23_7085543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7085543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085543 prefixEnd_7085543 := by exact prefixLift 7085543
  have htrace : WordTrace (prefixWord ++ tailWord_7085543) baseStart_7085543 baseEnd_7085543 := by
    simpa [prefixWord, tailWord_7085543, baseEnd_7085543] using wordTrace_append hprefix tailTrace_7085543
  have hstable : (prefixWord ++ tailWord_7085543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085543).length < 2 ^ (prefixWord ++ tailWord_7085543).sum := by decide
  have hdescent : baseEnd_7085543 < baseStart_7085543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085560 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_7085560 : Nat := 118140960795 + 7085560 * 2 ^ 59
def prefixEnd_7085560 : Nat := 4983230072969 + 3 ^ 40 * 7085560 * 2
def baseEnd_7085560 : Nat := 3638297986271402947614109

theorem tailTrace_7085560 : CollatzResearch.WordTrace tailWord_7085560 prefixEnd_7085560 3638297986271402947614109 := by
  unfold tailWord_7085560
  simp only [CollatzResearch.WordTrace]
  refine ⟨129215802105116856075375067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172287736140155808100500089 129215802105116856075375067)
  ·
    refine ⟨193823703157675284113062601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129215802105116856075375067 193823703157675284113062601)
    ·
      refine ⟨145367777368256463084796951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193823703157675284113062601 145367777368256463084796951)
      ·
        refine ⟨218051666052384694627195427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145367777368256463084796951 218051666052384694627195427)
        ·
          refine ⟨327077499078577041940793141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218051666052384694627195427 327077499078577041940793141)
          ·
            refine ⟨30663515538616597681949357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327077499078577041940793141 30663515538616597681949357)
            ·
              refine ⟨11498818326981224130731009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30663515538616597681949357 11498818326981224130731009)
              ·
                refine ⟨8624113745235918098048257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11498818326981224130731009 8624113745235918098048257)
                ·
                  refine ⟨6468085308926938573536193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624113745235918098048257 6468085308926938573536193)
                  ·
                    refine ⟨4851063981695203930152145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468085308926938573536193 4851063981695203930152145)
                    ·
                      refine ⟨3638297986271402947614109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851063981695203930152145 3638297986271402947614109)
                      ·
                        rfl

theorem cell23_7085560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_7085560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085560 prefixEnd_7085560 := by exact prefixLift 7085560
  have htrace : WordTrace (prefixWord ++ tailWord_7085560) baseStart_7085560 baseEnd_7085560 := by
    simpa [prefixWord, tailWord_7085560, baseEnd_7085560] using wordTrace_append hprefix tailTrace_7085560
  have hstable : (prefixWord ++ tailWord_7085560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085560).length < 2 ^ (prefixWord ++ tailWord_7085560).sum := by decide
  have hdescent : baseEnd_7085560 < baseStart_7085560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085576 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_7085576 : Nat := 118140960795 + 7085576 * 2 ^ 59
def prefixEnd_7085576 : Nat := 4983230072969 + 3 ^ 40 * 7085576 * 2
def baseEnd_7085576 : Nat := 3638306201961874885014035

theorem tailTrace_7085576 : CollatzResearch.WordTrace tailWord_7085576 prefixEnd_7085576 3638306201961874885014035 := by
  unfold tailWord_7085576
  simp only [CollatzResearch.WordTrace]
  refine ⟨129216093889087873441666291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172288125185450497922221721 129216093889087873441666291)
  ·
    refine ⟨193824140833631810162499437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129216093889087873441666291 193824140833631810162499437)
    ·
      refine ⟨72684052812611928810937289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193824140833631810162499437 72684052812611928810937289)
      ·
        refine ⟨54513039609458946608202967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72684052812611928810937289 54513039609458946608202967)
        ·
          refine ⟨81769559414188419912304451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54513039609458946608202967 81769559414188419912304451)
          ·
            refine ⟨122654339121282629868456677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81769559414188419912304451 122654339121282629868456677)
            ·
              refine ⟨22997688585240493100335627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122654339121282629868456677 22997688585240493100335627)
              ·
                refine ⟨34496532877860739650503441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22997688585240493100335627 34496532877860739650503441)
                ·
                  refine ⟨25872399658395554737877581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34496532877860739650503441 25872399658395554737877581)
                  ·
                    refine ⟨9702149871898333026704093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25872399658395554737877581 9702149871898333026704093)
                    ·
                      refine ⟨3638306201961874885014035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9702149871898333026704093 3638306201961874885014035)
                      ·
                        rfl

theorem cell23_7085576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_7085576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085576 prefixEnd_7085576 := by exact prefixLift 7085576
  have htrace : WordTrace (prefixWord ++ tailWord_7085576) baseStart_7085576 baseEnd_7085576 := by
    simpa [prefixWord, tailWord_7085576, baseEnd_7085576] using wordTrace_append hprefix tailTrace_7085576
  have hstable : (prefixWord ++ tailWord_7085576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085576).length < 2 ^ (prefixWord ++ tailWord_7085576).sum := by decide
  have hdescent : baseEnd_7085576 < baseStart_7085576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085596 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_7085596 : Nat := 118140960795 + 7085596 * 2 ^ 59
def prefixEnd_7085596 : Nat := 4983230072969 + 3 ^ 40 * 7085596 * 2
def baseEnd_7085596 : Nat := 1212772157191654935587981

theorem tailTrace_7085596 : CollatzResearch.WordTrace tailWord_7085596 prefixEnd_7085596 1212772157191654935587981 := by
  unfold tailWord_7085596
  simp only [CollatzResearch.WordTrace]
  refine ⟨129216458619051645149530321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172288611492068860199373761 129216458619051645149530321)
  ·
    refine ⟨96912343964288733862147741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129216458619051645149530321 96912343964288733862147741)
    ·
      refine ⟨36342128986608275198305403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96912343964288733862147741 36342128986608275198305403)
      ·
        refine ⟨54513193479912412797458105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36342128986608275198305403 54513193479912412797458105)
        ·
          refine ⟨40884895109934309598093579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54513193479912412797458105 40884895109934309598093579)
          ·
            refine ⟨61327342664901464397140369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40884895109934309598093579 61327342664901464397140369)
            ·
              refine ⟨45995506998676098297855277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61327342664901464397140369 45995506998676098297855277)
              ·
                refine ⟨17248315124503536861695729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45995506998676098297855277 17248315124503536861695729)
                ·
                  refine ⟨12936236343377652646271797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17248315124503536861695729 12936236343377652646271797)
                  ·
                    refine ⟨1212772157191654935587981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12936236343377652646271797 1212772157191654935587981)
                    ·
                      rfl

theorem cell23_7085596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_7085596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085596 prefixEnd_7085596 := by exact prefixLift 7085596
  have htrace : WordTrace (prefixWord ++ tailWord_7085596) baseStart_7085596 baseEnd_7085596 := by
    simpa [prefixWord, tailWord_7085596, baseEnd_7085596] using wordTrace_append hprefix tailTrace_7085596
  have hstable : (prefixWord ++ tailWord_7085596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085596).length < 2 ^ (prefixWord ++ tailWord_7085596).sum := by decide
  have hdescent : baseEnd_7085596 < baseStart_7085596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085600 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 5]
def baseStart_7085600 : Nat := 118140960795 + 7085600 * 2 ^ 59
def prefixEnd_7085600 : Nat := 4983230072969 + 3 ^ 40 * 7085600 * 2
def baseEnd_7085600 : Nat := 404257613944175865679325

theorem tailTrace_7085600 : CollatzResearch.WordTrace tailWord_7085600 prefixEnd_7085600 404257613944175865679325 := by
  unfold tailWord_7085600
  simp only [CollatzResearch.WordTrace]
  refine ⟨129216531565044399491103127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172288708753392532654804169 129216531565044399491103127)
  ·
    refine ⟨193824797347566599236654691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129216531565044399491103127 193824797347566599236654691)
    ·
      refine ⟨290737196021349898854982037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193824797347566599236654691 290737196021349898854982037)
      ·
        refine ⟨13628306063500776508827283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 290737196021349898854982037 13628306063500776508827283)
        ·
          refine ⟨20442459095251164763240925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13628306063500776508827283 20442459095251164763240925)
          ·
            refine ⟨7665922160719186786215347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20442459095251164763240925 7665922160719186786215347)
            ·
              refine ⟨11498883241078780179323021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665922160719186786215347 11498883241078780179323021)
              ·
                refine ⟨4312081215404542567246133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11498883241078780179323021 4312081215404542567246133)
                ·
                  refine ⟨404257613944175865679325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312081215404542567246133 404257613944175865679325)
                  ·
                    rfl

theorem cell23_7085600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 5].length) (baseStart_7085600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085600 prefixEnd_7085600 := by exact prefixLift 7085600
  have htrace : WordTrace (prefixWord ++ tailWord_7085600) baseStart_7085600 baseEnd_7085600 := by
    simpa [prefixWord, tailWord_7085600, baseEnd_7085600] using wordTrace_append hprefix tailTrace_7085600
  have hstable : (prefixWord ++ tailWord_7085600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085600).length < 2 ^ (prefixWord ++ tailWord_7085600).sum := by decide
  have hdescent : baseEnd_7085600 < baseStart_7085600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085633 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7085633 : Nat := 118140960795 + 7085633 * 2 ^ 59
def prefixEnd_7085633 : Nat := 4983230072969 + 3 ^ 40 * 7085633 * 2
def baseEnd_7085633 : Nat := 3638335470359181162001273

theorem tailTrace_7085633 : CollatzResearch.WordTrace tailWord_7085633 prefixEnd_7085633 3638335470359181162001273 := by
  unfold tailWord_7085633
  simp only [CollatzResearch.WordTrace]
  refine ⟨258434266738969245618157553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172289511159312830412105035 258434266738969245618157553)
  ·
    refine ⟨193825700054226934213618165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258434266738969245618157553 193825700054226934213618165)
    ·
      refine ⟨18171159380083775082526703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193825700054226934213618165 18171159380083775082526703)
      ·
        refine ⟨27256739070125662623790055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18171159380083775082526703 27256739070125662623790055)
        ·
          refine ⟨40885108605188493935685083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27256739070125662623790055 40885108605188493935685083)
          ·
            refine ⟨61327662907782740903527625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40885108605188493935685083 61327662907782740903527625)
            ·
              refine ⟨45995747180837055677645719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61327662907782740903527625 45995747180837055677645719)
              ·
                refine ⟨68993620771255583516468579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45995747180837055677645719 68993620771255583516468579)
                ·
                  refine ⟨103490431156883375274702869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68993620771255583516468579 103490431156883375274702869)
                  ·
                    refine ⟨4851113960478908216001697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103490431156883375274702869 4851113960478908216001697)
                    ·
                      refine ⟨3638335470359181162001273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851113960478908216001697 3638335470359181162001273)
                      ·
                        rfl

theorem cell23_7085633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7085633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085633 prefixEnd_7085633 := by exact prefixLift 7085633
  have htrace : WordTrace (prefixWord ++ tailWord_7085633) baseStart_7085633 baseEnd_7085633 := by
    simpa [prefixWord, tailWord_7085633, baseEnd_7085633] using wordTrace_append hprefix tailTrace_7085633
  have hstable : (prefixWord ++ tailWord_7085633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085633).length < 2 ^ (prefixWord ++ tailWord_7085633).sum := by decide
  have hdescent : baseEnd_7085633 < baseStart_7085633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085677 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7085677 : Nat := 118140960795 + 7085677 * 2 ^ 59
def prefixEnd_7085677 : Nat := 4983230072969 + 3 ^ 40 * 7085677 * 2
def baseEnd_7085677 : Nat := 1212786021169326329950357

theorem tailTrace_7085677 : CollatzResearch.WordTrace tailWord_7085677 prefixEnd_7085677 1212786021169326329950357 := by
  unfold tailWord_7085677
  simp only [CollatzResearch.WordTrace]
  refine ⟨258435871550809841132759285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172290581033873227421839523 258435871550809841132759285)
  ·
    refine ⟨24228362957888422606196183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258435871550809841132759285 24228362957888422606196183)
    ·
      refine ⟨36342544436832633909294275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24228362957888422606196183 36342544436832633909294275)
      ·
        refine ⟨54513816655248950863941413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36342544436832633909294275 54513816655248950863941413)
        ·
          refine ⟨10221340622859178286989015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54513816655248950863941413 10221340622859178286989015)
          ·
            refine ⟨15332010934288767430483523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221340622859178286989015 15332010934288767430483523)
            ·
              refine ⟨22998016401433151145725285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332010934288767430483523 22998016401433151145725285)
              ·
                refine ⟨4312128075268715839823491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22998016401433151145725285 4312128075268715839823491)
                ·
                  refine ⟨6468192112903073759735237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312128075268715839823491 6468192112903073759735237)
                  ·
                    refine ⟨1212786021169326329950357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6468192112903073759735237 1212786021169326329950357)
                    ·
                      rfl

theorem cell23_7085677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7085677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085677 prefixEnd_7085677 := by exact prefixLift 7085677
  have htrace : WordTrace (prefixWord ++ tailWord_7085677) baseStart_7085677 baseEnd_7085677 := by
    simpa [prefixWord, tailWord_7085677, baseEnd_7085677] using wordTrace_append hprefix tailTrace_7085677
  have hstable : (prefixWord ++ tailWord_7085677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085677).length < 2 ^ (prefixWord ++ tailWord_7085677).sum := by decide
  have hdescent : baseEnd_7085677 < baseStart_7085677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085704 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7085704 : Nat := 118140960795 + 7085704 * 2 ^ 59
def prefixEnd_7085704 : Nat := 4983230072969 + 3 ^ 40 * 7085704 * 2
def baseEnd_7085704 : Nat := 3638371927485650384213447

theorem tailTrace_7085704 : CollatzResearch.WordTrace tailWord_7085704 prefixEnd_7085704 3638371927485650384213447 := by
  unfold tailWord_7085704
  simp only [CollatzResearch.WordTrace]
  refine ⟨129218428160856012371996083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172291237547808016495994777 129218428160856012371996083)
  ·
    refine ⟨193827642241284018557994125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129218428160856012371996083 193827642241284018557994125)
    ·
      refine ⟨72685365840481506959247797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193827642241284018557994125 72685365840481506959247797)
      ·
        refine ⟨6814253047545141277429481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72685365840481506959247797 6814253047545141277429481)
        ·
          refine ⟨5110689785658855958072111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6814253047545141277429481 5110689785658855958072111)
          ·
            refine ⟨7666034678488283937108167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110689785658855958072111 7666034678488283937108167)
            ·
              refine ⟨11499052017732425905662251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7666034678488283937108167 11499052017732425905662251)
              ·
                refine ⟨17248578026598638858493377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499052017732425905662251 17248578026598638858493377)
                ·
                  refine ⟨12936433519948979143870033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17248578026598638858493377 12936433519948979143870033)
                  ·
                    refine ⟨9702325139961734357902525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12936433519948979143870033 9702325139961734357902525)
                    ·
                      refine ⟨3638371927485650384213447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9702325139961734357902525 3638371927485650384213447)
                      ·
                        rfl

theorem cell23_7085704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7085704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085704 prefixEnd_7085704 := by exact prefixLift 7085704
  have htrace : WordTrace (prefixWord ++ tailWord_7085704) baseStart_7085704 baseEnd_7085704 := by
    simpa [prefixWord, tailWord_7085704, baseEnd_7085704] using wordTrace_append hprefix tailTrace_7085704
  have hstable : (prefixWord ++ tailWord_7085704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085704).length < 2 ^ (prefixWord ++ tailWord_7085704).sum := by decide
  have hdescent : baseEnd_7085704 < baseStart_7085704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085710 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7085710 : Nat := 118140960795 + 7085710 * 2 ^ 59
def prefixEnd_7085710 : Nat := 4983230072969 + 3 ^ 40 * 7085710 * 2
def baseEnd_7085710 : Nat := 3638375008369577360738419

theorem tailTrace_7085710 : CollatzResearch.WordTrace tailWord_7085710 prefixEnd_7085710 3638375008369577360738419 := by
  unfold tailWord_7085710
  simp only [CollatzResearch.WordTrace]
  refine ⟨32304634394961285971088823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172291383439793525179140389 32304634394961285971088823)
  ·
    refine ⟨48456951592441928956633235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32304634394961285971088823 48456951592441928956633235)
    ·
      refine ⟨72685427388662893434949853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48456951592441928956633235 72685427388662893434949853)
      ·
        refine ⟨27257035270748585038106195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72685427388662893434949853 27257035270748585038106195)
        ·
          refine ⟨40885552906122877557159293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257035270748585038106195 40885552906122877557159293)
          ·
            refine ⟨15332082339796079083934735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40885552906122877557159293 15332082339796079083934735)
            ·
              refine ⟨22998123509694118625902103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332082339796079083934735 22998123509694118625902103)
              ·
                refine ⟨34497185264541177938853155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22998123509694118625902103 34497185264541177938853155)
                ·
                  refine ⟨51745777896811766908279733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34497185264541177938853155 51745777896811766908279733)
                  ·
                    refine ⟨4851166677826103147651225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51745777896811766908279733 4851166677826103147651225)
                    ·
                      refine ⟨3638375008369577360738419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851166677826103147651225 3638375008369577360738419)
                      ·
                        rfl

theorem cell23_7085710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7085710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085710 prefixEnd_7085710 := by exact prefixLift 7085710
  have htrace : WordTrace (prefixWord ++ tailWord_7085710) baseStart_7085710 baseEnd_7085710 := by
    simpa [prefixWord, tailWord_7085710, baseEnd_7085710] using wordTrace_append hprefix tailTrace_7085710
  have hstable : (prefixWord ++ tailWord_7085710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085710).length < 2 ^ (prefixWord ++ tailWord_7085710).sum := by decide
  have hdescent : baseEnd_7085710 < baseStart_7085710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085720 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 1, 5]
def baseStart_7085720 : Nat := 118140960795 + 7085720 * 2 ^ 59
def prefixEnd_7085720 : Nat := 4983230072969 + 3 ^ 40 * 7085720 * 2
def baseEnd_7085720 : Nat := 1212793381058707440537791

theorem tailTrace_7085720 : CollatzResearch.WordTrace tailWord_7085720 prefixEnd_7085720 1212793381058707440537791 := by
  unfold tailWord_7085720
  simp only [CollatzResearch.WordTrace]
  refine ⟨129218719944827029738287307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172291626593102706317716409 129218719944827029738287307)
  ·
    refine ⟨193828079917240544607430961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129218719944827029738287307 193828079917240544607430961)
    ·
      refine ⟨145371059937930408455573221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193828079917240544607430961 145371059937930408455573221)
      ·
        refine ⟨27257073738361951585419979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145371059937930408455573221 27257073738361951585419979)
        ·
          refine ⟨40885610607542927378129969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257073738361951585419979 40885610607542927378129969)
          ·
            refine ⟨30664207955657195533597477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40885610607542927378129969 30664207955657195533597477)
            ·
              refine ⟨5749538991685724162549527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30664207955657195533597477 5749538991685724162549527)
              ·
                refine ⟨8624308487528586243824291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749538991685724162549527 8624308487528586243824291)
                ·
                  refine ⟨12936462731292879365736437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624308487528586243824291 12936462731292879365736437)
                  ·
                    refine ⟨1212793381058707440537791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12936462731292879365736437 1212793381058707440537791)
                    ·
                      rfl

theorem cell23_7085720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_7085720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085720 prefixEnd_7085720 := by exact prefixLift 7085720
  have htrace : WordTrace (prefixWord ++ tailWord_7085720) baseStart_7085720 baseEnd_7085720 := by
    simpa [prefixWord, tailWord_7085720, baseEnd_7085720] using wordTrace_append hprefix tailTrace_7085720
  have hstable : (prefixWord ++ tailWord_7085720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085720).length < 2 ^ (prefixWord ++ tailWord_7085720).sum := by decide
  have hdescent : baseEnd_7085720 < baseStart_7085720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085753 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7085753 : Nat := 118140960795 + 7085753 * 2 ^ 59
def prefixEnd_7085753 : Nat := 4983230072969 + 3 ^ 40 * 7085753 * 2
def baseEnd_7085753 : Nat := 3638397088037720692500721

theorem tailTrace_7085753 : CollatzResearch.WordTrace tailWord_7085753 prefixEnd_7085753 3638397088037720692500721 := by
  unfold tailWord_7085753
  simp only [CollatzResearch.WordTrace]
  refine ⟨258438643498534506112525913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172292428999023004075017275 258438643498534506112525913)
  ·
    refine ⟨193828982623900879584394435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258438643498534506112525913 193828982623900879584394435)
    ·
      refine ⟨290743473935851319376591653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193828982623900879584394435 290743473935851319376591653)
      ·
        refine ⟨54514401362972122383110935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290743473935851319376591653 54514401362972122383110935)
        ·
          refine ⟨81771602044458183574666403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54514401362972122383110935 81771602044458183574666403)
          ·
            refine ⟨122657403066687275361999605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81771602044458183574666403 122657403066687275361999605)
            ·
              refine ⟨11499131537501932065187463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122657403066687275361999605 11499131537501932065187463)
              ·
                refine ⟨17248697306252898097781195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499131537501932065187463 17248697306252898097781195)
                ·
                  refine ⟨25873045959379347146671793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17248697306252898097781195 25873045959379347146671793)
                  ·
                    refine ⟨19404784469534510360003845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25873045959379347146671793 19404784469534510360003845)
                    ·
                      refine ⟨3638397088037720692500721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19404784469534510360003845 3638397088037720692500721)
                      ·
                        rfl

theorem cell23_7085753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7085753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085753 prefixEnd_7085753 := by exact prefixLift 7085753
  have htrace : WordTrace (prefixWord ++ tailWord_7085753) baseStart_7085753 baseEnd_7085753 := by
    simpa [prefixWord, tailWord_7085753, baseEnd_7085753] using wordTrace_append hprefix tailTrace_7085753
  have hstable : (prefixWord ++ tailWord_7085753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085753).length < 2 ^ (prefixWord ++ tailWord_7085753).sum := by decide
  have hdescent : baseEnd_7085753 < baseStart_7085753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085760 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_7085760 : Nat := 118140960795 + 7085760 * 2 ^ 59
def prefixEnd_7085760 : Nat := 4983230072969 + 3 ^ 40 * 7085760 * 2
def baseEnd_7085760 : Nat := 3638400682402302165113189

theorem tailTrace_7085760 : CollatzResearch.WordTrace tailWord_7085760 prefixEnd_7085760 3638400682402302165113189 := by
  unfold tailWord_7085760
  simp only [CollatzResearch.WordTrace]
  refine ⟨129219449404754573154015367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172292599206339430872020489 129219449404754573154015367)
  ·
    refine ⟨193829174107131859731023051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129219449404754573154015367 193829174107131859731023051)
    ·
      refine ⟨290743761160697789596534577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193829174107131859731023051 290743761160697789596534577)
      ·
        refine ⟨218057820870523342197400933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290743761160697789596534577 218057820870523342197400933)
        ·
          refine ⟨40885841413223126662012675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218057820870523342197400933 40885841413223126662012675)
          ·
            refine ⟨61328762119834689993019013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40885841413223126662012675 61328762119834689993019013)
            ·
              refine ⟨11499142897469004373691065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61328762119834689993019013 11499142897469004373691065)
              ·
                refine ⟨8624357173101753280268299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11499142897469004373691065 8624357173101753280268299)
                ·
                  refine ⟨12936535759652629920402449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624357173101753280268299 12936535759652629920402449)
                  ·
                    refine ⟨9702401819739472440301837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12936535759652629920402449 9702401819739472440301837)
                    ·
                      refine ⟨3638400682402302165113189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9702401819739472440301837 3638400682402302165113189)
                      ·
                        rfl

theorem cell23_7085760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_7085760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085760 prefixEnd_7085760 := by exact prefixLift 7085760
  have htrace : WordTrace (prefixWord ++ tailWord_7085760) baseStart_7085760 baseEnd_7085760 := by
    simpa [prefixWord, tailWord_7085760, baseEnd_7085760] using wordTrace_append hprefix tailTrace_7085760
  have hstable : (prefixWord ++ tailWord_7085760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085760).length < 2 ^ (prefixWord ++ tailWord_7085760).sum := by decide
  have hdescent : baseEnd_7085760 < baseStart_7085760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085834 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_7085834 : Nat := 118140960795 + 7085834 * 2 ^ 59
def prefixEnd_7085834 : Nat := 4983230072969 + 3 ^ 40 * 7085834 * 2
def baseEnd_7085834 : Nat := 3638438679970734875587849

theorem tailTrace_7085834 : CollatzResearch.WordTrace tailWord_7085834 prefixEnd_7085834 3638438679970734875587849 := by
  unfold tailWord_7085834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64610399452810264236556139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172294398540827371297483037 64610399452810264236556139)
  ·
    refine ⟨96915599179215396354834209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64610399452810264236556139 96915599179215396354834209)
    ·
      refine ⟨72686699384411547266125657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96915599179215396354834209 72686699384411547266125657)
      ·
        refine ⟨54515024538308660449594243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72686699384411547266125657 54515024538308660449594243)
        ·
          refine ⟨81772536807462990674391365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54515024538308660449594243 81772536807462990674391365)
          ·
            refine ⟨15332350651399310751448381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81772536807462990674391365 15332350651399310751448381)
            ·
              refine ⟨5749631494274741531793143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15332350651399310751448381 5749631494274741531793143)
              ·
                refine ⟨8624447241412112297689715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749631494274741531793143 8624447241412112297689715)
                ·
                  refine ⟨12936670862118168446534573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624447241412112297689715 12936670862118168446534573)
                  ·
                    refine ⟨4851251573294313167450465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12936670862118168446534573 4851251573294313167450465)
                    ·
                      refine ⟨3638438679970734875587849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851251573294313167450465 3638438679970734875587849)
                      ·
                        rfl

theorem cell23_7085834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_7085834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085834 prefixEnd_7085834 := by exact prefixLift 7085834
  have htrace : WordTrace (prefixWord ++ tailWord_7085834) baseStart_7085834 baseEnd_7085834 := by
    simpa [prefixWord, tailWord_7085834, baseEnd_7085834] using wordTrace_append hprefix tailTrace_7085834
  have hstable : (prefixWord ++ tailWord_7085834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085834).length < 2 ^ (prefixWord ++ tailWord_7085834).sum := by decide
  have hdescent : baseEnd_7085834 < baseStart_7085834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085860 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7085860 : Nat := 118140960795 + 7085860 * 2 ^ 59
def prefixEnd_7085860 : Nat := 4983230072969 + 3 ^ 40 * 7085860 * 2
def baseEnd_7085860 : Nat := 3638452030467751773862729

theorem tailTrace_7085860 : CollatzResearch.WordTrace tailWord_7085860 prefixEnd_7085860 3638452030467751773862729 := by
  unfold tailWord_7085860
  simp only [CollatzResearch.WordTrace]
  refine ⟨129221273054573431693335517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172295030739431242257780689 129221273054573431693335517)
  ·
    refine ⟨48457977395465036885000819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129221273054573431693335517 48457977395465036885000819)
    ·
      refine ⟨72686966093197555327501229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48457977395465036885000819 72686966093197555327501229)
      ·
        refine ⟨27257612284949083247812961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72686966093197555327501229 27257612284949083247812961)
        ·
          refine ⟨20443209213711812435859721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27257612284949083247812961 20443209213711812435859721)
          ·
            refine ⟨15332406910283859326894791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443209213711812435859721 15332406910283859326894791)
            ·
              refine ⟨22998610365425788990342187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332406910283859326894791 22998610365425788990342187)
              ·
                refine ⟨34497915548138683485513281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22998610365425788990342187 34497915548138683485513281)
                ·
                  refine ⟨25873436661104012614134961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34497915548138683485513281 25873436661104012614134961)
                  ·
                    refine ⟨19405077495828009460601221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25873436661104012614134961 19405077495828009460601221)
                    ·
                      refine ⟨3638452030467751773862729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19405077495828009460601221 3638452030467751773862729)
                      ·
                        rfl

theorem cell23_7085860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7085860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085860 prefixEnd_7085860 := by exact prefixLift 7085860
  have htrace : WordTrace (prefixWord ++ tailWord_7085860) baseStart_7085860 baseEnd_7085860 := by
    simpa [prefixWord, tailWord_7085860, baseEnd_7085860] using wordTrace_append hprefix tailTrace_7085860
  have hstable : (prefixWord ++ tailWord_7085860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085860).length < 2 ^ (prefixWord ++ tailWord_7085860).sum := by decide
  have hdescent : baseEnd_7085860 < baseStart_7085860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085864 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_7085864 : Nat := 118140960795 + 7085864 * 2 ^ 59
def prefixEnd_7085864 : Nat := 4983230072969 + 3 ^ 40 * 7085864 * 2
def baseEnd_7085864 : Nat := 3638454084390369758212711

theorem tailTrace_7085864 : CollatzResearch.WordTrace tailWord_7085864 prefixEnd_7085864 3638454084390369758212711 := by
  unfold tailWord_7085864
  simp only [CollatzResearch.WordTrace]
  refine ⟨129221346000566186034908323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172295128000754914713211097 129221346000566186034908323)
  ·
    refine ⟨193832019000849279052362485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129221346000566186034908323 193832019000849279052362485)
    ·
      refine ⟨18171751781329619911158983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193832019000849279052362485 18171751781329619911158983)
      ·
        refine ⟨27257627671994429866738475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18171751781329619911158983 27257627671994429866738475)
        ·
          refine ⟨40886441507991644800107713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257627671994429866738475 40886441507991644800107713)
          ·
            refine ⟨30664831130993733600080785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40886441507991644800107713 30664831130993733600080785)
            ·
              refine ⟨22998623348245300200060589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30664831130993733600080785 22998623348245300200060589)
              ·
                refine ⟨8624483755591987575022721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22998623348245300200060589 8624483755591987575022721)
                ·
                  refine ⟨6468362816693990681267041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624483755591987575022721 6468362816693990681267041)
                  ·
                    refine ⟨4851272112520493010950281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468362816693990681267041 4851272112520493010950281)
                    ·
                      refine ⟨3638454084390369758212711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851272112520493010950281 3638454084390369758212711)
                      ·
                        rfl

theorem cell23_7085864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_7085864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085864 prefixEnd_7085864 := by exact prefixLift 7085864
  have htrace : WordTrace (prefixWord ++ tailWord_7085864) baseStart_7085864 baseEnd_7085864 := by
    simpa [prefixWord, tailWord_7085864, baseEnd_7085864] using wordTrace_append hprefix tailTrace_7085864
  have hstable : (prefixWord ++ tailWord_7085864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085864).length < 2 ^ (prefixWord ++ tailWord_7085864).sum := by decide
  have hdescent : baseEnd_7085864 < baseStart_7085864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7085887 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 5]
def baseStart_7085887 : Nat := 118140960795 + 7085887 * 2 ^ 59
def prefixEnd_7085887 : Nat := 4983230072969 + 3 ^ 40 * 7085887 * 2
def baseEnd_7085887 : Nat := 404273988271713685358345

theorem tailTrace_7085887 : CollatzResearch.WordTrace tailWord_7085887 prefixEnd_7085887 404273988271713685358345 := by
  unfold tailWord_7085887
  simp only [CollatzResearch.WordTrace]
  refine ⟨258443530880049046997903915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172295687253366031331935943 258443530880049046997903915)
  ·
    refine ⟨387665296320073570496855873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258443530880049046997903915 387665296320073570496855873)
    ·
      refine ⟨290748972240055177872641905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387665296320073570496855873 290748972240055177872641905)
      ·
        refine ⟨218061729180041383404481429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290748972240055177872641905 218061729180041383404481429)
        ·
          refine ⟨10221643555314439847085067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218061729180041383404481429 10221643555314439847085067)
          ·
            refine ⟨15332465332971659770627601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221643555314439847085067 15332465332971659770627601)
            ·
              refine ⟨11499348999728744827970701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15332465332971659770627601 11499348999728744827970701)
              ·
                refine ⟨4312255874898279310489013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11499348999728744827970701 4312255874898279310489013)
                ·
                  refine ⟨404273988271713685358345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312255874898279310489013 404273988271713685358345)
                  ·
                    rfl

theorem cell23_7085887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 5].length) (baseStart_7085887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7085887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7085887 prefixEnd_7085887 := by exact prefixLift 7085887
  have htrace : WordTrace (prefixWord ++ tailWord_7085887) baseStart_7085887 baseEnd_7085887 := by
    simpa [prefixWord, tailWord_7085887, baseEnd_7085887] using wordTrace_append hprefix tailTrace_7085887
  have hstable : (prefixWord ++ tailWord_7085887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7085887).length < 2 ^ (prefixWord ++ tailWord_7085887).sum := by decide
  have hdescent : baseEnd_7085887 < baseStart_7085887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7085887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086014 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_7086014 : Nat := 118140960795 + 7086014 * 2 ^ 59
def prefixEnd_7086014 : Nat := 4983230072969 + 3 ^ 40 * 7086014 * 2
def baseEnd_7086014 : Nat := 3638531106488544171337021

theorem tailTrace_7086014 : CollatzResearch.WordTrace tailWord_7086014 prefixEnd_7086014 3638531106488544171337021 := by
  unfold tailWord_7086014
  simp only [CollatzResearch.WordTrace]
  refine ⟨32306020368823618460972137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172298775300392631791851397 32306020368823618460972137)
  ·
    refine ⟨24229515276617713845729103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32306020368823618460972137 24229515276617713845729103)
    ·
      refine ⟨36344272914926570768593655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24229515276617713845729103 36344272914926570768593655)
      ·
        refine ⟨54516409372389856152890483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36344272914926570768593655 54516409372389856152890483)
        ·
          refine ⟨81774614058584784229335725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54516409372389856152890483 81774614058584784229335725)
          ·
            refine ⟨30665480271969294086000897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81774614058584784229335725 30665480271969294086000897)
            ·
              refine ⟨22999110203976970564500673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30665480271969294086000897 22999110203976970564500673)
              ·
                refine ⟨17249332652982727923375505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22999110203976970564500673 17249332652982727923375505)
                ·
                  refine ⟨12936999489737045942531629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17249332652982727923375505 12936999489737045942531629)
                  ·
                    refine ⟨4851374808651392228449361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12936999489737045942531629 4851374808651392228449361)
                    ·
                      refine ⟨3638531106488544171337021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851374808651392228449361 3638531106488544171337021)
                      ·
                        rfl

theorem cell23_7086014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_7086014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086014 prefixEnd_7086014 := by exact prefixLift 7086014
  have htrace : WordTrace (prefixWord ++ tailWord_7086014) baseStart_7086014 baseEnd_7086014 := by
    simpa [prefixWord, tailWord_7086014, baseEnd_7086014] using wordTrace_append hprefix tailTrace_7086014
  have hstable : (prefixWord ++ tailWord_7086014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086014).length < 2 ^ (prefixWord ++ tailWord_7086014).sum := by decide
  have hdescent : baseEnd_7086014 < baseStart_7086014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086030 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_7086030 : Nat := 118140960795 + 7086030 * 2 ^ 59
def prefixEnd_7086030 : Nat := 4983230072969 + 3 ^ 40 * 7086030 * 2
def baseEnd_7086030 : Nat := 3638539322179016108736947

theorem tailTrace_7086030 : CollatzResearch.WordTrace tailWord_7086030 prefixEnd_7086030 3638539322179016108736947 := by
  unfold tailWord_7086030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32306093314816372802544943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172299164345687321613573029 32306093314816372802544943)
  ·
    refine ⟨48459139972224559203817415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32306093314816372802544943 48459139972224559203817415)
    ·
      refine ⟨72688709958336838805726123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48459139972224559203817415 72688709958336838805726123)
      ·
        refine ⟨109033064937505258208589185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72688709958336838805726123 109033064937505258208589185)
        ·
          refine ⟨81774798703128943656441889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109033064937505258208589185 81774798703128943656441889)
          ·
            refine ⟨61331099027346707742331417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81774798703128943656441889 61331099027346707742331417)
            ·
              refine ⟨45998324270510030806748563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61331099027346707742331417 45998324270510030806748563)
              ·
                refine ⟨68997486405765046210122845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45998324270510030806748563 68997486405765046210122845)
                ·
                  refine ⟨25874057402161892328796067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68997486405765046210122845 25874057402161892328796067)
                  ·
                    refine ⟨38811086103242838493194101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25874057402161892328796067 38811086103242838493194101)
                    ·
                      refine ⟨3638539322179016108736947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38811086103242838493194101 3638539322179016108736947)
                      ·
                        rfl

theorem cell23_7086030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_7086030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086030 prefixEnd_7086030 := by exact prefixLift 7086030
  have htrace : WordTrace (prefixWord ++ tailWord_7086030) baseStart_7086030 baseEnd_7086030 := by
    simpa [prefixWord, tailWord_7086030, baseEnd_7086030] using wordTrace_append hprefix tailTrace_7086030
  have hstable : (prefixWord ++ tailWord_7086030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086030).length < 2 ^ (prefixWord ++ tailWord_7086030).sum := by decide
  have hdescent : baseEnd_7086030 < baseStart_7086030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086033 : List Nat := [1, 2, 2, 1, 2, 1, 2, 12]
def baseStart_7086033 : Nat := 118140960795 + 7086033 * 2 ^ 59
def prefixEnd_7086033 : Nat := 4983230072969 + 3 ^ 40 * 7086033 * 2
def baseEnd_7086033 : Nat := 134760772689665910999979

theorem tailTrace_7086033 : CollatzResearch.WordTrace tailWord_7086033 prefixEnd_7086033 134760772689665910999979 := by
  unfold tailWord_7086033
  simp only [CollatzResearch.WordTrace]
  refine ⟨258448855937520113932718753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172299237291680075955145835 258448855937520113932718753)
  ·
    refine ⟨193836641953140085449539065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258448855937520113932718753 193836641953140085449539065)
    ·
      refine ⟨145377481464855064087154299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193836641953140085449539065 145377481464855064087154299)
      ·
        refine ⟨218066222197282596130731449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145377481464855064087154299 218066222197282596130731449)
        ·
          refine ⟨163549666647961947098048587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218066222197282596130731449 163549666647961947098048587)
          ·
            refine ⟨245324499971942920647072881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163549666647961947098048587 245324499971942920647072881)
            ·
              refine ⟨183993374978957190485304661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245324499971942920647072881 183993374978957190485304661)
              ·
                refine ⟨134760772689665910999979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 183993374978957190485304661 134760772689665910999979)
                ·
                  rfl

theorem cell23_7086033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 12].length) (baseStart_7086033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086033 prefixEnd_7086033 := by exact prefixLift 7086033
  have htrace : WordTrace (prefixWord ++ tailWord_7086033) baseStart_7086033 baseEnd_7086033 := by
    simpa [prefixWord, tailWord_7086033, baseEnd_7086033] using wordTrace_append hprefix tailTrace_7086033
  have hstable : (prefixWord ++ tailWord_7086033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086033).length < 2 ^ (prefixWord ++ tailWord_7086033).sum := by decide
  have hdescent : baseEnd_7086033 < baseStart_7086033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086037 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_7086037 : Nat := 118140960795 + 7086037 * 2 ^ 59
def prefixEnd_7086037 : Nat := 4983230072969 + 3 ^ 40 * 7086037 * 2
def baseEnd_7086037 : Nat := 1212847638847865860449805

theorem tailTrace_7086037 : CollatzResearch.WordTrace tailWord_7086037 prefixEnd_7086037 1212847638847865860449805 := by
  unfold tailWord_7086037
  simp only [CollatzResearch.WordTrace]
  refine ⟨258449001829505622615864365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172299334553003748410576243 258449001829505622615864365)
  ·
    refine ⟨96918375686064608480949137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258449001829505622615864365 96918375686064608480949137)
    ·
      refine ⟨72688781764548456360711853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96918375686064608480949137 72688781764548456360711853)
      ·
        refine ⟨27258293161705671135266945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72688781764548456360711853 27258293161705671135266945)
        ·
          refine ⟨20443719871279253351450209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27258293161705671135266945 20443719871279253351450209)
          ·
            refine ⟨15332789903459440013587657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443719871279253351450209 15332789903459440013587657)
            ·
              refine ⟨11499592427594580010190743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15332789903459440013587657 11499592427594580010190743)
              ·
                refine ⟨17249388641391870015286115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499592427594580010190743 17249388641391870015286115)
                ·
                  refine ⟨25874082962087805022929173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17249388641391870015286115 25874082962087805022929173)
                  ·
                    refine ⟨1212847638847865860449805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25874082962087805022929173 1212847638847865860449805)
                    ·
                      rfl

theorem cell23_7086037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_7086037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086037 prefixEnd_7086037 := by exact prefixLift 7086037
  have htrace : WordTrace (prefixWord ++ tailWord_7086037) baseStart_7086037 baseEnd_7086037 := by
    simpa [prefixWord, tailWord_7086037, baseEnd_7086037] using wordTrace_append hprefix tailTrace_7086037
  have hstable : (prefixWord ++ tailWord_7086037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086037).length < 2 ^ (prefixWord ++ tailWord_7086037).sum := by decide
  have hdescent : baseEnd_7086037 < baseStart_7086037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086047 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_7086047 : Nat := 118140960795 + 7086047 * 2 ^ 59
def prefixEnd_7086047 : Nat := 4983230072969 + 3 ^ 40 * 7086047 * 2
def baseEnd_7086047 : Nat := 3638548051350142542224369

theorem tailTrace_7086047 : CollatzResearch.WordTrace tailWord_7086047 prefixEnd_7086047 3638548051350142542224369 := by
  unfold tailWord_7086047
  simp only [CollatzResearch.WordTrace]
  refine ⟨258449366559469394323728395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172299577706312929549152263 258449366559469394323728395)
  ·
    refine ⟨387674049839204091485592593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258449366559469394323728395 387674049839204091485592593)
    ·
      refine ⟨290755537379403068614194445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387674049839204091485592593 290755537379403068614194445)
      ·
        refine ⟨109033326517276150730322917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290755537379403068614194445 109033326517276150730322917)
        ·
          refine ⟨20443748721989278261935547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109033326517276150730322917 20443748721989278261935547)
          ·
            refine ⟨30665623082983917392903321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20443748721989278261935547 30665623082983917392903321)
            ·
              refine ⟨22999217312237938044677491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30665623082983917392903321 22999217312237938044677491)
              ·
                refine ⟨34498825968356907067016237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22999217312237938044677491 34498825968356907067016237)
                ·
                  refine ⟨12937059738133840150131089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34498825968356907067016237 12937059738133840150131089)
                  ·
                    refine ⟨9702794803600380112598317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12937059738133840150131089 9702794803600380112598317)
                    ·
                      refine ⟨3638548051350142542224369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9702794803600380112598317 3638548051350142542224369)
                      ·
                        rfl

theorem cell23_7086047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_7086047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086047 prefixEnd_7086047 := by exact prefixLift 7086047
  have htrace : WordTrace (prefixWord ++ tailWord_7086047) baseStart_7086047 baseEnd_7086047 := by
    simpa [prefixWord, tailWord_7086047, baseEnd_7086047] using wordTrace_append hprefix tailTrace_7086047
  have hstable : (prefixWord ++ tailWord_7086047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086047).length < 2 ^ (prefixWord ++ tailWord_7086047).sum := by decide
  have hdescent : baseEnd_7086047 < baseStart_7086047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086061 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7086061 : Nat := 118140960795 + 7086061 * 2 ^ 59
def prefixEnd_7086061 : Nat := 4983230072969 + 3 ^ 40 * 7086061 * 2
def baseEnd_7086061 : Nat := 3638555240079305487449305

theorem tailTrace_7086061 : CollatzResearch.WordTrace tailWord_7086061 prefixEnd_7086061 3638555240079305487449305 := by
  unfold tailWord_7086061
  simp only [CollatzResearch.WordTrace]
  refine ⟨258449877181418674714738037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172299918120945783143158691 258449877181418674714738037)
  ·
    refine ⟨24229675985758000754506691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258449877181418674714738037 24229675985758000754506691)
    ·
      refine ⟨36344513978637001131760037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24229675985758000754506691 36344513978637001131760037)
      ·
        refine ⟨6814596370994437712205007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36344513978637001131760037 6814596370994437712205007)
        ·
          refine ⟨10221894556491656568307511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814596370994437712205007 10221894556491656568307511)
          ·
            refine ⟨15332841834737484852461267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221894556491656568307511 15332841834737484852461267)
            ·
              refine ⟨22999262752106227278691901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332841834737484852461267 22999262752106227278691901)
              ·
                refine ⟨8624723532039835229509463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22999262752106227278691901 8624723532039835229509463)
                ·
                  refine ⟨12937085298059752844264195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624723532039835229509463 12937085298059752844264195)
                  ·
                    refine ⟨19405627947089629266396293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12937085298059752844264195 19405627947089629266396293)
                    ·
                      refine ⟨3638555240079305487449305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19405627947089629266396293 3638555240079305487449305)
                      ·
                        rfl

theorem cell23_7086061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7086061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086061 prefixEnd_7086061 := by exact prefixLift 7086061
  have htrace : WordTrace (prefixWord ++ tailWord_7086061) baseStart_7086061 baseEnd_7086061 := by
    simpa [prefixWord, tailWord_7086061, baseEnd_7086061] using wordTrace_append hprefix tailTrace_7086061
  have hstable : (prefixWord ++ tailWord_7086061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086061).length < 2 ^ (prefixWord ++ tailWord_7086061).sum := by decide
  have hdescent : baseEnd_7086061 < baseStart_7086061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086064 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3]
def baseStart_7086064 : Nat := 118140960795 + 7086064 * 2 ^ 59
def prefixEnd_7086064 : Nat := 4983230072969 + 3 ^ 40 * 7086064 * 2
def baseEnd_7086064 : Nat := 3638556780521268975711791

theorem tailTrace_7086064 : CollatzResearch.WordTrace tailWord_7086064 prefixEnd_7086064 3638556780521268975711791 := by
  unfold tailWord_7086064
  simp only [CollatzResearch.WordTrace]
  refine ⟨129224993300203903113548623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172299991066938537484731497 129224993300203903113548623)
  ·
    refine ⟨193837489950305854670322935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129224993300203903113548623 193837489950305854670322935)
    ·
      refine ⟨290756234925458782005484403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193837489950305854670322935 290756234925458782005484403)
      ·
        refine ⟨436134352388188173008226605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290756234925458782005484403 436134352388188173008226605)
        ·
          refine ⟨163550382145570564878084977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436134352388188173008226605 163550382145570564878084977)
          ·
            refine ⟨122662786609177923658563733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163550382145570564878084977 122662786609177923658563733)
            ·
              refine ⟨5749818122305215171495175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122662786609177923658563733 5749818122305215171495175)
              ·
                refine ⟨8624727183457822757242763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749818122305215171495175 8624727183457822757242763)
                ·
                  refine ⟨12937090775186734135864145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624727183457822757242763 12937090775186734135864145)
                  ·
                    refine ⟨9702818081390050601898109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12937090775186734135864145 9702818081390050601898109)
                    ·
                      refine ⟨3638556780521268975711791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9702818081390050601898109 3638556780521268975711791)
                      ·
                        rfl

theorem cell23_7086064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3].length) (baseStart_7086064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086064 prefixEnd_7086064 := by exact prefixLift 7086064
  have htrace : WordTrace (prefixWord ++ tailWord_7086064) baseStart_7086064 baseEnd_7086064 := by
    simpa [prefixWord, tailWord_7086064, baseEnd_7086064] using wordTrace_append hprefix tailTrace_7086064
  have hstable : (prefixWord ++ tailWord_7086064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086064).length < 2 ^ (prefixWord ++ tailWord_7086064).sum := by decide
  have hdescent : baseEnd_7086064 < baseStart_7086064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086078 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7086078 : Nat := 118140960795 + 7086078 * 2 ^ 59
def prefixEnd_7086078 : Nat := 4983230072969 + 3 ^ 40 * 7086078 * 2
def baseEnd_7086078 : Nat := 3638563969250431920936727

theorem tailTrace_7086078 : CollatzResearch.WordTrace tailWord_7086078 prefixEnd_7086078 3638563969250431920936727 := by
  unfold tailWord_7086078
  simp only [CollatzResearch.WordTrace]
  refine ⟨32306312152794635827263361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172300331481571391078737925 32306312152794635827263361)
  ·
    refine ⟨24229734114595976870447521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32306312152794635827263361 24229734114595976870447521)
    ·
      refine ⟨18172300585946982652835641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24229734114595976870447521 18172300585946982652835641)
      ·
        refine ⟨13629225439460236989626731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18172300585946982652835641 13629225439460236989626731)
        ·
          refine ⟨20443838159190355484440097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629225439460236989626731 20443838159190355484440097)
          ·
            refine ⟨15332878619392766613330073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443838159190355484440097 15332878619392766613330073)
            ·
              refine ⟨11499658964544574959997555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15332878619392766613330073 11499658964544574959997555)
              ·
                refine ⟨17249488446816862439996333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499658964544574959997555 17249488446816862439996333)
                ·
                  refine ⟨6468558167556323414998625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17249488446816862439996333 6468558167556323414998625)
                  ·
                    refine ⟨4851418625667242561248969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468558167556323414998625 4851418625667242561248969)
                    ·
                      refine ⟨3638563969250431920936727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851418625667242561248969 3638563969250431920936727)
                      ·
                        rfl

theorem cell23_7086078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7086078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086078 prefixEnd_7086078 := by exact prefixLift 7086078
  have htrace : WordTrace (prefixWord ++ tailWord_7086078) baseStart_7086078 baseEnd_7086078 := by
    simpa [prefixWord, tailWord_7086078, baseEnd_7086078] using wordTrace_append hprefix tailTrace_7086078
  have hstable : (prefixWord ++ tailWord_7086078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086078).length < 2 ^ (prefixWord ++ tailWord_7086078).sum := by decide
  have hdescent : baseEnd_7086078 < baseStart_7086078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086151 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_7086151 : Nat := 118140960795 + 7086151 * 2 ^ 59
def prefixEnd_7086151 : Nat := 4983230072969 + 3 ^ 40 * 7086151 * 2
def baseEnd_7086151 : Nat := 3638601453338210135323891

theorem tailTrace_7086151 : CollatzResearch.WordTrace tailWord_7086151 prefixEnd_7086151 3638601453338210135323891 := by
  unfold tailWord_7086151
  simp only [CollatzResearch.WordTrace]
  refine ⟨258453159751092620085514307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172302106500728413390342871 258453159751092620085514307)
  ·
    refine ⟨387679739626638930128271461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258453159751092620085514307 387679739626638930128271461)
    ·
      refine ⟨72689951179994799399050899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387679739626638930128271461 72689951179994799399050899)
      ·
        refine ⟨109034926769992199098576349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72689951179994799399050899 109034926769992199098576349)
        ·
          refine ⟨40888097538747074661966131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109034926769992199098576349 40888097538747074661966131)
          ·
            refine ⟨61332146308120611992949197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40888097538747074661966131 61332146308120611992949197)
            ·
              refine ⟨22999554865545229497355949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61332146308120611992949197 22999554865545229497355949)
              ·
                refine ⟨8624833074579461061508481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22999554865545229497355949 8624833074579461061508481)
                ·
                  refine ⟨6468624805934595796131361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8624833074579461061508481 6468624805934595796131361)
                  ·
                    refine ⟨4851468604450946847098521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468624805934595796131361 4851468604450946847098521)
                    ·
                      refine ⟨3638601453338210135323891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851468604450946847098521 3638601453338210135323891)
                      ·
                        rfl

theorem cell23_7086151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_7086151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086151 prefixEnd_7086151 := by exact prefixLift 7086151
  have htrace : WordTrace (prefixWord ++ tailWord_7086151) baseStart_7086151 baseEnd_7086151 := by
    simpa [prefixWord, tailWord_7086151, baseEnd_7086151] using wordTrace_append hprefix tailTrace_7086151
  have hstable : (prefixWord ++ tailWord_7086151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086151).length < 2 ^ (prefixWord ++ tailWord_7086151).sum := by decide
  have hdescent : baseEnd_7086151 < baseStart_7086151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086157 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7086157 : Nat := 118140960795 + 7086157 * 2 ^ 59
def prefixEnd_7086157 : Nat := 4983230072969 + 3 ^ 40 * 7086157 * 2
def baseEnd_7086157 : Nat := 404289392691348567983207

theorem tailTrace_7086157 : CollatzResearch.WordTrace tailWord_7086157 prefixEnd_7086157 404289392691348567983207 := by
  unfold tailWord_7086157
  simp only [CollatzResearch.WordTrace]
  refine ⟨258453378589070883110232725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172302252392713922073488483 258453378589070883110232725)
  ·
    refine ⟨12115002121362697645792159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258453378589070883110232725 12115002121362697645792159)
    ·
      refine ⟨18172503182044046468688239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115002121362697645792159 18172503182044046468688239)
      ·
        refine ⟨27258754773066069703032359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18172503182044046468688239 27258754773066069703032359)
        ·
          refine ⟨40888132159599104554548539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27258754773066069703032359 40888132159599104554548539)
          ·
            refine ⟨61332198239398656831822809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40888132159599104554548539 61332198239398656831822809)
            ·
              refine ⟨45999148679548992623867107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61332198239398656831822809 45999148679548992623867107)
              ·
                refine ⟨68998723019323488935800661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45999148679548992623867107 68998723019323488935800661)
                ·
                  refine ⟨404289392691348567983207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68998723019323488935800661 404289392691348567983207)
                  ·
                    rfl

theorem cell23_7086157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7086157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086157 prefixEnd_7086157 := by exact prefixLift 7086157
  have htrace : WordTrace (prefixWord ++ tailWord_7086157) baseStart_7086157 baseEnd_7086157 := by
    simpa [prefixWord, tailWord_7086157, baseEnd_7086157] using wordTrace_append hprefix tailTrace_7086157
  have hstable : (prefixWord ++ tailWord_7086157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086157).length < 2 ^ (prefixWord ++ tailWord_7086157).sum := by decide
  have hdescent : baseEnd_7086157 < baseStart_7086157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
