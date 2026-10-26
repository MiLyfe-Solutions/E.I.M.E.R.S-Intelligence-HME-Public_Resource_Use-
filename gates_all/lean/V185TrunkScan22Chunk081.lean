import V185TrunkScan22Chunk080

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_727780 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_727780 : Nat := 118140960795 + 727780 * 2 ^ 59
def prefixEnd_727780 : Nat := 4983230072969 + 3 ^ 40 * 727780 * 2
def baseEnd_727780 : Nat := 83044655717615064689557

theorem tailTrace_727780 : CollatzResearch.WordTrace tailWord_727780 prefixEnd_727780 83044655717615064689557 := by
  unfold tailWord_727780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13272158651692414886742397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17696211535589886515656529 13272158651692414886742397)
  ·
    refine ⟨4977059494384655582528399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13272158651692414886742397 4977059494384655582528399)
    ·
      refine ⟨7465589241576983373792599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977059494384655582528399 7465589241576983373792599)
      ·
        refine ⟨11198383862365475060688899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465589241576983373792599 11198383862365475060688899)
        ·
          refine ⟨16797575793548212591033349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11198383862365475060688899 16797575793548212591033349)
          ·
            refine ⟨3149545461290289860818753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16797575793548212591033349 3149545461290289860818753)
            ·
              refine ⟨2362159095967717395614065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149545461290289860818753 2362159095967717395614065)
              ·
                refine ⟨1771619321975788046710549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362159095967717395614065 1771619321975788046710549)
                ·
                  refine ⟨83044655717615064689557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1771619321975788046710549 83044655717615064689557)
                  ·
                    rfl

theorem cell22_727780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_727780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727780 prefixEnd_727780 := by exact prefixLift 727780
  have htrace : WordTrace (prefixWord ++ tailWord_727780) baseStart_727780 baseEnd_727780 := by
    simpa [prefixWord, tailWord_727780, baseEnd_727780] using wordTrace_append hprefix tailTrace_727780
  have hstable : (prefixWord ++ tailWord_727780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727780).length < 2 ^ (prefixWord ++ tailWord_727780).sum := by decide
  have hdescent : baseEnd_727780 < baseStart_727780 := by decide
  rcases family_descends (prefixWord ++ tailWord_727780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727812 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_727812 : Nat := 118140960795 + 727812 * 2 ^ 59
def prefixEnd_727812 : Nat := 4983230072969 + 3 ^ 40 * 727812 * 2
def baseEnd_727812 : Nat := 249144921406807777268573

theorem tailTrace_727812 : CollatzResearch.WordTrace tailWord_727812 prefixEnd_727812 249144921406807777268573 := by
  unfold tailWord_727812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13272742219634449619324845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17696989626179266159099793 13272742219634449619324845)
  ·
    refine ⟨4977278332362918607246817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13272742219634449619324845 4977278332362918607246817)
    ·
      refine ⟨3732958749272188955435113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4977278332362918607246817 3732958749272188955435113)
      ·
        refine ⟨2799719061954141716576335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3732958749272188955435113 2799719061954141716576335)
        ·
          refine ⟨4199578592931212574864503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799719061954141716576335 4199578592931212574864503)
          ·
            refine ⟨6299367889396818862296755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199578592931212574864503 6299367889396818862296755)
            ·
              refine ⟨9449051834095228293445133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299367889396818862296755 9449051834095228293445133)
              ·
                refine ⟨3543394437785710610041925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9449051834095228293445133 3543394437785710610041925)
                ·
                  refine ⟨664386457084820739382861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3543394437785710610041925 664386457084820739382861)
                  ·
                    refine ⟨249144921406807777268573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664386457084820739382861 249144921406807777268573)
                    ·
                      rfl

theorem cell22_727812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_727812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727812 prefixEnd_727812 := by exact prefixLift 727812
  have htrace : WordTrace (prefixWord ++ tailWord_727812) baseStart_727812 baseEnd_727812 := by
    simpa [prefixWord, tailWord_727812, baseEnd_727812] using wordTrace_append hprefix tailTrace_727812
  have hstable : (prefixWord ++ tailWord_727812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727812).length < 2 ^ (prefixWord ++ tailWord_727812).sum := by decide
  have hdescent : baseEnd_727812 < baseStart_727812 := by decide
  rcases family_descends (prefixWord ++ tailWord_727812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727844 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_727844 : Nat := 118140960795 + 727844 * 2 ^ 59
def prefixEnd_727844 : Nat := 4983230072969 + 3 ^ 40 * 727844 * 2
def baseEnd_727844 : Nat := 249155875660770360468475

theorem tailTrace_727844 : CollatzResearch.WordTrace tailWord_727844 prefixEnd_727844 249155875660770360468475 := by
  unfold tailWord_727844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273325787576484351907293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17697767716768645802543057 13273325787576484351907293)
  ·
    refine ⟨4977497170341181631965235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13273325787576484351907293 4977497170341181631965235)
    ·
      refine ⟨7466245755511772447947853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977497170341181631965235 7466245755511772447947853)
      ·
        refine ⟨2799842158316914667980445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7466245755511772447947853 2799842158316914667980445)
        ·
          refine ⟨1049940809368843000492667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2799842158316914667980445 1049940809368843000492667)
          ·
            refine ⟨1574911214053264500739001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049940809368843000492667 1574911214053264500739001)
            ·
              refine ⟨1181183410539948375554251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574911214053264500739001 1181183410539948375554251)
              ·
                refine ⟨1771775115809922563331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181183410539948375554251 1771775115809922563331377)
                ·
                  refine ⟨1328831336857441922498533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1771775115809922563331377 1328831336857441922498533)
                  ·
                    refine ⟨249155875660770360468475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328831336857441922498533 249155875660770360468475)
                    ·
                      rfl

theorem cell22_727844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_727844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727844 prefixEnd_727844 := by exact prefixLift 727844
  have htrace : WordTrace (prefixWord ++ tailWord_727844) baseStart_727844 baseEnd_727844 := by
    simpa [prefixWord, tailWord_727844, baseEnd_727844] using wordTrace_append hprefix tailTrace_727844
  have hstable : (prefixWord ++ tailWord_727844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727844).length < 2 ^ (prefixWord ++ tailWord_727844).sum := by decide
  have hdescent : baseEnd_727844 < baseStart_727844 := by decide
  rcases family_descends (prefixWord ++ tailWord_727844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727876 : List Nat := [2, 3, 4, 2, 1, 2, 1, 7]
def baseStart_727876 : Nat := 118140960795 + 727876 * 2 ^ 59
def prefixEnd_727876 : Nat := 4983230072969 + 3 ^ 40 * 727876 * 2
def baseEnd_727876 : Nat := 27685203323859215963153

theorem tailTrace_727876 : CollatzResearch.WordTrace tailWord_727876 prefixEnd_727876 27685203323859215963153 := by
  unfold tailWord_727876
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273909355518519084489741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17698545807358025445986321 13273909355518519084489741)
  ·
    refine ⟨4977716008319444656683653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13273909355518519084489741 4977716008319444656683653)
    ·
      refine ⟨933321751559895873128185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4977716008319444656683653 933321751559895873128185)
      ·
        refine ⟨699991313669921904846139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933321751559895873128185 699991313669921904846139)
        ·
          refine ⟨1049986970504882857269209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699991313669921904846139 1049986970504882857269209)
          ·
            refine ⟨787490227878662142951907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049986970504882857269209 787490227878662142951907)
            ·
              refine ⟨1181235341817993214427861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787490227878662142951907 1181235341817993214427861)
              ·
                refine ⟨27685203323859215963153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1181235341817993214427861 27685203323859215963153)
                ·
                  rfl

theorem cell22_727876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_727876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727876 prefixEnd_727876 := by exact prefixLift 727876
  have htrace : WordTrace (prefixWord ++ tailWord_727876) baseStart_727876 baseEnd_727876 := by
    simpa [prefixWord, tailWord_727876, baseEnd_727876] using wordTrace_append hprefix tailTrace_727876
  have hstable : (prefixWord ++ tailWord_727876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727876).length < 2 ^ (prefixWord ++ tailWord_727876).sum := by decide
  have hdescent : baseEnd_727876 < baseStart_727876 := by decide
  rcases family_descends (prefixWord ++ tailWord_727876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727947 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 1, 5]
def baseStart_727947 : Nat := 118140960795 + 727947 * 2 ^ 59
def prefixEnd_727947 : Nat := 4983230072969 + 3 ^ 40 * 727947 * 2
def baseEnd_727947 : Nat := 249191134665712425143159

theorem tailTrace_727947 : CollatzResearch.WordTrace tailWord_727947 prefixEnd_727947 249191134665712425143159 := by
  unfold tailWord_727947
  simp only [CollatzResearch.WordTrace]
  refine ⟨26550408293779817294814095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17700272195853211529876063 26550408293779817294814095)
  ·
    refine ⟨39825612440669725942221143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26550408293779817294814095 39825612440669725942221143)
    ·
      refine ⟨59738418661004588913331715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39825612440669725942221143 59738418661004588913331715)
      ·
        refine ⟨89607627991506883369997573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59738418661004588913331715 89607627991506883369997573)
        ·
          refine ⟨16801430248407540631874545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89607627991506883369997573 16801430248407540631874545)
          ·
            refine ⟨12601072686305655473905909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16801430248407540631874545 12601072686305655473905909)
            ·
              refine ⟨1181350564341155200678679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12601072686305655473905909 1181350564341155200678679)
              ·
                refine ⟨1772025846511732801018019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181350564341155200678679 1772025846511732801018019)
                ·
                  refine ⟨2658038769767599201527029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772025846511732801018019 2658038769767599201527029)
                  ·
                    refine ⟨249191134665712425143159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2658038769767599201527029 249191134665712425143159)
                    ·
                      rfl

theorem cell22_727947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_727947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727947 prefixEnd_727947 := by exact prefixLift 727947
  have htrace : WordTrace (prefixWord ++ tailWord_727947) baseStart_727947 baseEnd_727947 := by
    simpa [prefixWord, tailWord_727947, baseEnd_727947] using wordTrace_append hprefix tailTrace_727947
  have hstable : (prefixWord ++ tailWord_727947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727947).length < 2 ^ (prefixWord ++ tailWord_727947).sum := by decide
  have hdescent : baseEnd_727947 < baseStart_727947 := by decide
  rcases family_descends (prefixWord ++ tailWord_727947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728039 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 5]
def baseStart_728039 : Nat := 118140960795 + 728039 * 2 ^ 59
def prefixEnd_728039 : Nat := 4983230072969 + 3 ^ 40 * 728039 * 2
def baseEnd_728039 : Nat := 83074209381951617280959

theorem tailTrace_728039 : CollatzResearch.WordTrace tailWord_728039 prefixEnd_728039 83074209381951617280959 := by
  unfold tailWord_728039
  simp only [CollatzResearch.WordTrace]
  refine ⟨26553763809446517007163171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17702509206297678004775447 26553763809446517007163171)
  ·
    refine ⟨39830645714169775510744757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26553763809446517007163171 39830645714169775510744757)
    ·
      refine ⟨3734123035703416454132321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39830645714169775510744757 3734123035703416454132321)
      ·
        refine ⟨2800592276777562340599241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3734123035703416454132321 2800592276777562340599241)
        ·
          refine ⟨2100444207583171755449431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800592276777562340599241 2100444207583171755449431)
          ·
            refine ⟨3150666311374757633174147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100444207583171755449431 3150666311374757633174147)
            ·
              refine ⟨4725999467062136449761221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150666311374757633174147 4725999467062136449761221)
              ·
                refine ⟨886124900074150584330229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4725999467062136449761221 886124900074150584330229)
                ·
                  refine ⟨83074209381951617280959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 886124900074150584330229 83074209381951617280959)
                  ·
                    rfl

theorem cell22_728039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 5].length) (baseStart_728039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728039 prefixEnd_728039 := by exact prefixLift 728039
  have htrace : WordTrace (prefixWord ++ tailWord_728039) baseStart_728039 baseEnd_728039 := by
    simpa [prefixWord, tailWord_728039, baseEnd_728039] using wordTrace_append hprefix tailTrace_728039
  have hstable : (prefixWord ++ tailWord_728039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728039).length < 2 ^ (prefixWord ++ tailWord_728039).sum := by decide
  have hdescent : baseEnd_728039 < baseStart_728039 := by decide
  rcases family_descends (prefixWord ++ tailWord_728039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728054 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_728054 : Nat := 118140960795 + 728054 * 2 ^ 59
def prefixEnd_728054 : Nat := 4983230072969 + 3 ^ 40 * 728054 * 2
def baseEnd_728054 : Nat := 249227762952399812717831

theorem tailTrace_728054 : CollatzResearch.WordTrace tailWord_728054 prefixEnd_728054 249227762952399812717831 := by
  unfold tailWord_728054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659644431524510910559951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17702873936261449712639477 1659644431524510910559951)
  ·
    refine ⟨2489466647286766365839927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1659644431524510910559951 2489466647286766365839927)
    ·
      refine ⟨3734199970930149548759891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2489466647286766365839927 3734199970930149548759891)
      ·
        refine ⟨5601299956395224323139837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734199970930149548759891 5601299956395224323139837)
        ·
          refine ⟨2100487483648209121177439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5601299956395224323139837 2100487483648209121177439)
          ·
            refine ⟨3150731225472313681766159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100487483648209121177439 3150731225472313681766159)
            ·
              refine ⟨4726096838208470522649239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150731225472313681766159 4726096838208470522649239)
              ·
                refine ⟨7089145257312705783973859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726096838208470522649239 7089145257312705783973859)
                ·
                  refine ⟨10633717885969058675960789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7089145257312705783973859 10633717885969058675960789)
                  ·
                    refine ⟨249227762952399812717831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10633717885969058675960789 249227762952399812717831)
                    ·
                      rfl

theorem cell22_728054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_728054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728054 prefixEnd_728054 := by exact prefixLift 728054
  have htrace : WordTrace (prefixWord ++ tailWord_728054) baseStart_728054 baseEnd_728054 := by
    simpa [prefixWord, tailWord_728054, baseEnd_728054] using wordTrace_append hprefix tailTrace_728054
  have hstable : (prefixWord ++ tailWord_728054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728054).length < 2 ^ (prefixWord ++ tailWord_728054).sum := by decide
  have hdescent : baseEnd_728054 < baseStart_728054 := by decide
  rcases family_descends (prefixWord ++ tailWord_728054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728069 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_728069 : Nat := 118140960795 + 728069 * 2 ^ 59
def prefixEnd_728069 : Nat := 4983230072969 + 3 ^ 40 * 728069 * 2
def baseEnd_728069 : Nat := 249232897758944773592785

theorem tailTrace_728069 : CollatzResearch.WordTrace tailWord_728069 prefixEnd_728069 249232897758944773592785 := by
  unfold tailWord_728069
  simp only [CollatzResearch.WordTrace]
  refine ⟨26554857999337832130755261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17703238666225221420503507 26554857999337832130755261)
  ·
    refine ⟨9958071749751687049033223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26554857999337832130755261 9958071749751687049033223)
    ·
      refine ⟨14937107624627530573549835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958071749751687049033223 14937107624627530573549835)
      ·
        refine ⟨22405661436941295860324753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937107624627530573549835 22405661436941295860324753)
        ·
          refine ⟨16804246077705971895243565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22405661436941295860324753 16804246077705971895243565)
          ·
            refine ⟨6301592279139739460716337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16804246077705971895243565 6301592279139739460716337)
            ·
              refine ⟨4726194209354804595537253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301592279139739460716337 4726194209354804595537253)
              ·
                refine ⟨886161414254025861663235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4726194209354804595537253 886161414254025861663235)
                ·
                  refine ⟨1329242121381038792494853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886161414254025861663235 1329242121381038792494853)
                  ·
                    refine ⟨249232897758944773592785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1329242121381038792494853 249232897758944773592785)
                    ·
                      rfl

theorem cell22_728069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_728069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728069 prefixEnd_728069 := by exact prefixLift 728069
  have htrace : WordTrace (prefixWord ++ tailWord_728069) baseStart_728069 baseEnd_728069 := by
    simpa [prefixWord, tailWord_728069, baseEnd_728069] using wordTrace_append hprefix tailTrace_728069
  have hstable : (prefixWord ++ tailWord_728069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728069).length < 2 ^ (prefixWord ++ tailWord_728069).sum := by decide
  have hdescent : baseEnd_728069 < baseStart_728069 := by decide
  rcases family_descends (prefixWord ++ tailWord_728069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728112 : List Nat := [2, 1, 1, 1, 2, 4, 2, 9]
def baseStart_728112 : Nat := 118140960795 + 728112 * 2 ^ 59
def prefixEnd_728112 : Nat := 4983230072969 + 3 ^ 40 * 728112 * 2
def baseEnd_728112 : Nat := 27694179726411888307517

theorem tailTrace_728112 : CollatzResearch.WordTrace tailWord_728112 prefixEnd_728112 27694179726411888307517 := by
  unfold tailWord_728112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278213169091025237285295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17704284225454700316380393 13278213169091025237285295)
  ·
    refine ⟨19917319753636537855927943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13278213169091025237285295 19917319753636537855927943)
    ·
      refine ⟨29875979630454806783891915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19917319753636537855927943 29875979630454806783891915)
      ·
        refine ⟨44813969445682210175837873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29875979630454806783891915 44813969445682210175837873)
        ·
          refine ⟨33610477084261657631878405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44813969445682210175837873 33610477084261657631878405)
          ·
            refine ⟨6301964453299060805977201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33610477084261657631878405 6301964453299060805977201)
            ·
              refine ⟨4726473339974295604482901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301964453299060805977201 4726473339974295604482901)
              ·
                refine ⟨27694179726411888307517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4726473339974295604482901 27694179726411888307517)
                ·
                  rfl

theorem cell22_728112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_728112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728112 prefixEnd_728112 := by exact prefixLift 728112
  have htrace : WordTrace (prefixWord ++ tailWord_728112) baseStart_728112 baseEnd_728112 := by
    simpa [prefixWord, tailWord_728112, baseEnd_728112] using wordTrace_append hprefix tailTrace_728112
  have hstable : (prefixWord ++ tailWord_728112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728112).length < 2 ^ (prefixWord ++ tailWord_728112).sum := by decide
  have hdescent : baseEnd_728112 < baseStart_728112 := by decide
  rcases family_descends (prefixWord ++ tailWord_728112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728127 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_728127 : Nat := 118140960795 + 728127 * 2 ^ 59
def prefixEnd_728127 : Nat := 4983230072969 + 3 ^ 40 * 728127 * 2
def baseEnd_728127 : Nat := 249252752344251955642607

theorem tailTrace_728127 : CollatzResearch.WordTrace tailWord_728127 prefixEnd_728127 249252752344251955642607 := by
  unfold tailWord_728127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556973433127708036366635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17704648955418472024244423 26556973433127708036366635)
  ·
    refine ⟨39835460149691562054549953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26556973433127708036366635 39835460149691562054549953)
    ·
      refine ⟨29876595112268671540912465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39835460149691562054549953 29876595112268671540912465)
      ·
        refine ⟨22407446334201503655684349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29876595112268671540912465 22407446334201503655684349)
        ·
          refine ⟨8402792375325563870881631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22407446334201503655684349 8402792375325563870881631)
          ·
            refine ⟨12604188562988345806322447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8402792375325563870881631 12604188562988345806322447)
            ·
              refine ⟨18906282844482518709483671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12604188562988345806322447 18906282844482518709483671)
              ·
                refine ⟨28359424266723778064225507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18906282844482518709483671 28359424266723778064225507)
                ·
                  refine ⟨42539136400085667096338261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28359424266723778064225507 42539136400085667096338261)
                  ·
                    refine ⟨249252752344251955642607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42539136400085667096338261 249252752344251955642607)
                    ·
                      rfl

theorem cell22_728127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_728127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728127 prefixEnd_728127 := by exact prefixLift 728127
  have htrace : WordTrace (prefixWord ++ tailWord_728127) baseStart_728127 baseEnd_728127 := by
    simpa [prefixWord, tailWord_728127, baseEnd_728127] using wordTrace_append hprefix tailTrace_728127
  have hstable : (prefixWord ++ tailWord_728127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728127).length < 2 ^ (prefixWord ++ tailWord_728127).sum := by decide
  have hdescent : baseEnd_728127 < baseStart_728127 := by decide
  rcases family_descends (prefixWord ++ tailWord_728127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728144 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_728144 : Nat := 118140960795 + 728144 * 2 ^ 59
def prefixEnd_728144 : Nat := 4983230072969 + 3 ^ 40 * 728144 * 2
def baseEnd_728144 : Nat := 249258571791669577967555

theorem tailTrace_728144 : CollatzResearch.WordTrace tailWord_728144 prefixEnd_728144 249258571791669577967555 := by
  unfold tailWord_728144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278796737033059969867743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17705062316044079959823657 13278796737033059969867743)
  ·
    refine ⟨19918195105549589954801615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13278796737033059969867743 19918195105549589954801615)
    ·
      refine ⟨29877292658324384932202423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19918195105549589954801615 29877292658324384932202423)
      ·
        refine ⟨44815938987486577398303635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29877292658324384932202423 44815938987486577398303635)
        ·
          refine ⟨67223908481229866097455453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44815938987486577398303635 67223908481229866097455453)
          ·
            refine ⟨25208965680461199786545795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67223908481229866097455453 25208965680461199786545795)
            ·
              refine ⟨37813448520691799679818693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25208965680461199786545795 37813448520691799679818693)
              ·
                refine ⟨7090021597629712439966005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37813448520691799679818693 7090021597629712439966005)
                ·
                  refine ⟨664689524777785541246813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7090021597629712439966005 664689524777785541246813)
                  ·
                    refine ⟨249258571791669577967555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664689524777785541246813 249258571791669577967555)
                    ·
                      rfl

theorem cell22_728144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_728144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728144 prefixEnd_728144 := by exact prefixLift 728144
  have htrace : WordTrace (prefixWord ++ tailWord_728144) baseStart_728144 baseEnd_728144 := by
    simpa [prefixWord, tailWord_728144, baseEnd_728144] using wordTrace_append hprefix tailTrace_728144
  have hstable : (prefixWord ++ tailWord_728144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728144).length < 2 ^ (prefixWord ++ tailWord_728144).sum := by decide
  have hdescent : baseEnd_728144 < baseStart_728144 := by decide
  rcases family_descends (prefixWord ++ tailWord_728144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728161 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_728161 : Nat := 118140960795 + 728161 * 2 ^ 59
def prefixEnd_728161 : Nat := 4983230072969 + 3 ^ 40 * 728161 * 2
def baseEnd_728161 : Nat := 249264391239087200292503

theorem tailTrace_728161 : CollatzResearch.WordTrace tailWord_728161 prefixEnd_728161 249264391239087200292503 := by
  unfold tailWord_728161
  simp only [CollatzResearch.WordTrace]
  refine ⟨26558213515004531843104337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17705475676669687895402891 26558213515004531843104337)
  ·
    refine ⟨19918660136253398882328253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26558213515004531843104337 19918660136253398882328253)
    ·
      refine ⟨7469497551095024580873095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19918660136253398882328253 7469497551095024580873095)
      ·
        refine ⟨11204246326642536871309643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469497551095024580873095 11204246326642536871309643)
        ·
          refine ⟨16806369489963805306964465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11204246326642536871309643 16806369489963805306964465)
          ·
            refine ⟨12604777117472853980223349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16806369489963805306964465 12604777117472853980223349)
            ·
              refine ⟨1181697854763080060645939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12604777117472853980223349 1181697854763080060645939)
              ·
                refine ⟨1772546782144620090968909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181697854763080060645939 1772546782144620090968909)
                ·
                  refine ⟨664705043304232534113341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1772546782144620090968909 664705043304232534113341)
                  ·
                    refine ⟨249264391239087200292503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664705043304232534113341 249264391239087200292503)
                    ·
                      rfl

theorem cell22_728161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_728161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728161 prefixEnd_728161 := by exact prefixLift 728161
  have htrace : WordTrace (prefixWord ++ tailWord_728161) baseStart_728161 baseEnd_728161 := by
    simpa [prefixWord, tailWord_728161, baseEnd_728161] using wordTrace_append hprefix tailTrace_728161
  have hstable : (prefixWord ++ tailWord_728161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728161).length < 2 ^ (prefixWord ++ tailWord_728161).sum := by decide
  have hdescent : baseEnd_728161 < baseStart_728161 := by decide
  rcases family_descends (prefixWord ++ tailWord_728161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728285 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_728285 : Nat := 118140960795 + 728285 * 2 ^ 59
def prefixEnd_728285 : Nat := 4983230072969 + 3 ^ 40 * 728285 * 2
def baseEnd_728285 : Nat := 249306838973192210192123

theorem tailTrace_728285 : CollatzResearch.WordTrace tailWord_728285 prefixEnd_728285 249306838973192210192123 := by
  unfold tailWord_728285
  simp only [CollatzResearch.WordTrace]
  refine ⟨26562736166555301020618309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17708490777703534013745539 26562736166555301020618309)
  ·
    refine ⟨4980513031229118941365933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26562736166555301020618309 4980513031229118941365933)
    ·
      refine ⟨1867692386710919603012225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4980513031229118941365933 1867692386710919603012225)
      ·
        refine ⟨1400769290033189702259169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867692386710919603012225 1400769290033189702259169)
        ·
          refine ⟨1050576967524892276694377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400769290033189702259169 1050576967524892276694377)
          ·
            refine ⟨787932725643669207520783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050576967524892276694377 787932725643669207520783)
            ·
              refine ⟨1181899088465503811281175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787932725643669207520783 1181899088465503811281175)
              ·
                refine ⟨1772848632698255716921763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181899088465503811281175 1772848632698255716921763)
                ·
                  refine ⟨2659272949047383575382645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772848632698255716921763 2659272949047383575382645)
                  ·
                    refine ⟨249306838973192210192123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2659272949047383575382645 249306838973192210192123)
                    ·
                      rfl

theorem cell22_728285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_728285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728285 prefixEnd_728285 := by exact prefixLift 728285
  have htrace : WordTrace (prefixWord ++ tailWord_728285) baseStart_728285 baseEnd_728285 := by
    simpa [prefixWord, tailWord_728285, baseEnd_728285] using wordTrace_append hprefix tailTrace_728285
  have hstable : (prefixWord ++ tailWord_728285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728285).length < 2 ^ (prefixWord ++ tailWord_728285).sum := by decide
  have hdescent : baseEnd_728285 < baseStart_728285 := by decide
  rcases family_descends (prefixWord ++ tailWord_728285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728298 : List Nat := [3, 1, 3, 1, 1, 5, 2, 6]
def baseStart_728298 : Nat := 118140960795 + 728298 * 2 ^ 59
def prefixEnd_728298 : Nat := 4983230072969 + 3 ^ 40 * 728298 * 2
def baseEnd_728298 : Nat := 27701254348762723290787

theorem tailTrace_728298 : CollatzResearch.WordTrace tailWord_728298 prefixEnd_728298 27701254348762723290787 := by
  unfold tailWord_728298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640802578877051060210387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17708806877005469493894365 6640802578877051060210387)
  ·
    refine ⟨9961203868315576590315581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640802578877051060210387 9961203868315576590315581)
    ·
      refine ⟨3735451450618341221368343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9961203868315576590315581 3735451450618341221368343)
      ·
        refine ⟨5603177175927511832052515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735451450618341221368343 5603177175927511832052515)
        ·
          refine ⟨8404765763891267748078773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603177175927511832052515 8404765763891267748078773)
          ·
            refine ⟨787946790364806351382385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8404765763891267748078773 787946790364806351382385)
            ·
              refine ⟨590960092773604763536789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787946790364806351382385 590960092773604763536789)
              ·
                refine ⟨27701254348762723290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 590960092773604763536789 27701254348762723290787)
                ·
                  rfl

theorem cell22_728298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_728298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728298 prefixEnd_728298 := by exact prefixLift 728298
  have htrace : WordTrace (prefixWord ++ tailWord_728298) baseStart_728298 baseEnd_728298 := by
    simpa [prefixWord, tailWord_728298, baseEnd_728298] using wordTrace_append hprefix tailTrace_728298
  have hstable : (prefixWord ++ tailWord_728298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728298).length < 2 ^ (prefixWord ++ tailWord_728298).sum := by decide
  have hdescent : baseEnd_728298 < baseStart_728298 := by decide
  rcases family_descends (prefixWord ++ tailWord_728298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728339 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_728339 : Nat := 118140960795 + 728339 * 2 ^ 59
def prefixEnd_728339 : Nat := 4983230072969 + 3 ^ 40 * 728339 * 2
def baseEnd_728339 : Nat := 249325324276754069341957

theorem tailTrace_728339 : CollatzResearch.WordTrace tailWord_728339 prefixEnd_728339 249325324276754069341957 := by
  unfold tailWord_728339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564705708359668243084071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17709803805573112162056047 26564705708359668243084071)
  ·
    refine ⟨39847058562539502364626107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26564705708359668243084071 39847058562539502364626107)
    ·
      refine ⟨59770587843809253546939161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39847058562539502364626107 59770587843809253546939161)
      ·
        refine ⟨44827940882856940160204371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59770587843809253546939161 44827940882856940160204371)
        ·
          refine ⟨67241911324285410240306557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44827940882856940160204371 67241911324285410240306557)
          ·
            refine ⟨25215716746607028840114959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67241911324285410240306557 25215716746607028840114959)
            ·
              refine ⟨37823575119910543260172439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25215716746607028840114959 37823575119910543260172439)
              ·
                refine ⟨56735362679865814890258659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37823575119910543260172439 56735362679865814890258659)
                ·
                  refine ⟨85103044019798722335387989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56735362679865814890258659 85103044019798722335387989)
                  ·
                    refine ⟨249325324276754069341957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 85103044019798722335387989 249325324276754069341957)
                    ·
                      rfl

theorem cell22_728339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_728339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728339 prefixEnd_728339 := by exact prefixLift 728339
  have htrace : WordTrace (prefixWord ++ tailWord_728339) baseStart_728339 baseEnd_728339 := by
    simpa [prefixWord, tailWord_728339, baseEnd_728339] using wordTrace_append hprefix tailTrace_728339
  have hstable : (prefixWord ++ tailWord_728339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728339).length < 2 ^ (prefixWord ++ tailWord_728339).sum := by decide
  have hdescent : baseEnd_728339 < baseStart_728339 := by decide
  rcases family_descends (prefixWord ++ tailWord_728339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728381 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_728381 : Nat := 118140960795 + 728381 * 2 ^ 59
def prefixEnd_728381 : Nat := 4983230072969 + 3 ^ 40 * 728381 * 2
def baseEnd_728381 : Nat := 249339701735079959791829

theorem tailTrace_728381 : CollatzResearch.WordTrace tailWord_728381 prefixEnd_728381 249339701735079959791829 := by
  unfold tailWord_728381
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566237574207509416112997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17710825049471672944075331 26566237574207509416112997)
  ·
    refine ⟨4981169545163908015521187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26566237574207509416112997 4981169545163908015521187)
    ·
      refine ⟨7471754317745862023281781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981169545163908015521187 7471754317745862023281781)
      ·
        refine ⟨700476967288674564682667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7471754317745862023281781 700476967288674564682667)
        ·
          refine ⟨1050715450933011847024001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700476967288674564682667 1050715450933011847024001)
          ·
            refine ⟨788036588199758885268001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050715450933011847024001 788036588199758885268001)
            ·
              refine ⟨591027441149819163951001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788036588199758885268001 591027441149819163951001)
              ·
                refine ⟨443270580862364372963251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591027441149819163951001 443270580862364372963251)
                ·
                  refine ⟨664905871293546559444877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443270580862364372963251 664905871293546559444877)
                  ·
                    refine ⟨249339701735079959791829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664905871293546559444877 249339701735079959791829)
                    ·
                      rfl

theorem cell22_728381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_728381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728381 prefixEnd_728381 := by exact prefixLift 728381
  have htrace : WordTrace (prefixWord ++ tailWord_728381) baseStart_728381 baseEnd_728381 := by
    simpa [prefixWord, tailWord_728381, baseEnd_728381] using wordTrace_append hprefix tailTrace_728381
  have hstable : (prefixWord ++ tailWord_728381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728381).length < 2 ^ (prefixWord ++ tailWord_728381).sum := by decide
  have hdescent : baseEnd_728381 < baseStart_728381 := by decide
  rcases family_descends (prefixWord ++ tailWord_728381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728401 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_728401 : Nat := 118140960795 + 728401 * 2 ^ 59
def prefixEnd_728401 : Nat := 4983230072969 + 3 ^ 40 * 728401 * 2
def baseEnd_728401 : Nat := 249346548143806574291767

theorem tailTrace_728401 : CollatzResearch.WordTrace tailWord_728401 prefixEnd_728401 249346548143806574291767 := by
  unfold tailWord_728401
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566967034135052831841057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17711311356090035221227371 26566967034135052831841057)
  ·
    refine ⟨19925225275601289623880793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26566967034135052831841057 19925225275601289623880793)
    ·
      refine ⟨14943918956700967217910595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19925225275601289623880793 14943918956700967217910595)
      ·
        refine ⟨22415878435051450826865893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14943918956700967217910595 22415878435051450826865893)
        ·
          refine ⟨4202977206572147030037355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22415878435051450826865893 4202977206572147030037355)
          ·
            refine ⟨6304465809858220545056033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202977206572147030037355 6304465809858220545056033)
            ·
              refine ⟨4728349357393665408792025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6304465809858220545056033 4728349357393665408792025)
              ·
                refine ⟨3546262018045249056594019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728349357393665408792025 3546262018045249056594019)
                ·
                  refine ⟨5319393027067873584891029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546262018045249056594019 5319393027067873584891029)
                  ·
                    refine ⟨249346548143806574291767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5319393027067873584891029 249346548143806574291767)
                    ·
                      rfl

theorem cell22_728401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_728401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728401 prefixEnd_728401 := by exact prefixLift 728401
  have htrace : WordTrace (prefixWord ++ tailWord_728401) baseStart_728401 baseEnd_728401 := by
    simpa [prefixWord, tailWord_728401, baseEnd_728401] using wordTrace_append hprefix tailTrace_728401
  have hstable : (prefixWord ++ tailWord_728401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728401).length < 2 ^ (prefixWord ++ tailWord_728401).sum := by decide
  have hdescent : baseEnd_728401 < baseStart_728401 := by decide
  rcases family_descends (prefixWord ++ tailWord_728401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728403 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 2, 3]
def baseStart_728403 : Nat := 118140960795 + 728403 * 2 ^ 59
def prefixEnd_728403 : Nat := 4983230072969 + 3 ^ 40 * 728403 * 2
def baseEnd_728403 : Nat := 249347232784679235741761

theorem tailTrace_728403 : CollatzResearch.WordTrace tailWord_728403 prefixEnd_728403 249347232784679235741761 := by
  unfold tailWord_728403
  simp only [CollatzResearch.WordTrace]
  refine ⟨26567039980127807173413863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17711359986751871448942575 26567039980127807173413863)
  ·
    refine ⟨39850559970191710760120795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26567039980127807173413863 39850559970191710760120795)
    ·
      refine ⟨59775839955287566140181193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39850559970191710760120795 59775839955287566140181193)
      ·
        refine ⟨44831879966465674605135895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59775839955287566140181193 44831879966465674605135895)
        ·
          refine ⟨67247819949698511907703843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44831879966465674605135895 67247819949698511907703843)
          ·
            refine ⟨100871729924547767861555765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67247819949698511907703843 100871729924547767861555765)
            ·
              refine ⟨9456724680426353237020853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100871729924547767861555765 9456724680426353237020853)
              ·
                refine ⟨886567938789970615970705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9456724680426353237020853 886567938789970615970705)
                ·
                  refine ⟨664925954092477961978029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 886567938789970615970705 664925954092477961978029)
                  ·
                    refine ⟨249347232784679235741761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664925954092477961978029 249347232784679235741761)
                    ·
                      rfl

theorem cell22_728403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3].length) (baseStart_728403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728403 prefixEnd_728403 := by exact prefixLift 728403
  have htrace : WordTrace (prefixWord ++ tailWord_728403) baseStart_728403 baseEnd_728403 := by
    simpa [prefixWord, tailWord_728403, baseEnd_728403] using wordTrace_append hprefix tailTrace_728403
  have hstable : (prefixWord ++ tailWord_728403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728403).length < 2 ^ (prefixWord ++ tailWord_728403).sum := by decide
  have hdescent : baseEnd_728403 < baseStart_728403 := by decide
  rcases family_descends (prefixWord ++ tailWord_728403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728418 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_728418 : Nat := 118140960795 + 728418 * 2 ^ 59
def prefixEnd_728418 : Nat := 4983230072969 + 3 ^ 40 * 728418 * 2
def baseEnd_728418 : Nat := 249352367591224196616715

theorem tailTrace_728418 : CollatzResearch.WordTrace tailWord_728418 prefixEnd_728418 249352367591224196616715 := by
  unfold tailWord_728418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641896768768366183802477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17711724716715643156806605 6641896768768366183802477)
  ·
    refine ⟨2490711288288137318925929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6641896768768366183802477 2490711288288137318925929)
    ·
      refine ⟨1868033466216102989194447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2490711288288137318925929 1868033466216102989194447)
      ·
        refine ⟨2802050199324154483791671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868033466216102989194447 2802050199324154483791671)
        ·
          refine ⟨4203075298986231725687507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802050199324154483791671 4203075298986231725687507)
          ·
            refine ⟨6304612948479347588531261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203075298986231725687507 6304612948479347588531261)
            ·
              refine ⟨2364229855679755345699223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6304612948479347588531261 2364229855679755345699223)
              ·
                refine ⟨3546344783519633018548835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364229855679755345699223 3546344783519633018548835)
                ·
                  refine ⟨5319517175279449527823253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546344783519633018548835 5319517175279449527823253)
                  ·
                    refine ⟨249352367591224196616715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5319517175279449527823253 249352367591224196616715)
                    ·
                      rfl

theorem cell22_728418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_728418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728418 prefixEnd_728418 := by exact prefixLift 728418
  have htrace : WordTrace (prefixWord ++ tailWord_728418) baseStart_728418 baseEnd_728418 := by
    simpa [prefixWord, tailWord_728418, baseEnd_728418] using wordTrace_append hprefix tailTrace_728418
  have hstable : (prefixWord ++ tailWord_728418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728418).length < 2 ^ (prefixWord ++ tailWord_728418).sum := by decide
  have hdescent : baseEnd_728418 < baseStart_728418 := by decide
  rcases family_descends (prefixWord ++ tailWord_728418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728424 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_728424 : Nat := 118140960795 + 728424 * 2 ^ 59
def prefixEnd_728424 : Nat := 4983230072969 + 3 ^ 40 * 728424 * 2
def baseEnd_728424 : Nat := 249354421513842180966697

theorem tailTrace_728424 : CollatzResearch.WordTrace tailWord_728424 prefixEnd_728424 249354421513842180966697 := by
  unfold tailWord_728424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13283902956525863879964163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17711870608701151839952217 13283902956525863879964163)
  ·
    refine ⟨19925854434788795819946245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13283902956525863879964163 19925854434788795819946245)
    ·
      refine ⟨3736097706522899216239921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19925854434788795819946245 3736097706522899216239921)
      ·
        refine ⟨2802073279892174412179941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3736097706522899216239921 2802073279892174412179941)
        ·
          refine ⟨525388739979782702283739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2802073279892174412179941 525388739979782702283739)
          ·
            refine ⟨788083109969674053425609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525388739979782702283739 788083109969674053425609)
            ·
              refine ⟨591062332477255540069207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788083109969674053425609 591062332477255540069207)
              ·
                refine ⟨886593498715883310103811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591062332477255540069207 886593498715883310103811)
                ·
                  refine ⟨1329890248073824965155717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886593498715883310103811 1329890248073824965155717)
                  ·
                    refine ⟨249354421513842180966697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1329890248073824965155717 249354421513842180966697)
                    ·
                      rfl

theorem cell22_728424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_728424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728424 prefixEnd_728424 := by exact prefixLift 728424
  have htrace : WordTrace (prefixWord ++ tailWord_728424) baseStart_728424 baseEnd_728424 := by
    simpa [prefixWord, tailWord_728424, baseEnd_728424] using wordTrace_append hprefix tailTrace_728424
  have hstable : (prefixWord ++ tailWord_728424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728424).length < 2 ^ (prefixWord ++ tailWord_728424).sum := by decide
  have hdescent : baseEnd_728424 < baseStart_728424 := by decide
  rcases family_descends (prefixWord ++ tailWord_728424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728538 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_728538 : Nat := 118140960795 + 728538 * 2 ^ 59
def prefixEnd_728538 : Nat := 4983230072969 + 3 ^ 40 * 728538 * 2
def baseEnd_728538 : Nat := 249393446043583883616347

theorem tailTrace_728538 : CollatzResearch.WordTrace tailWord_728538 prefixEnd_728538 249393446043583883616347 := by
  unfold tailWord_728538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642990958659681307394567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17714642556425816819718845 6642990958659681307394567)
  ·
    refine ⟨9964486437989521961091851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6642990958659681307394567 9964486437989521961091851)
    ·
      refine ⟨14946729656984282941637777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9964486437989521961091851 14946729656984282941637777)
      ·
        refine ⟨11210047242738212206228333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14946729656984282941637777 11210047242738212206228333)
        ·
          refine ⟨4203767716026829577335625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11210047242738212206228333 4203767716026829577335625)
          ·
            refine ⟨3152825787020122183001719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4203767716026829577335625 3152825787020122183001719)
            ·
              refine ⟨4729238680530183274502579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152825787020122183001719 4729238680530183274502579)
              ·
                refine ⟨7093858020795274911753869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729238680530183274502579 7093858020795274911753869)
                ·
                  refine ⟨2660196757798228091907701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7093858020795274911753869 2660196757798228091907701)
                  ·
                    refine ⟨249393446043583883616347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2660196757798228091907701 249393446043583883616347)
                    ·
                      rfl

theorem cell22_728538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_728538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728538 prefixEnd_728538 := by exact prefixLift 728538
  have htrace : WordTrace (prefixWord ++ tailWord_728538) baseStart_728538 baseEnd_728538 := by
    simpa [prefixWord, tailWord_728538, baseEnd_728538] using wordTrace_append hprefix tailTrace_728538
  have hstable : (prefixWord ++ tailWord_728538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728538).length < 2 ^ (prefixWord ++ tailWord_728538).sum := by decide
  have hdescent : baseEnd_728538 < baseStart_728538 := by decide
  rcases family_descends (prefixWord ++ tailWord_728538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728568 : List Nat := [2, 1, 2, 1, 1, 5, 3, 7]
def baseStart_728568 : Nat := 118140960795 + 728568 * 2 ^ 59
def prefixEnd_728568 : Nat := 4983230072969 + 3 ^ 40 * 728568 * 2
def baseEnd_728568 : Nat := 27711523961852645040695

theorem tailTrace_728568 : CollatzResearch.WordTrace tailWord_728568 prefixEnd_728568 27711523961852645040695 := by
  unfold tailWord_728568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286529012265020176585179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17715372016353360235446905 13286529012265020176585179)
  ·
    refine ⟨19929793518397530264877769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13286529012265020176585179 19929793518397530264877769)
    ·
      refine ⟨14947345138798147698658327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19929793518397530264877769 14947345138798147698658327)
      ·
        refine ⟨22421017708197221547987491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14947345138798147698658327 22421017708197221547987491)
        ·
          refine ⟨33631526562295832321981237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22421017708197221547987491 33631526562295832321981237)
          ·
            refine ⟨3152955615215234280185741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33631526562295832321981237 3152955615215234280185741)
            ·
              refine ⟨1182358355705712855069653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3152955615215234280185741 1182358355705712855069653)
              ·
                refine ⟨27711523961852645040695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1182358355705712855069653 27711523961852645040695)
                ·
                  rfl

theorem cell22_728568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_728568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728568 prefixEnd_728568 := by exact prefixLift 728568
  have htrace : WordTrace (prefixWord ++ tailWord_728568) baseStart_728568 baseEnd_728568 := by
    simpa [prefixWord, tailWord_728568, baseEnd_728568] using wordTrace_append hprefix tailTrace_728568
  have hstable : (prefixWord ++ tailWord_728568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728568).length < 2 ^ (prefixWord ++ tailWord_728568).sum := by decide
  have hdescent : baseEnd_728568 < baseStart_728568 := by decide
  rcases family_descends (prefixWord ++ tailWord_728568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728587 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 2, 4]
def baseStart_728587 : Nat := 118140960795 + 728587 * 2 ^ 59
def prefixEnd_728587 : Nat := 4983230072969 + 3 ^ 40 * 728587 * 2
def baseEnd_728587 : Nat := 249410219744964089141197

theorem tailTrace_728587 : CollatzResearch.WordTrace tailWord_728587 prefixEnd_728587 249410219744964089141197 := by
  unfold tailWord_728587
  simp only [CollatzResearch.WordTrace]
  refine ⟨26573751011461206598112015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17715834007640804398741343 26573751011461206598112015)
  ·
    refine ⟨39860626517191809897168023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26573751011461206598112015 39860626517191809897168023)
    ·
      refine ⟨59790939775787714845752035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39860626517191809897168023 59790939775787714845752035)
      ·
        refine ⟨89686409663681572268628053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59790939775787714845752035 89686409663681572268628053)
        ·
          refine ⟨1051012613246268425022985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 89686409663681572268628053 1051012613246268425022985)
          ·
            refine ⟨788259459934701318767239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051012613246268425022985 788259459934701318767239)
            ·
              refine ⟨1182389189902051978150859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788259459934701318767239 1182389189902051978150859)
              ·
                refine ⟨1773583784853077967226289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182389189902051978150859 1773583784853077967226289)
                ·
                  refine ⟨1330187838639808475419717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1773583784853077967226289 1330187838639808475419717)
                  ·
                    refine ⟨249410219744964089141197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330187838639808475419717 249410219744964089141197)
                    ·
                      rfl

theorem cell22_728587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4].length) (baseStart_728587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728587 prefixEnd_728587 := by exact prefixLift 728587
  have htrace : WordTrace (prefixWord ++ tailWord_728587) baseStart_728587 baseEnd_728587 := by
    simpa [prefixWord, tailWord_728587, baseEnd_728587] using wordTrace_append hprefix tailTrace_728587
  have hstable : (prefixWord ++ tailWord_728587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728587).length < 2 ^ (prefixWord ++ tailWord_728587).sum := by decide
  have hdescent : baseEnd_728587 < baseStart_728587 := by decide
  rcases family_descends (prefixWord ++ tailWord_728587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728675 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 6]
def baseStart_728675 : Nat := 118140960795 + 728675 * 2 ^ 59
def prefixEnd_728675 : Nat := 4983230072969 + 3 ^ 40 * 728675 * 2
def baseEnd_728675 : Nat := 83146781314453730980309

theorem tailTrace_728675 : CollatzResearch.WordTrace tailWord_728675 prefixEnd_728675 83146781314453730980309 := by
  unfold tailWord_728675
  simp only [CollatzResearch.WordTrace]
  refine ⟨26576960635142397627315479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17717973756761598418210319 26576960635142397627315479)
  ·
    refine ⟨39865440952713596440973219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26576960635142397627315479 39865440952713596440973219)
    ·
      refine ⟨59798161429070394661459829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39865440952713596440973219 59798161429070394661459829)
      ·
        refine ⟨5606077633975349499511859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59798161429070394661459829 5606077633975349499511859)
        ·
          refine ⟨8409116450963024249267789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5606077633975349499511859 8409116450963024249267789)
          ·
            refine ⟨3153418669111134093475421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8409116450963024249267789 3153418669111134093475421)
            ·
              refine ⟨1182532000916675285053283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3153418669111134093475421 1182532000916675285053283)
              ·
                refine ⟨1773798001375012927579925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182532000916675285053283 1773798001375012927579925)
                ·
                  refine ⟨83146781314453730980309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1773798001375012927579925 83146781314453730980309)
                  ·
                    rfl

theorem cell22_728675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 6].length) (baseStart_728675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728675 prefixEnd_728675 := by exact prefixLift 728675
  have htrace : WordTrace (prefixWord ++ tailWord_728675) baseStart_728675 baseEnd_728675 := by
    simpa [prefixWord, tailWord_728675, baseEnd_728675] using wordTrace_append hprefix tailTrace_728675
  have hstable : (prefixWord ++ tailWord_728675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728675).length < 2 ^ (prefixWord ++ tailWord_728675).sum := by decide
  have hdescent : baseEnd_728675 < baseStart_728675 := by decide
  rcases family_descends (prefixWord ++ tailWord_728675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728694 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_728694 : Nat := 118140960795 + 728694 * 2 ^ 59
def prefixEnd_728694 : Nat := 4983230072969 + 3 ^ 40 * 728694 * 2
def baseEnd_728694 : Nat := 249446848031651476715869

theorem tailTrace_728694 : CollatzResearch.WordTrace tailWord_728694 prefixEnd_728694 249446848031651476715869 := by
  unfold tailWord_728694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661103351379597742016071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17718435748049042581504757 1661103351379597742016071)
  ·
    refine ⟨2491655027069396613024107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1661103351379597742016071 2491655027069396613024107)
    ·
      refine ⟨3737482540604094919536161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491655027069396613024107 3737482540604094919536161)
      ·
        refine ⟨2803111905453071189652121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737482540604094919536161 2803111905453071189652121)
        ·
          refine ⟨2102333929089803392239091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803111905453071189652121 2102333929089803392239091)
          ·
            refine ⟨3153500893634705088358637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102333929089803392239091 3153500893634705088358637)
            ·
              refine ⟨1182562835113014408134489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3153500893634705088358637 1182562835113014408134489)
              ·
                refine ⟨886922126334760806100867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182562835113014408134489 886922126334760806100867)
                ·
                  refine ⟨1330383189502141209151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886922126334760806100867 1330383189502141209151301)
                  ·
                    refine ⟨249446848031651476715869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330383189502141209151301 249446848031651476715869)
                    ·
                      rfl

theorem cell22_728694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_728694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728694 prefixEnd_728694 := by exact prefixLift 728694
  have htrace : WordTrace (prefixWord ++ tailWord_728694) baseStart_728694 baseEnd_728694 := by
    simpa [prefixWord, tailWord_728694, baseEnd_728694] using wordTrace_append hprefix tailTrace_728694
  have hstable : (prefixWord ++ tailWord_728694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728694).length < 2 ^ (prefixWord ++ tailWord_728694).sum := by decide
  have hdescent : baseEnd_728694 < baseStart_728694 := by decide
  rcases family_descends (prefixWord ++ tailWord_728694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728737 : List Nat := [1, 2, 3, 3, 2, 3, 1, 7]
def baseStart_728737 : Nat := 118140960795 + 728737 * 2 ^ 59
def prefixEnd_728737 : Nat := 4983230072969 + 3 ^ 40 * 728737 * 2
def baseEnd_728737 : Nat := 27717951978934855321193

theorem tailTrace_728737 : CollatzResearch.WordTrace tailWord_728737 prefixEnd_728737 27717951978934855321193 := by
  unfold tailWord_728737
  simp only [CollatzResearch.WordTrace]
  refine ⟨26579221960917782216072465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17719481307278521477381643 26579221960917782216072465)
  ·
    refine ⟨19934416470688336662054349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26579221960917782216072465 19934416470688336662054349)
    ·
      refine ⟨7475406176508126248270381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19934416470688336662054349 7475406176508126248270381)
      ·
        refine ⟨2803277316190547343101393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7475406176508126248270381 2803277316190547343101393)
        ·
          refine ⟨2102457987142910507326045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803277316190547343101393 2102457987142910507326045)
          ·
            refine ⟨788421745178591440247267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2102457987142910507326045 788421745178591440247267)
            ·
              refine ⟨1182632617767887160370901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788421745178591440247267 1182632617767887160370901)
              ·
                refine ⟨27717951978934855321193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1182632617767887160370901 27717951978934855321193)
                ·
                  rfl

theorem cell22_728737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 7].length) (baseStart_728737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728737 prefixEnd_728737 := by exact prefixLift 728737
  have htrace : WordTrace (prefixWord ++ tailWord_728737) baseStart_728737 baseEnd_728737 := by
    simpa [prefixWord, tailWord_728737, baseEnd_728737] using wordTrace_append hprefix tailTrace_728737
  have hstable : (prefixWord ++ tailWord_728737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728737).length < 2 ^ (prefixWord ++ tailWord_728737).sum := by decide
  have hdescent : baseEnd_728737 < baseStart_728737 := by decide
  rcases family_descends (prefixWord ++ tailWord_728737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728765 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 7]
def baseStart_728765 : Nat := 118140960795 + 728765 * 2 ^ 59
def prefixEnd_728765 : Nat := 4983230072969 + 3 ^ 40 * 728765 * 2
def baseEnd_728765 : Nat := 83157050927543652730217

theorem tailTrace_728765 : CollatzResearch.WordTrace tailWord_728765 prefixEnd_728765 83157050927543652730217 := by
  unfold tailWord_728765
  simp only [CollatzResearch.WordTrace]
  refine ⟨26580243204816342998091749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17720162136544228665394499 26580243204816342998091749)
  ·
    refine ⟨4983795600903064312142203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26580243204816342998091749 4983795600903064312142203)
    ·
      refine ⟨7475693401354596468213305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4983795600903064312142203 7475693401354596468213305)
      ·
        refine ⟨5606770051015947351159979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7475693401354596468213305 5606770051015947351159979)
        ·
          refine ⟨8410155076523921026739969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5606770051015947351159979 8410155076523921026739969)
          ·
            refine ⟨6307616307392940770054977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8410155076523921026739969 6307616307392940770054977)
            ·
              refine ⟨4730712230544705577541233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6307616307392940770054977 4730712230544705577541233)
              ·
                refine ⟨3548034172908529183155925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4730712230544705577541233 3548034172908529183155925)
                ·
                  refine ⟨83157050927543652730217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3548034172908529183155925 83157050927543652730217)
                  ·
                    rfl

theorem cell22_728765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_728765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728765 prefixEnd_728765 := by exact prefixLift 728765
  have htrace : WordTrace (prefixWord ++ tailWord_728765) baseStart_728765 baseEnd_728765 := by
    simpa [prefixWord, tailWord_728765, baseEnd_728765] using wordTrace_append hprefix tailTrace_728765
  have hstable : (prefixWord ++ tailWord_728765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728765).length < 2 ^ (prefixWord ++ tailWord_728765).sum := by decide
  have hdescent : baseEnd_728765 < baseStart_728765 := by decide
  rcases family_descends (prefixWord ++ tailWord_728765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728786 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_728786 : Nat := 118140960795 + 728786 * 2 ^ 59
def prefixEnd_728786 : Nat := 4983230072969 + 3 ^ 40 * 728786 * 2
def baseEnd_728786 : Nat := 249478341511793903415587

theorem tailTrace_728786 : CollatzResearch.WordTrace tailWord_728786 prefixEnd_728786 249478341511793903415587 := by
  unfold tailWord_728786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645252284435065896151553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17720672758493509056404141 6645252284435065896151553)
  ·
    refine ⟨4983939213326299422113665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6645252284435065896151553 4983939213326299422113665)
    ·
      refine ⟨3737954409994724566585249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4983939213326299422113665 3737954409994724566585249)
      ·
        refine ⟨2803465807496043424938937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737954409994724566585249 2803465807496043424938937)
        ·
          refine ⟨2102599355622032568704203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803465807496043424938937 2102599355622032568704203)
          ·
            refine ⟨3153899033433048853056305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102599355622032568704203 3153899033433048853056305)
            ·
              refine ⟨2365424275074786639792229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153899033433048853056305 2365424275074786639792229)
              ·
                refine ⟨443517051576522494961043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2365424275074786639792229 443517051576522494961043)
                ·
                  refine ⟨665275577364783742441565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443517051576522494961043 665275577364783742441565)
                  ·
                    refine ⟨249478341511793903415587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665275577364783742441565 249478341511793903415587)
                    ·
                      rfl

theorem cell22_728786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_728786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728786 prefixEnd_728786 := by exact prefixLift 728786
  have htrace : WordTrace (prefixWord ++ tailWord_728786) baseStart_728786 baseEnd_728786 := by
    simpa [prefixWord, tailWord_728786, baseEnd_728786] using wordTrace_append hprefix tailTrace_728786
  have hstable : (prefixWord ++ tailWord_728786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728786).length < 2 ^ (prefixWord ++ tailWord_728786).sum := by decide
  have hdescent : baseEnd_728786 < baseStart_728786 := by decide
  rcases family_descends (prefixWord ++ tailWord_728786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728812 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_728812 : Nat := 118140960795 + 728812 * 2 ^ 59
def prefixEnd_728812 : Nat := 4983230072969 + 3 ^ 40 * 728812 * 2
def baseEnd_728812 : Nat := 249487241843138502265507

theorem tailTrace_728812 : CollatzResearch.WordTrace tailWord_728812 prefixEnd_728812 249487241843138502265507 := by
  unfold tailWord_728812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290978717823035012526345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17721304957097380016701793 13290978717823035012526345)
  ·
    refine ⟨9968234038367276259394759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13290978717823035012526345 9968234038367276259394759)
    ·
      refine ⟨14952351057550914389092139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968234038367276259394759 14952351057550914389092139)
      ·
        refine ⟨22428526586326371583638209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14952351057550914389092139 22428526586326371583638209)
        ·
          refine ⟨16821394939744778687728657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22428526586326371583638209 16821394939744778687728657)
          ·
            refine ⟨12616046204808584015796493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16821394939744778687728657 12616046204808584015796493)
            ·
              refine ⟨4731017326803219005923685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12616046204808584015796493 4731017326803219005923685)
              ·
                refine ⟨887065748775603563610691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4731017326803219005923685 887065748775603563610691)
                ·
                  refine ⟨1330598623163405345416037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887065748775603563610691 1330598623163405345416037)
                  ·
                    refine ⟨249487241843138502265507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330598623163405345416037 249487241843138502265507)
                    ·
                      rfl

theorem cell22_728812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_728812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728812 prefixEnd_728812 := by exact prefixLift 728812
  have htrace : WordTrace (prefixWord ++ tailWord_728812) baseStart_728812 baseEnd_728812 := by
    simpa [prefixWord, tailWord_728812, baseEnd_728812] using wordTrace_append hprefix tailTrace_728812
  have hstable : (prefixWord ++ tailWord_728812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728812).length < 2 ^ (prefixWord ++ tailWord_728812).sum := by decide
  have hdescent : baseEnd_728812 < baseStart_728812 := by decide
  rcases family_descends (prefixWord ++ tailWord_728812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728820 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_728820 : Nat := 118140960795 + 728820 * 2 ^ 59
def prefixEnd_728820 : Nat := 4983230072969 + 3 ^ 40 * 728820 * 2
def baseEnd_728820 : Nat := 249489980406629148065483

theorem tailTrace_728820 : CollatzResearch.WordTrace tailWord_728820 prefixEnd_728820 249489980406629148065483 := by
  unfold tailWord_728820
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291124609808543695671957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17721499479744724927562609 13291124609808543695671957)
  ·
    refine ⟨623021466084775485734623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13291124609808543695671957 623021466084775485734623)
    ·
      refine ⟨934532199127163228601935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623021466084775485734623 934532199127163228601935)
      ·
        refine ⟨1401798298690744842902903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934532199127163228601935 1401798298690744842902903)
        ·
          refine ⟨2102697448036117264354355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401798298690744842902903 2102697448036117264354355)
          ·
            refine ⟨3154046172054175896531533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102697448036117264354355 3154046172054175896531533)
            ·
              refine ⟨1182767314520315961199325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3154046172054175896531533 1182767314520315961199325)
              ·
                refine ⟨443537742945118485449747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182767314520315961199325 443537742945118485449747)
                ·
                  refine ⟨665306614417677728174621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443537742945118485449747 665306614417677728174621)
                  ·
                    refine ⟨249489980406629148065483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665306614417677728174621 249489980406629148065483)
                    ·
                      rfl

theorem cell22_728820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_728820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728820 prefixEnd_728820 := by exact prefixLift 728820
  have htrace : WordTrace (prefixWord ++ tailWord_728820) baseStart_728820 baseEnd_728820 := by
    simpa [prefixWord, tailWord_728820, baseEnd_728820] using wordTrace_append hprefix tailTrace_728820
  have hstable : (prefixWord ++ tailWord_728820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728820).length < 2 ^ (prefixWord ++ tailWord_728820).sum := by decide
  have hdescent : baseEnd_728820 < baseStart_728820 := by decide
  rcases family_descends (prefixWord ++ tailWord_728820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 4]
def baseStart_728827 : Nat := 118140960795 + 728827 * 2 ^ 59
def prefixEnd_728827 : Nat := 4983230072969 + 3 ^ 40 * 728827 * 2
def baseEnd_728827 : Nat := 83164125549894487713487

theorem tailTrace_728827 : CollatzResearch.WordTrace tailWord_728827 prefixEnd_728827 83164125549894487713487 := by
  unfold tailWord_728827
  simp only [CollatzResearch.WordTrace]
  refine ⟨26582504530591727586848735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17721669687061151724565823 26582504530591727586848735)
  ·
    refine ⟨39873756795887591380273103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26582504530591727586848735 39873756795887591380273103)
    ·
      refine ⟨59810635193831387070409655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39873756795887591380273103 59810635193831387070409655)
      ·
        refine ⟨89715952790747080605614483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59810635193831387070409655 89715952790747080605614483)
        ·
          refine ⟨134573929186120620908421725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89715952790747080605614483 134573929186120620908421725)
          ·
            refine ⟨50465223444795232840658147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134573929186120620908421725 50465223444795232840658147)
            ·
              refine ⟨75697835167192849260987221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50465223444795232840658147 75697835167192849260987221)
              ·
                refine ⟨443542002932770601138597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 75697835167192849260987221 443542002932770601138597)
                ·
                  refine ⟨83164125549894487713487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443542002932770601138597 83164125549894487713487)
                  ·
                    rfl

theorem cell22_728827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 4].length) (baseStart_728827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728827 prefixEnd_728827 := by exact prefixLift 728827
  have htrace : WordTrace (prefixWord ++ tailWord_728827) baseStart_728827 baseEnd_728827 := by
    simpa [prefixWord, tailWord_728827, baseEnd_728827] using wordTrace_append hprefix tailTrace_728827
  have hstable : (prefixWord ++ tailWord_728827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728827).length < 2 ^ (prefixWord ++ tailWord_728827).sum := by decide
  have hdescent : baseEnd_728827 < baseStart_728827 := by decide
  rcases family_descends (prefixWord ++ tailWord_728827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728872 : List Nat := [2, 1, 5, 1, 1, 2, 2, 8]
def baseStart_728872 : Nat := 118140960795 + 728872 * 2 ^ 59
def prefixEnd_728872 : Nat := 4983230072969 + 3 ^ 40 * 728872 * 2
def baseEnd_728872 : Nat := 27723086785479816196147

theorem tailTrace_728872 : CollatzResearch.WordTrace tailWord_728872 prefixEnd_728872 27723086785479816196147 := by
  unfold tailWord_728872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292072907714350136118435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17722763876952466848157913 13292072907714350136118435)
  ·
    refine ⟨19938109361571525204177653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13292072907714350136118435 19938109361571525204177653)
    ·
      refine ⟨1869197752647330487891655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19938109361571525204177653 1869197752647330487891655)
      ·
        refine ⟨2803796628970995731837483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869197752647330487891655 2803796628970995731837483)
        ·
          refine ⟨4205694943456493597756225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803796628970995731837483 4205694943456493597756225)
          ·
            refine ⟨3154271207592370198317169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4205694943456493597756225 3154271207592370198317169)
            ·
              refine ⟨2365703405694277648737877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3154271207592370198317169 2365703405694277648737877)
              ·
                refine ⟨27723086785479816196147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2365703405694277648737877 27723086785479816196147)
                ·
                  rfl

theorem cell22_728872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_728872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728872 prefixEnd_728872 := by exact prefixLift 728872
  have htrace : WordTrace (prefixWord ++ tailWord_728872) baseStart_728872 baseEnd_728872 := by
    simpa [prefixWord, tailWord_728872, baseEnd_728872] using wordTrace_append hprefix tailTrace_728872
  have hstable : (prefixWord ++ tailWord_728872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728872).length < 2 ^ (prefixWord ++ tailWord_728872).sum := by decide
  have hdescent : baseEnd_728872 < baseStart_728872 := by decide
  rcases family_descends (prefixWord ++ tailWord_728872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728887 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 7, 3]
def baseStart_728887 : Nat := 118140960795 + 728887 * 2 ^ 59
def prefixEnd_728887 : Nat := 4983230072969 + 3 ^ 40 * 728887 * 2
def baseEnd_728887 : Nat := 249512915875863306640277

theorem tailTrace_728887 : CollatzResearch.WordTrace tailWord_728887 prefixEnd_728887 249512915875863306640277 := by
  unfold tailWord_728887
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584692910374357834032915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17723128606916238556021943 26584692910374357834032915)
  ·
    refine ⟨39877039365561536751049373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26584692910374357834032915 39877039365561536751049373)
    ·
      refine ⟨14953889762085576281643515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39877039365561536751049373 14953889762085576281643515)
      ·
        refine ⟨22430834643128364422465273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14953889762085576281643515 22430834643128364422465273)
        ·
          refine ⟨16823125982346273316848955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22430834643128364422465273 16823125982346273316848955)
          ·
            refine ⟨25234688973519409975273433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16823125982346273316848955 25234688973519409975273433)
            ·
              refine ⟨18926016730139557481455075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25234688973519409975273433 18926016730139557481455075)
              ·
                refine ⟨28389025095209336222182613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18926016730139557481455075 28389025095209336222182613)
                ·
                  refine ⟨665367775668968817707405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28389025095209336222182613 665367775668968817707405)
                  ·
                    refine ⟨249512915875863306640277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665367775668968817707405 249512915875863306640277)
                    ·
                      rfl

theorem cell22_728887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_728887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728887 prefixEnd_728887 := by exact prefixLift 728887
  have htrace : WordTrace (prefixWord ++ tailWord_728887) baseStart_728887 baseEnd_728887 := by
    simpa [prefixWord, tailWord_728887, baseEnd_728887] using wordTrace_append hprefix tailTrace_728887
  have hstable : (prefixWord ++ tailWord_728887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728887).length < 2 ^ (prefixWord ++ tailWord_728887).sum := by decide
  have hdescent : baseEnd_728887 < baseStart_728887 := by decide
  rcases family_descends (prefixWord ++ tailWord_728887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728889 : List Nat := [1, 2, 1, 7, 2, 9]
def baseStart_728889 : Nat := 118140960795 + 728889 * 2 ^ 59
def prefixEnd_728889 : Nat := 4983230072969 + 3 ^ 40 * 728889 * 2
def baseEnd_728889 : Nat := 3080414821194271210991

theorem tailTrace_728889 : CollatzResearch.WordTrace tailWord_728889 prefixEnd_728889 3080414821194271210991 := by
  unfold tailWord_728889
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584765856367112175605721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17723177237578074783737147 26584765856367112175605721)
  ·
    refine ⟨19938574392275334131704291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26584765856367112175605721 19938574392275334131704291)
    ·
      refine ⟨29907861588413001197556437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19938574392275334131704291 29907861588413001197556437)
      ·
        refine ⟨700965505978429715567729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29907861588413001197556437 700965505978429715567729)
        ·
          refine ⟨525724129483822286675797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700965505978429715567729 525724129483822286675797)
          ·
            refine ⟨3080414821194271210991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 525724129483822286675797 3080414821194271210991)
            ·
              rfl

theorem cell22_728889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 9].length) (baseStart_728889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728889 prefixEnd_728889 := by exact prefixLift 728889
  have htrace : WordTrace (prefixWord ++ tailWord_728889) baseStart_728889 baseEnd_728889 := by
    simpa [prefixWord, tailWord_728889, baseEnd_728889] using wordTrace_append hprefix tailTrace_728889
  have hstable : (prefixWord ++ tailWord_728889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728889).length < 2 ^ (prefixWord ++ tailWord_728889).sum := by decide
  have hdescent : baseEnd_728889 < baseStart_728889 := by decide
  rcases family_descends (prefixWord ++ tailWord_728889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728996 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_728996 : Nat := 118140960795 + 728996 * 2 ^ 59
def prefixEnd_728996 : Nat := 4983230072969 + 3 ^ 40 * 728996 * 2
def baseEnd_728996 : Nat := 83183409601141118554981

theorem tailTrace_728996 : CollatzResearch.WordTrace tailWord_728996 prefixEnd_728996 83183409601141118554981 := by
  unfold tailWord_728996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294334233489734724875421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17725778977986312966500561 13294334233489734724875421)
  ·
    refine ⟨4985375337558650521828283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13294334233489734724875421 4985375337558650521828283)
    ·
      refine ⟨7478063006337975782742425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985375337558650521828283 7478063006337975782742425)
      ·
        refine ⟨5608547254753481837056819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7478063006337975782742425 5608547254753481837056819)
        ·
          refine ⟨8412820882130222755585229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608547254753481837056819 8412820882130222755585229)
          ·
            refine ⟨3154807830798833533344461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8412820882130222755585229 3154807830798833533344461)
            ·
              refine ⟨1183052936549562575004173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3154807830798833533344461 1183052936549562575004173)
              ·
                refine ⟨443644851206085965626565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183052936549562575004173 443644851206085965626565)
                ·
                  refine ⟨83183409601141118554981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443644851206085965626565 83183409601141118554981)
                  ·
                    rfl

theorem cell22_728996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_728996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_728996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_728996 prefixEnd_728996 := by exact prefixLift 728996
  have htrace : WordTrace (prefixWord ++ tailWord_728996) baseStart_728996 baseEnd_728996 := by
    simpa [prefixWord, tailWord_728996, baseEnd_728996] using wordTrace_append hprefix tailTrace_728996
  have hstable : (prefixWord ++ tailWord_728996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728996).length < 2 ^ (prefixWord ++ tailWord_728996).sum := by decide
  have hdescent : baseEnd_728996 < baseStart_728996 := by decide
  rcases family_descends (prefixWord ++ tailWord_728996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729009 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_729009 : Nat := 118140960795 + 729009 * 2 ^ 59
def prefixEnd_729009 : Nat := 4983230072969 + 3 ^ 40 * 729009 * 2
def baseEnd_729009 : Nat := 249554678969095655089903

theorem tailTrace_729009 : CollatzResearch.WordTrace tailWord_729009 prefixEnd_729009 249554678969095655089903 := by
  unfold tailWord_729009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26589142615932372669974081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17726095077288248446649387 26589142615932372669974081)
  ·
    refine ⟨19941856961949279502480561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26589142615932372669974081 19941856961949279502480561)
    ·
      refine ⟨14956392721461959626860421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19941856961949279502480561 14956392721461959626860421)
      ·
        refine ⟨2804323635274117430036329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14956392721461959626860421 2804323635274117430036329)
        ·
          refine ⟨2103242726455588072527247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2804323635274117430036329 2103242726455588072527247)
          ·
            refine ⟨3154864089683382108790871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103242726455588072527247 3154864089683382108790871)
            ·
              refine ⟨4732296134525073163186307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154864089683382108790871 4732296134525073163186307)
              ·
                refine ⟨7098444201787609744779461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732296134525073163186307 7098444201787609744779461)
                ·
                  refine ⟨1330958287835176827146149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7098444201787609744779461 1330958287835176827146149)
                  ·
                    refine ⟨249554678969095655089903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330958287835176827146149 249554678969095655089903)
                    ·
                      rfl

theorem cell22_729009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_729009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729009 prefixEnd_729009 := by exact prefixLift 729009
  have htrace : WordTrace (prefixWord ++ tailWord_729009) baseStart_729009 baseEnd_729009 := by
    simpa [prefixWord, tailWord_729009, baseEnd_729009] using wordTrace_append hprefix tailTrace_729009
  have hstable : (prefixWord ++ tailWord_729009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729009).length < 2 ^ (prefixWord ++ tailWord_729009).sum := by decide
  have hdescent : baseEnd_729009 < baseStart_729009 := by decide
  rcases family_descends (prefixWord ++ tailWord_729009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729013 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 4]
def baseStart_729013 : Nat := 118140960795 + 729013 * 2 ^ 59
def prefixEnd_729013 : Nat := 4983230072969 + 3 ^ 40 * 729013 * 2
def baseEnd_729013 : Nat := 83185349416946992663297

theorem tailTrace_729013 : CollatzResearch.WordTrace tailWord_729013 prefixEnd_729013 83185349416946992663297 := by
  unfold tailWord_729013
  simp only [CollatzResearch.WordTrace]
  refine ⟨26589288507917881353119693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17726192338611920902079795 26589288507917881353119693)
  ·
    refine ⟨9970983190469205507419885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26589288507917881353119693 9970983190469205507419885)
    ·
      refine ⟨3739118696425952065282457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9970983190469205507419885 3739118696425952065282457)
      ·
        refine ⟨2804339022319464048961843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3739118696425952065282457 2804339022319464048961843)
        ·
          refine ⟨4206508533479196073442765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804339022319464048961843 4206508533479196073442765)
          ·
            refine ⟨1577440700054698527541037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4206508533479196073442765 1577440700054698527541037)
            ·
              refine ⟨591540262520511947827889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1577440700054698527541037 591540262520511947827889)
              ·
                refine ⟨443655196890383960870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591540262520511947827889 443655196890383960870917)
                ·
                  refine ⟨83185349416946992663297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443655196890383960870917 83185349416946992663297)
                  ·
                    rfl

theorem cell22_729013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_729013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729013 prefixEnd_729013 := by exact prefixLift 729013
  have htrace : WordTrace (prefixWord ++ tailWord_729013) baseStart_729013 baseEnd_729013 := by
    simpa [prefixWord, tailWord_729013, baseEnd_729013] using wordTrace_append hprefix tailTrace_729013
  have hstable : (prefixWord ++ tailWord_729013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729013).length < 2 ^ (prefixWord ++ tailWord_729013).sum := by decide
  have hdescent : baseEnd_729013 < baseStart_729013 := by decide
  rcases family_descends (prefixWord ++ tailWord_729013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729039 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 5, 3]
def baseStart_729039 : Nat := 118140960795 + 729039 * 2 ^ 59
def prefixEnd_729039 : Nat := 4983230072969 + 3 ^ 40 * 729039 * 2
def baseEnd_729039 : Nat := 249564948582185576839811

theorem tailTrace_729039 : CollatzResearch.WordTrace tailWord_729039 prefixEnd_729039 249564948582185576839811 := by
  unfold tailWord_729039
  simp only [CollatzResearch.WordTrace]
  refine ⟨26590236805823687793566171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17726824537215791862377447 26590236805823687793566171)
  ·
    refine ⟨39885355208735531690349257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26590236805823687793566171 39885355208735531690349257)
    ·
      refine ⟨29914016406551648767761943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39885355208735531690349257 29914016406551648767761943)
      ·
        refine ⟨44871024609827473151642915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29914016406551648767761943 44871024609827473151642915)
        ·
          refine ⟨67306536914741209727464373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44871024609827473151642915 67306536914741209727464373)
          ·
            refine ⟨6309987835756988411949785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67306536914741209727464373 6309987835756988411949785)
            ·
              refine ⟨4732490876817741308962339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309987835756988411949785 4732490876817741308962339)
              ·
                refine ⟨7098736315226611963443509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732490876817741308962339 7098736315226611963443509)
                ·
                  refine ⟨665506529552494871572829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7098736315226611963443509 665506529552494871572829)
                  ·
                    refine ⟨249564948582185576839811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665506529552494871572829 249564948582185576839811)
                    ·
                      rfl

theorem cell22_729039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_729039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729039 prefixEnd_729039 := by exact prefixLift 729039
  have htrace : WordTrace (prefixWord ++ tailWord_729039) baseStart_729039 baseEnd_729039 := by
    simpa [prefixWord, tailWord_729039, baseEnd_729039] using wordTrace_append hprefix tailTrace_729039
  have hstable : (prefixWord ++ tailWord_729039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729039).length < 2 ^ (prefixWord ++ tailWord_729039).sum := by decide
  have hdescent : baseEnd_729039 < baseStart_729039 := by decide
  rcases family_descends (prefixWord ++ tailWord_729039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729067 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_729067 : Nat := 118140960795 + 729067 * 2 ^ 59
def prefixEnd_729067 : Nat := 4983230072969 + 3 ^ 40 * 729067 * 2
def baseEnd_729067 : Nat := 249574533554402837139725

theorem tailTrace_729067 : CollatzResearch.WordTrace tailWord_729067 prefixEnd_729067 249574533554402837139725 := by
  unfold tailWord_729067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26591258049722248575585455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17727505366481499050390303 26591258049722248575585455)
  ·
    refine ⟨39886887074583372863378183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26591258049722248575585455 39886887074583372863378183)
    ·
      refine ⟨59830330611875059295067275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39886887074583372863378183 59830330611875059295067275)
      ·
        refine ⟨89745495917812588942600913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59830330611875059295067275 89745495917812588942600913)
        ·
          refine ⟨67309121938359441706950685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89745495917812588942600913 67309121938359441706950685)
          ·
            refine ⟨25240920726884790640106507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67309121938359441706950685 25240920726884790640106507)
            ·
              refine ⟨37861381090327185960159761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25240920726884790640106507 37861381090327185960159761)
              ·
                refine ⟨28396035817745389470119821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37861381090327185960159761 28396035817745389470119821)
                ·
                  refine ⟨10648513431654521051294933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28396035817745389470119821 10648513431654521051294933)
                  ·
                    refine ⟨249574533554402837139725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10648513431654521051294933 249574533554402837139725)
                    ·
                      rfl

theorem cell22_729067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_729067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729067 prefixEnd_729067 := by exact prefixLift 729067
  have htrace : WordTrace (prefixWord ++ tailWord_729067) baseStart_729067 baseEnd_729067 := by
    simpa [prefixWord, tailWord_729067, baseEnd_729067] using wordTrace_append hprefix tailTrace_729067
  have hstable : (prefixWord ++ tailWord_729067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729067).length < 2 ^ (prefixWord ++ tailWord_729067).sum := by decide
  have hdescent : baseEnd_729067 < baseStart_729067 := by decide
  rcases family_descends (prefixWord ++ tailWord_729067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729084 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_729084 : Nat := 118140960795 + 729084 * 2 ^ 59
def prefixEnd_729084 : Nat := 4983230072969 + 3 ^ 40 * 729084 * 2
def baseEnd_729084 : Nat := 249580353001820459464673

theorem tailTrace_729084 : CollatzResearch.WordTrace tailWord_729084 prefixEnd_729084 249580353001820459464673 := by
  unfold tailWord_729084
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295939045330330239477153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17727918727107106985969537 13295939045330330239477153)
  ·
    refine ⟨9971954283997747679607865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13295939045330330239477153 9971954283997747679607865)
    ·
      refine ⟨7478965712998310759705899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9971954283997747679607865 7478965712998310759705899)
      ·
        refine ⟨11218448569497466139558849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7478965712998310759705899 11218448569497466139558849)
        ·
          refine ⟨8413836427123099604669137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11218448569497466139558849 8413836427123099604669137)
          ·
            refine ⟨6310377320342324703501853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8413836427123099604669137 6310377320342324703501853)
            ·
              refine ⟨2366391495128371763813195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6310377320342324703501853 2366391495128371763813195)
              ·
                refine ⟨3549587242692557645719793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366391495128371763813195 3549587242692557645719793)
                ·
                  refine ⟨2662190432019418234289845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549587242692557645719793 2662190432019418234289845)
                  ·
                    refine ⟨249580353001820459464673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2662190432019418234289845 249580353001820459464673)
                    ·
                      rfl

theorem cell22_729084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_729084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729084 prefixEnd_729084 := by exact prefixLift 729084
  have htrace : WordTrace (prefixWord ++ tailWord_729084) baseStart_729084 baseEnd_729084 := by
    simpa [prefixWord, tailWord_729084, baseEnd_729084] using wordTrace_append hprefix tailTrace_729084
  have hstable : (prefixWord ++ tailWord_729084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729084).length < 2 ^ (prefixWord ++ tailWord_729084).sum := by decide
  have hdescent : baseEnd_729084 < baseStart_729084 := by decide
  rcases family_descends (prefixWord ++ tailWord_729084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729094 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_729094 : Nat := 118140960795 + 729094 * 2 ^ 59
def prefixEnd_729094 : Nat := 4983230072969 + 3 ^ 40 * 729094 * 2
def baseEnd_729094 : Nat := 249583776206183766714643

theorem tailTrace_729094 : CollatzResearch.WordTrace tailWord_729094 prefixEnd_729094 249583776206183766714643 := by
  unfold tailWord_729094
  simp only [CollatzResearch.WordTrace]
  refine ⟨831007588144513505838073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17728161880416288124545557 831007588144513505838073)
  ·
    refine ⟨623255691108385129378555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831007588144513505838073 623255691108385129378555)
    ·
      refine ⟨934883536662577694067833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623255691108385129378555 934883536662577694067833)
      ·
        refine ⟨701162652496933270550875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 934883536662577694067833 701162652496933270550875)
        ·
          refine ⟨1051743978745399905826313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701162652496933270550875 1051743978745399905826313)
          ·
            refine ⟨788807984059049929369735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051743978745399905826313 788807984059049929369735)
            ·
              refine ⟨1183211976088574894054603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788807984059049929369735 1183211976088574894054603)
              ·
                refine ⟨1774817964132862341081905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183211976088574894054603 1774817964132862341081905)
                ·
                  refine ⟨1331113473099646755811429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1774817964132862341081905 1331113473099646755811429)
                  ·
                    refine ⟨249583776206183766714643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331113473099646755811429 249583776206183766714643)
                    ·
                      rfl

theorem cell22_729094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_729094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729094 prefixEnd_729094 := by exact prefixLift 729094
  have htrace : WordTrace (prefixWord ++ tailWord_729094) baseStart_729094 baseEnd_729094 := by
    simpa [prefixWord, tailWord_729094, baseEnd_729094] using wordTrace_append hprefix tailTrace_729094
  have hstable : (prefixWord ++ tailWord_729094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729094).length < 2 ^ (prefixWord ++ tailWord_729094).sum := by decide
  have hdescent : baseEnd_729094 < baseStart_729094 := by decide
  rcases family_descends (prefixWord ++ tailWord_729094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729099 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_729099 : Nat := 118140960795 + 729099 * 2 ^ 59
def prefixEnd_729099 : Nat := 4983230072969 + 3 ^ 40 * 729099 * 2
def baseEnd_729099 : Nat := 249585487808365420339627

theorem tailTrace_729099 : CollatzResearch.WordTrace tailWord_729099 prefixEnd_729099 249585487808365420339627 := by
  unfold tailWord_729099
  simp only [CollatzResearch.WordTrace]
  refine ⟨26592425185606318040750351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17728283457070878693833567 26592425185606318040750351)
  ·
    refine ⟨39888637778409477061125527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26592425185606318040750351 39888637778409477061125527)
    ·
      refine ⟨59832956667614215591688291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39888637778409477061125527 59832956667614215591688291)
      ·
        refine ⟨89749435001421323387532437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59832956667614215591688291 89749435001421323387532437)
        ·
          refine ⟨4207004765691624533790583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89749435001421323387532437 4207004765691624533790583)
          ·
            refine ⟨6310507148537436800685875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207004765691624533790583 6310507148537436800685875)
            ·
              refine ⟨9465760722806155201028813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310507148537436800685875 9465760722806155201028813)
              ·
                refine ⟨3549660271052308200385805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9465760722806155201028813 3549660271052308200385805)
                ·
                  refine ⟨1331122601644615575144677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3549660271052308200385805 1331122601644615575144677)
                  ·
                    refine ⟨249585487808365420339627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331122601644615575144677 249585487808365420339627)
                    ·
                      rfl

theorem cell22_729099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_729099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729099 prefixEnd_729099 := by exact prefixLift 729099
  have htrace : WordTrace (prefixWord ++ tailWord_729099) baseStart_729099 baseEnd_729099 := by
    simpa [prefixWord, tailWord_729099, baseEnd_729099] using wordTrace_append hprefix tailTrace_729099
  have hstable : (prefixWord ++ tailWord_729099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729099).length < 2 ^ (prefixWord ++ tailWord_729099).sum := by decide
  have hdescent : baseEnd_729099 < baseStart_729099 := by decide
  rcases family_descends (prefixWord ++ tailWord_729099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729150 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_729150 : Nat := 118140960795 + 729150 * 2 ^ 59
def prefixEnd_729150 : Nat := 4983230072969 + 3 ^ 40 * 729150 * 2
def baseEnd_729150 : Nat := 249602946150618287314471

theorem tailTrace_729150 : CollatzResearch.WordTrace tailWord_729150 prefixEnd_729150 249602946150618287314471 := by
  unfold tailWord_729150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324285663552694218857113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17729523538947702500571269 3324285663552694218857113)
  ·
    refine ⟨2493214247664520664142835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3324285663552694218857113 2493214247664520664142835)
    ·
      refine ⟨3739821371496780996214253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493214247664520664142835 3739821371496780996214253)
      ·
        refine ⟨1402433014311292873580345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3739821371496780996214253 1402433014311292873580345)
        ·
          refine ⟨1051824760733469655185259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402433014311292873580345 1051824760733469655185259)
          ·
            refine ⟨1577737141100204482777889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051824760733469655185259 1577737141100204482777889)
            ·
              refine ⟨1183302855825153362083417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577737141100204482777889 1183302855825153362083417)
              ·
                refine ⟨887477141868865021562563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183302855825153362083417 887477141868865021562563)
                ·
                  refine ⟨1331215712803297532343845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887477141868865021562563 1331215712803297532343845)
                  ·
                    refine ⟨249602946150618287314471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331215712803297532343845 249602946150618287314471)
                    ·
                      rfl

theorem cell22_729150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_729150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729150 prefixEnd_729150 := by exact prefixLift 729150
  have htrace : WordTrace (prefixWord ++ tailWord_729150) baseStart_729150 baseEnd_729150 := by
    simpa [prefixWord, tailWord_729150, baseEnd_729150] using wordTrace_append hprefix tailTrace_729150
  have hstable : (prefixWord ++ tailWord_729150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729150).length < 2 ^ (prefixWord ++ tailWord_729150).sum := by decide
  have hdescent : baseEnd_729150 < baseStart_729150 := by decide
  rcases family_descends (prefixWord ++ tailWord_729150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729159 : List Nat := [1, 1, 4, 1, 3, 1, 3, 8]
def baseStart_729159 : Nat := 118140960795 + 729159 * 2 ^ 59
def prefixEnd_729159 : Nat := 4983230072969 + 3 ^ 40 * 729159 * 2
def baseEnd_729159 : Nat := 27734003003838362648827

theorem tailTrace_729159 : CollatzResearch.WordTrace tailWord_729159 prefixEnd_729159 27734003003838362648827 := by
  unfold tailWord_729159
  simp only [CollatzResearch.WordTrace]
  refine ⟨26594613565388948287934531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17729742376925965525289687 26594613565388948287934531)
  ·
    refine ⟨39891920348083422431901797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26594613565388948287934531 39891920348083422431901797)
    ·
      refine ⟨7479735065265641705981587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39891920348083422431901797 7479735065265641705981587)
      ·
        refine ⟨11219602597898462558972381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7479735065265641705981587 11219602597898462558972381)
        ·
          refine ⟨4207350974211923459614643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11219602597898462558972381 4207350974211923459614643)
          ·
            refine ⟨6311026461317885189421965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207350974211923459614643 6311026461317885189421965)
            ·
              refine ⟨2366634922994206946033237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6311026461317885189421965 2366634922994206946033237)
              ·
                refine ⟨27734003003838362648827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2366634922994206946033237 27734003003838362648827)
                ·
                  rfl

theorem cell22_729159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 8].length) (baseStart_729159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729159 prefixEnd_729159 := by exact prefixLift 729159
  have htrace : WordTrace (prefixWord ++ tailWord_729159) baseStart_729159 baseEnd_729159 := by
    simpa [prefixWord, tailWord_729159, baseEnd_729159] using wordTrace_append hprefix tailTrace_729159
  have hstable : (prefixWord ++ tailWord_729159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729159).length < 2 ^ (prefixWord ++ tailWord_729159).sum := by decide
  have hdescent : baseEnd_729159 < baseStart_729159 := by decide
  rcases family_descends (prefixWord ++ tailWord_729159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729182 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_729182 : Nat := 118140960795 + 729182 * 2 ^ 59
def prefixEnd_729182 : Nat := 4983230072969 + 3 ^ 40 * 729182 * 2
def baseEnd_729182 : Nat := 83204633468193623504791

theorem tailTrace_729182 : CollatzResearch.WordTrace tailWord_729182 prefixEnd_729182 83204633468193623504791 := by
  unfold tailWord_729182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324431555538202902002725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17730301629537082144014533 3324431555538202902002725)
  ·
    refine ⟨623330916663413044125511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3324431555538202902002725 623330916663413044125511)
    ·
      refine ⟨934996374995119566188267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623330916663413044125511 934996374995119566188267)
      ·
        refine ⟨1402494562492679349282401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934996374995119566188267 1402494562492679349282401)
        ·
          refine ⟨1051870921869509511961801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402494562492679349282401 1051870921869509511961801)
          ·
            refine ⟨788903191402132133971351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051870921869509511961801 788903191402132133971351)
            ·
              refine ⟨1183354787103198200957027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788903191402132133971351 1183354787103198200957027)
              ·
                refine ⟨1775032180654797301435541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183354787103198200957027 1775032180654797301435541)
                ·
                  refine ⟨83204633468193623504791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1775032180654797301435541 83204633468193623504791)
                  ·
                    rfl

theorem cell22_729182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_729182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729182 prefixEnd_729182 := by exact prefixLift 729182
  have htrace : WordTrace (prefixWord ++ tailWord_729182) baseStart_729182 baseEnd_729182 := by
    simpa [prefixWord, tailWord_729182, baseEnd_729182] using wordTrace_append hprefix tailTrace_729182
  have hstable : (prefixWord ++ tailWord_729182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729182).length < 2 ^ (prefixWord ++ tailWord_729182).sum := by decide
  have hdescent : baseEnd_729182 < baseStart_729182 := by decide
  rcases family_descends (prefixWord ++ tailWord_729182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729242 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_729242 : Nat := 118140960795 + 729242 * 2 ^ 59
def prefixEnd_729242 : Nat := 4983230072969 + 3 ^ 40 * 729242 * 2
def baseEnd_729242 : Nat := 249634439630760714014189

theorem tailTrace_729242 : CollatzResearch.WordTrace tailWord_729242 prefixEnd_729242 249634439630760714014189 := by
  unfold tailWord_729242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649410206022063365801495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17731760549392168975470653 6649410206022063365801495)
  ·
    refine ⟨9974115309033095048702243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6649410206022063365801495 9974115309033095048702243)
    ·
      refine ⟨14961172963549642573053365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974115309033095048702243 14961172963549642573053365)
      ·
        refine ⟨1402609965332778991223753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14961172963549642573053365 1402609965332778991223753)
        ·
          refine ⟨1051957473999584243417815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402609965332778991223753 1051957473999584243417815)
          ·
            refine ⟨1577936210999376365126723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051957473999584243417815 1577936210999376365126723)
            ·
              refine ⟨2366904316499064547690085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577936210999376365126723 2366904316499064547690085)
              ·
                refine ⟨443794559343574602691891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2366904316499064547690085 443794559343574602691891)
                ·
                  refine ⟨665691839015361904037837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443794559343574602691891 665691839015361904037837)
                  ·
                    refine ⟨249634439630760714014189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665691839015361904037837 249634439630760714014189)
                    ·
                      rfl

theorem cell22_729242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_729242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729242 prefixEnd_729242 := by exact prefixLift 729242
  have htrace : WordTrace (prefixWord ++ tailWord_729242) baseStart_729242 baseEnd_729242 := by
    simpa [prefixWord, tailWord_729242, baseEnd_729242] using wordTrace_append hprefix tailTrace_729242
  have hstable : (prefixWord ++ tailWord_729242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729242).length < 2 ^ (prefixWord ++ tailWord_729242).sum := by decide
  have hdescent : baseEnd_729242 < baseStart_729242 := by decide
  rcases family_descends (prefixWord ++ tailWord_729242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729266 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_729266 : Nat := 118140960795 + 729266 * 2 ^ 59
def prefixEnd_729266 : Nat := 4983230072969 + 3 ^ 40 * 729266 * 2
def baseEnd_729266 : Nat := 83214218440410883804705

theorem tailTrace_729266 : CollatzResearch.WordTrace tailWord_729266 prefixEnd_729266 83214218440410883804705 := by
  unfold tailWord_729266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649629044000326390519913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17732344117334203708053101 6649629044000326390519913)
  ·
    refine ⟨4987221783000244792889935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6649629044000326390519913 4987221783000244792889935)
    ·
      refine ⟨7480832674500367189334903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4987221783000244792889935 7480832674500367189334903)
      ·
        refine ⟨11221249011750550784002355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480832674500367189334903 11221249011750550784002355)
        ·
          refine ⟨16831873517625826176003533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11221249011750550784002355 16831873517625826176003533)
          ·
            refine ⟨6311952569109684816001325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16831873517625826176003533 6311952569109684816001325)
            ·
              refine ⟨2366982213416131806000497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6311952569109684816001325 2366982213416131806000497)
              ·
                refine ⟨1775236660062098854500373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366982213416131806000497 1775236660062098854500373)
                ·
                  refine ⟨83214218440410883804705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1775236660062098854500373 83214218440410883804705)
                  ·
                    rfl

theorem cell22_729266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_729266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729266 prefixEnd_729266 := by exact prefixLift 729266
  have htrace : WordTrace (prefixWord ++ tailWord_729266) baseStart_729266 baseEnd_729266 := by
    simpa [prefixWord, tailWord_729266, baseEnd_729266] using wordTrace_append hprefix tailTrace_729266
  have hstable : (prefixWord ++ tailWord_729266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729266).length < 2 ^ (prefixWord ++ tailWord_729266).sum := by decide
  have hdescent : baseEnd_729266 < baseStart_729266 := by decide
  rcases family_descends (prefixWord ++ tailWord_729266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729326 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_729326 : Nat := 118140960795 + 729326 * 2 ^ 59
def prefixEnd_729326 : Nat := 4983230072969 + 3 ^ 40 * 729326 * 2
def baseEnd_729326 : Nat := 249663194547412494913931

theorem tailTrace_729326 : CollatzResearch.WordTrace tailWord_729326 prefixEnd_729326 249663194547412494913931 := by
  unfold tailWord_729326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325088069472991976157979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17733803037189290539509221 3325088069472991976157979)
  ·
    refine ⟨4987632104209487964236969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3325088069472991976157979 4987632104209487964236969)
    ·
      refine ⟨3740724078157115973177727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4987632104209487964236969 3740724078157115973177727)
      ·
        refine ⟨5611086117235673959766591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740724078157115973177727 5611086117235673959766591)
        ·
          refine ⟨8416629175853510939649887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611086117235673959766591 8416629175853510939649887)
          ·
            refine ⟨12624943763780266409474831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416629175853510939649887 12624943763780266409474831)
            ·
              refine ⟨18937415645670399614212247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12624943763780266409474831 18937415645670399614212247)
              ·
                refine ⟨28406123468505599421318371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18937415645670399614212247 28406123468505599421318371)
                ·
                  refine ⟨42609185202758399131977557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28406123468505599421318371 42609185202758399131977557)
                  ·
                    refine ⟨249663194547412494913931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42609185202758399131977557 249663194547412494913931)
                    ·
                      rfl

theorem cell22_729326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_729326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729326 prefixEnd_729326 := by exact prefixLift 729326
  have htrace : WordTrace (prefixWord ++ tailWord_729326) baseStart_729326 baseEnd_729326 := by
    simpa [prefixWord, tailWord_729326, baseEnd_729326] using wordTrace_append hprefix tailTrace_729326
  have hstable : (prefixWord ++ tailWord_729326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729326).length < 2 ^ (prefixWord ++ tailWord_729326).sum := by decide
  have hdescent : baseEnd_729326 < baseStart_729326 := by decide
  rcases family_descends (prefixWord ++ tailWord_729326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729356 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_729356 : Nat := 118140960795 + 729356 * 2 ^ 59
def prefixEnd_729356 : Nat := 4983230072969 + 3 ^ 40 * 729356 * 2
def baseEnd_729356 : Nat := 83224488053500805554613

theorem tailTrace_729356 : CollatzResearch.WordTrace tailWord_729356 prefixEnd_729356 83224488053500805554613 := by
  unfold tailWord_729356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13300899372837625466427961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17734532497116833955237281 13300899372837625466427961)
  ·
    refine ⟨9975674529628219099820971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13300899372837625466427961 9975674529628219099820971)
    ·
      refine ⟨14963511794442328649731457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975674529628219099820971 14963511794442328649731457)
      ·
        refine ⟨11222633845831746487298593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14963511794442328649731457 11222633845831746487298593)
        ·
          refine ⟨8416975384373809865473945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11222633845831746487298593 8416975384373809865473945)
          ·
            refine ⟨6312731538280357399105459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416975384373809865473945 6312731538280357399105459)
            ·
              refine ⟨9469097307420536098658189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312731538280357399105459 9469097307420536098658189)
              ·
                refine ⟨3550911490282701036996821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9469097307420536098658189 3550911490282701036996821)
                ·
                  refine ⟨83224488053500805554613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3550911490282701036996821 83224488053500805554613)
                  ·
                    rfl

theorem cell22_729356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_729356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729356 prefixEnd_729356 := by exact prefixLift 729356
  have htrace : WordTrace (prefixWord ++ tailWord_729356) baseStart_729356 baseEnd_729356 := by
    simpa [prefixWord, tailWord_729356, baseEnd_729356] using wordTrace_append hprefix tailTrace_729356
  have hstable : (prefixWord ++ tailWord_729356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729356).length < 2 ^ (prefixWord ++ tailWord_729356).sum := by decide
  have hdescent : baseEnd_729356 < baseStart_729356 := by decide
  rcases family_descends (prefixWord ++ tailWord_729356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729371 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_729371 : Nat := 118140960795 + 729371 * 2 ^ 59
def prefixEnd_729371 : Nat := 4983230072969 + 3 ^ 40 * 729371 * 2
def baseEnd_729371 : Nat := 249678598967047377538793

theorem tailTrace_729371 : CollatzResearch.WordTrace tailWord_729371 prefixEnd_729371 249678598967047377538793 := by
  unfold tailWord_729371
  simp only [CollatzResearch.WordTrace]
  refine ⟨26602345840620908494651967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17734897227080605663101311 26602345840620908494651967)
  ·
    refine ⟨39903518760931362741977951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26602345840620908494651967 39903518760931362741977951)
    ·
      refine ⟨59855278141397044112966927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39903518760931362741977951 59855278141397044112966927)
      ·
        refine ⟨89782917212095566169450391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59855278141397044112966927 89782917212095566169450391)
        ·
          refine ⟨134674375818143349254175587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89782917212095566169450391 134674375818143349254175587)
          ·
            refine ⟨202011563727215023881263381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134674375818143349254175587 202011563727215023881263381)
            ·
              refine ⟨9469292049713204244434221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202011563727215023881263381 9469292049713204244434221)
              ·
                refine ⟨3550984518642451591662833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9469292049713204244434221 3550984518642451591662833)
                ·
                  refine ⟨2663238388981838693747125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3550984518642451591662833 2663238388981838693747125)
                  ·
                    refine ⟨249678598967047377538793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2663238388981838693747125 249678598967047377538793)
                    ·
                      rfl

theorem cell22_729371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_729371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729371 prefixEnd_729371 := by exact prefixLift 729371
  have htrace : WordTrace (prefixWord ++ tailWord_729371) baseStart_729371 baseEnd_729371 := by
    simpa [prefixWord, tailWord_729371, baseEnd_729371] using wordTrace_append hprefix tailTrace_729371
  have hstable : (prefixWord ++ tailWord_729371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729371).length < 2 ^ (prefixWord ++ tailWord_729371).sum := by decide
  have hdescent : baseEnd_729371 < baseStart_729371 := by decide
  rcases family_descends (prefixWord ++ tailWord_729371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729433 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_729433 : Nat := 118140960795 + 729433 * 2 ^ 59
def prefixEnd_729433 : Nat := 4983230072969 + 3 ^ 40 * 729433 * 2
def baseEnd_729433 : Nat := 249699822834099882488603

theorem tailTrace_729433 : CollatzResearch.WordTrace tailWord_729433 prefixEnd_729433 249699822834099882488603 := by
  unfold tailWord_729433
  simp only [CollatzResearch.WordTrace]
  refine ⟨26604607166396293083408953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17736404777597528722272635 26604607166396293083408953)
  ·
    refine ⟨19953455374797219812556715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26604607166396293083408953 19953455374797219812556715)
    ·
      refine ⟨29930183062195829718835073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19953455374797219812556715 29930183062195829718835073)
      ·
        refine ⟨22447637296646872289126305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29930183062195829718835073 22447637296646872289126305)
        ·
          refine ⟨16835727972485154216844729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22447637296646872289126305 16835727972485154216844729)
          ·
            refine ⟨12626795979363865662633547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16835727972485154216844729 12626795979363865662633547)
            ·
              refine ⟨18940193969045798493950321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12626795979363865662633547 18940193969045798493950321)
              ·
                refine ⟨14205145476784348870462741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18940193969045798493950321 14205145476784348870462741)
                ·
                  refine ⟨665866194224266353302941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14205145476784348870462741 665866194224266353302941)
                  ·
                    refine ⟨249699822834099882488603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665866194224266353302941 249699822834099882488603)
                    ·
                      rfl

theorem cell22_729433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_729433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729433 prefixEnd_729433 := by exact prefixLift 729433
  have htrace : WordTrace (prefixWord ++ tailWord_729433) baseStart_729433 baseEnd_729433 := by
    simpa [prefixWord, tailWord_729433, baseEnd_729433] using wordTrace_append hprefix tailTrace_729433
  have hstable : (prefixWord ++ tailWord_729433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729433).length < 2 ^ (prefixWord ++ tailWord_729433).sum := by decide
  have hdescent : baseEnd_729433 < baseStart_729433 := by decide
  rcases family_descends (prefixWord ++ tailWord_729433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729450 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_729450 : Nat := 118140960795 + 729450 * 2 ^ 59
def prefixEnd_729450 : Nat := 4983230072969 + 3 ^ 40 * 729450 * 2
def baseEnd_729450 : Nat := 249705642281517504813551

theorem tailTrace_729450 : CollatzResearch.WordTrace tailWord_729450 prefixEnd_729450 249705642281517504813551 := by
  unfold tailWord_729450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651306801833676246694451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17736818138223136657851869 6651306801833676246694451)
  ·
    refine ⟨9976960202750514370041677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6651306801833676246694451 9976960202750514370041677)
    ·
      refine ⟨3741360076031442888765629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9976960202750514370041677 3741360076031442888765629)
      ·
        refine ⟨1403010028511791083287111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3741360076031442888765629 1403010028511791083287111)
        ·
          refine ⟨2104515042767686624930667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403010028511791083287111 2104515042767686624930667)
          ·
            refine ⟨3156772564151529937396001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104515042767686624930667 3156772564151529937396001)
            ·
              refine ⟨2367579423113647453047001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3156772564151529937396001 2367579423113647453047001)
              ·
                refine ⟨1775684567335235589785251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367579423113647453047001 1775684567335235589785251)
                ·
                  refine ⟨2663526851002853384677877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775684567335235589785251 2663526851002853384677877)
                  ·
                    refine ⟨249705642281517504813551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2663526851002853384677877 249705642281517504813551)
                    ·
                      rfl

theorem cell22_729450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_729450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729450 prefixEnd_729450 := by exact prefixLift 729450
  have htrace : WordTrace (prefixWord ++ tailWord_729450) baseStart_729450 baseEnd_729450 := by
    simpa [prefixWord, tailWord_729450, baseEnd_729450] using wordTrace_append hprefix tailTrace_729450
  have hstable : (prefixWord ++ tailWord_729450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729450).length < 2 ^ (prefixWord ++ tailWord_729450).sum := by decide
  have hdescent : baseEnd_729450 < baseStart_729450 := by decide
  rcases family_descends (prefixWord ++ tailWord_729450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729452 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_729452 : Nat := 118140960795 + 729452 * 2 ^ 59
def prefixEnd_729452 : Nat := 4983230072969 + 3 ^ 40 * 729452 * 2
def baseEnd_729452 : Nat := 83235442307463388754515

theorem tailTrace_729452 : CollatzResearch.WordTrace tailWord_729452 prefixEnd_729452 83235442307463388754515 := by
  unfold tailWord_729452
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302650076663729664175305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17736866768884972885567073 13302650076663729664175305)
  ·
    refine ⟨9976987557497797248131479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13302650076663729664175305 9976987557497797248131479)
    ·
      refine ⟨14965481336246695872197219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9976987557497797248131479 14965481336246695872197219)
      ·
        refine ⟨22448222004370043808295829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14965481336246695872197219 22448222004370043808295829)
        ·
          refine ⟨1052260406454845803513867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22448222004370043808295829 1052260406454845803513867)
          ·
            refine ⟨1578390609682268705270801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052260406454845803513867 1578390609682268705270801)
            ·
              refine ⟨1183792957261701528953101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1578390609682268705270801 1183792957261701528953101)
              ·
                refine ⟨443922358973138073357413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183792957261701528953101 443922358973138073357413)
                ·
                  refine ⟨83235442307463388754515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443922358973138073357413 83235442307463388754515)
                  ·
                    rfl

theorem cell22_729452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_729452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729452 prefixEnd_729452 := by exact prefixLift 729452
  have htrace : WordTrace (prefixWord ++ tailWord_729452) baseStart_729452 baseEnd_729452 := by
    simpa [prefixWord, tailWord_729452, baseEnd_729452] using wordTrace_append hprefix tailTrace_729452
  have hstable : (prefixWord ++ tailWord_729452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729452).length < 2 ^ (prefixWord ++ tailWord_729452).sum := by decide
  have hdescent : baseEnd_729452 < baseStart_729452 := by decide
  rcases family_descends (prefixWord ++ tailWord_729452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729467 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 2, 3]
def baseStart_729467 : Nat := 118140960795 + 729467 * 2 ^ 59
def prefixEnd_729467 : Nat := 4983230072969 + 3 ^ 40 * 729467 * 2
def baseEnd_729467 : Nat := 249711461728935127138499

theorem tailTrace_729467 : CollatzResearch.WordTrace tailWord_729467 prefixEnd_729467 249711461728935127138499 := by
  unfold tailWord_729467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26605847248273116890146655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17737231498848744593431103 26605847248273116890146655)
  ·
    refine ⟨39908770872409675335219983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26605847248273116890146655 39908770872409675335219983)
    ·
      refine ⟨59863156308614513002829975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39908770872409675335219983 59863156308614513002829975)
      ·
        refine ⟨89794734462921769504244963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59863156308614513002829975 89794734462921769504244963)
        ·
          refine ⟨134692101694382654256367445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89794734462921769504244963 134692101694382654256367445)
          ·
            refine ⟨789211533365523364783403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 134692101694382654256367445 789211533365523364783403)
            ·
              refine ⟨1183817300048285047175105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789211533365523364783403 1183817300048285047175105)
              ·
                refine ⟨887862975036213785381329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183817300048285047175105 887862975036213785381329)
                ·
                  refine ⟨665897231277160339035997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 887862975036213785381329 665897231277160339035997)
                  ·
                    refine ⟨249711461728935127138499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665897231277160339035997 249711461728935127138499)
                    ·
                      rfl

theorem cell22_729467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3].length) (baseStart_729467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729467 prefixEnd_729467 := by exact prefixLift 729467
  have htrace : WordTrace (prefixWord ++ tailWord_729467) baseStart_729467 baseEnd_729467 := by
    simpa [prefixWord, tailWord_729467, baseEnd_729467] using wordTrace_append hprefix tailTrace_729467
  have hstable : (prefixWord ++ tailWord_729467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729467).length < 2 ^ (prefixWord ++ tailWord_729467).sum := by decide
  have hdescent : baseEnd_729467 < baseStart_729467 := by decide
  rcases family_descends (prefixWord ++ tailWord_729467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729495 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 3, 3]
def baseStart_729495 : Nat := 118140960795 + 729495 * 2 ^ 59
def prefixEnd_729495 : Nat := 4983230072969 + 3 ^ 40 * 729495 * 2
def baseEnd_729495 : Nat := 249721046701152387438413

theorem tailTrace_729495 : CollatzResearch.WordTrace tailWord_729495 prefixEnd_729495 249721046701152387438413 := by
  unfold tailWord_729495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26606868492171677672165939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17737912328114451781443959 26606868492171677672165939)
  ·
    refine ⟨39910302738257516508248909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26606868492171677672165939 39910302738257516508248909)
    ·
      refine ⟨14966363526846568690593341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39910302738257516508248909 14966363526846568690593341)
      ·
        refine ⟨5612386322567463258972503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14966363526846568690593341 5612386322567463258972503)
        ·
          refine ⟨8418579483851194888458755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612386322567463258972503 8418579483851194888458755)
          ·
            refine ⟨12627869225776792332688133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418579483851194888458755 12627869225776792332688133)
            ·
              refine ⟨2367725479833148562379025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12627869225776792332688133 2367725479833148562379025)
              ·
                refine ⟨1775794109874861421784269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367725479833148562379025 1775794109874861421784269)
                ·
                  refine ⟨665922791203073033169101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1775794109874861421784269 665922791203073033169101)
                  ·
                    refine ⟨249721046701152387438413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665922791203073033169101 249721046701152387438413)
                    ·
                      rfl

theorem cell22_729495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_729495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729495 prefixEnd_729495 := by exact prefixLift 729495
  have htrace : WordTrace (prefixWord ++ tailWord_729495) baseStart_729495 baseEnd_729495 := by
    simpa [prefixWord, tailWord_729495, baseEnd_729495] using wordTrace_append hprefix tailTrace_729495
  have hstable : (prefixWord ++ tailWord_729495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729495).length < 2 ^ (prefixWord ++ tailWord_729495).sum := by decide
  have hdescent : baseEnd_729495 < baseStart_729495 := by decide
  rcases family_descends (prefixWord ++ tailWord_729495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729508 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_729508 : Nat := 118140960795 + 729508 * 2 ^ 59
def prefixEnd_729508 : Nat := 4983230072969 + 3 ^ 40 * 729508 * 2
def baseEnd_729508 : Nat := 83241832288941562287791

theorem tailTrace_729508 : CollatzResearch.WordTrace tailWord_729508 prefixEnd_729508 83241832288941562287791 := by
  unfold tailWord_729508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303671320562290446194589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17738228427416387261592785 13303671320562290446194589)
  ·
    refine ⟨4988876745210858917322971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13303671320562290446194589 4988876745210858917322971)
    ·
      refine ⟨7483315117816288375984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988876745210858917322971 7483315117816288375984457)
      ·
        refine ⟨5612486338362216281988343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7483315117816288375984457 5612486338362216281988343)
        ·
          refine ⟨8418729507543324422982515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612486338362216281988343 8418729507543324422982515)
          ·
            refine ⟨12628094261314986634473773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418729507543324422982515 12628094261314986634473773)
            ·
              refine ⟨4735535347993119987927665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12628094261314986634473773 4735535347993119987927665)
              ·
                refine ⟨3551651510994839990945749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735535347993119987927665 3551651510994839990945749)
                ·
                  refine ⟨83241832288941562287791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3551651510994839990945749 83241832288941562287791)
                  ·
                    rfl

theorem cell22_729508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_729508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729508 prefixEnd_729508 := by exact prefixLift 729508
  have htrace : WordTrace (prefixWord ++ tailWord_729508) baseStart_729508 baseEnd_729508 := by
    simpa [prefixWord, tailWord_729508, baseEnd_729508] using wordTrace_append hprefix tailTrace_729508
  have hstable : (prefixWord ++ tailWord_729508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729508).length < 2 ^ (prefixWord ++ tailWord_729508).sum := by decide
  have hdescent : baseEnd_729508 < baseStart_729508 := by decide
  rcases family_descends (prefixWord ++ tailWord_729508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729514 : List Nat := [3, 1, 6, 1, 1, 2, 8]
def baseStart_729514 : Nat := 118140960795 + 729514 * 2 ^ 59
def prefixEnd_729514 : Nat := 4983230072969 + 3 ^ 40 * 729514 * 2
def baseEnd_729514 : Nat := 9249168547757135970865

theorem tailTrace_729514 : CollatzResearch.WordTrace tailWord_729514 prefixEnd_729514 9249168547757135970865 := by
  unfold tailWord_729514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651890369775710979276899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17738374319401895944738397 6651890369775710979276899)
  ·
    refine ⟨9977835554663566468915349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6651890369775710979276899 9977835554663566468915349)
    ·
      refine ⟨467711041624854678230407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9977835554663566468915349 467711041624854678230407)
      ·
        refine ⟨701566562437282017345611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467711041624854678230407 701566562437282017345611)
        ·
          refine ⟨1052349843655923026018417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701566562437282017345611 1052349843655923026018417)
          ·
            refine ⟨789262382741942269513813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052349843655923026018417 789262382741942269513813)
            ·
              refine ⟨9249168547757135970865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 789262382741942269513813 9249168547757135970865)
              ·
                rfl

theorem cell22_729514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 8].length) (baseStart_729514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729514 prefixEnd_729514 := by exact prefixLift 729514
  have htrace : WordTrace (prefixWord ++ tailWord_729514) baseStart_729514 baseEnd_729514 := by
    simpa [prefixWord, tailWord_729514, baseEnd_729514] using wordTrace_append hprefix tailTrace_729514
  have hstable : (prefixWord ++ tailWord_729514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729514).length < 2 ^ (prefixWord ++ tailWord_729514).sum := by decide
  have hdescent : baseEnd_729514 < baseStart_729514 := by decide
  rcases family_descends (prefixWord ++ tailWord_729514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729553 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 6]
def baseStart_729553 : Nat := 118140960795 + 729553 * 2 ^ 59
def prefixEnd_729553 : Nat := 4983230072969 + 3 ^ 40 * 729553 * 2
def baseEnd_729553 : Nat := 83246967095486523162745

theorem tailTrace_729553 : CollatzResearch.WordTrace tailWord_729553 prefixEnd_729553 83246967095486523162745 := by
  unfold tailWord_729553
  simp only [CollatzResearch.WordTrace]
  refine ⟨26608983925961553577777313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17739322617307702385184875 26608983925961553577777313)
  ·
    refine ⟨19956737944471165183332985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26608983925961553577777313 19956737944471165183332985)
    ·
      refine ⟨14967553458353373887499739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19956737944471165183332985 14967553458353373887499739)
      ·
        refine ⟨22451330187530060831249609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14967553458353373887499739 22451330187530060831249609)
        ·
          refine ⟨16838497640647545623437207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22451330187530060831249609 16838497640647545623437207)
          ·
            refine ⟨25257746460971318435155811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16838497640647545623437207 25257746460971318435155811)
            ·
              refine ⟨37886619691456977652733717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25257746460971318435155811 37886619691456977652733717)
              ·
                refine ⟨1775935298037045827471893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37886619691456977652733717 1775935298037045827471893)
                ·
                  refine ⟨83246967095486523162745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1775935298037045827471893 83246967095486523162745)
                  ·
                    rfl

theorem cell22_729553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_729553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729553 prefixEnd_729553 := by exact prefixLift 729553
  have htrace : WordTrace (prefixWord ++ tailWord_729553) baseStart_729553 baseEnd_729553 := by
    simpa [prefixWord, tailWord_729553, baseEnd_729553] using wordTrace_append hprefix tailTrace_729553
  have hstable : (prefixWord ++ tailWord_729553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729553).length < 2 ^ (prefixWord ++ tailWord_729553).sum := by decide
  have hdescent : baseEnd_729553 < baseStart_729553 := by decide
  rcases family_descends (prefixWord ++ tailWord_729553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729583 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_729583 : Nat := 118140960795 + 729583 * 2 ^ 59
def prefixEnd_729583 : Nat := 4983230072969 + 3 ^ 40 * 729583 * 2
def baseEnd_729583 : Nat := 249751170899549491238143

theorem tailTrace_729583 : CollatzResearch.WordTrace tailWord_729583 prefixEnd_729583 249751170899549491238143 := by
  unfold tailWord_729583
  simp only [CollatzResearch.WordTrace]
  refine ⟨26610078115852868701369403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17740052077235245800912935 26610078115852868701369403)
  ·
    refine ⟨39915117173779303052054105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26610078115852868701369403 39915117173779303052054105)
    ·
      refine ⟨29936337880334477289040579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39915117173779303052054105 29936337880334477289040579)
      ·
        refine ⟨44904506820501715933560869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29936337880334477289040579 44904506820501715933560869)
        ·
          refine ⟨8419595028844071737542663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44904506820501715933560869 8419595028844071737542663)
          ·
            refine ⟨12629392543266107606313995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8419595028844071737542663 12629392543266107606313995)
            ·
              refine ⟨18944088814899161409470993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12629392543266107606313995 18944088814899161409470993)
              ·
                refine ⟨14208066611174371057103245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18944088814899161409470993 14208066611174371057103245)
                ·
                  refine ⟨5328024979190389146413717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14208066611174371057103245 5328024979190389146413717)
                  ·
                    refine ⟨249751170899549491238143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5328024979190389146413717 249751170899549491238143)
                    ·
                      rfl

theorem cell22_729583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_729583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729583 prefixEnd_729583 := by exact prefixLift 729583
  have htrace : WordTrace (prefixWord ++ tailWord_729583) baseStart_729583 baseEnd_729583 := by
    simpa [prefixWord, tailWord_729583, baseEnd_729583] using wordTrace_append hprefix tailTrace_729583
  have hstable : (prefixWord ++ tailWord_729583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729583).length < 2 ^ (prefixWord ++ tailWord_729583).sum := by decide
  have hdescent : baseEnd_729583 < baseStart_729583 := by decide
  rcases family_descends (prefixWord ++ tailWord_729583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729606 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_729606 : Nat := 118140960795 + 729606 * 2 ^ 59
def prefixEnd_729606 : Nat := 4983230072969 + 3 ^ 40 * 729606 * 2
def baseEnd_729606 : Nat := 249759044269585097913073

theorem tailTrace_729606 : CollatzResearch.WordTrace tailWord_729606 prefixEnd_729606 249759044269585097913073 := by
  unfold tailWord_729606
  simp only [CollatzResearch.WordTrace]
  refine ⟨831591156086548238420521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17740611329846362419637781 831591156086548238420521)
  ·
    refine ⟨623693367064911178815391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831591156086548238420521 623693367064911178815391)
    ·
      refine ⟨935540050597366768223087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623693367064911178815391 935540050597366768223087)
      ·
        refine ⟨1403310075896050152334631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935540050597366768223087 1403310075896050152334631)
        ·
          refine ⟨2104965113844075228501947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403310075896050152334631 2104965113844075228501947)
          ·
            refine ⟨3157447670766112842752921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104965113844075228501947 3157447670766112842752921)
            ·
              refine ⟨2368085753074584632064691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157447670766112842752921 2368085753074584632064691)
              ·
                refine ⟨3552128629611876948097037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368085753074584632064691 3552128629611876948097037)
                ·
                  refine ⟨1332048236104453855536389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3552128629611876948097037 1332048236104453855536389)
                  ·
                    refine ⟨249759044269585097913073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332048236104453855536389 249759044269585097913073)
                    ·
                      rfl

theorem cell22_729606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_729606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729606 prefixEnd_729606 := by exact prefixLift 729606
  have htrace : WordTrace (prefixWord ++ tailWord_729606) baseStart_729606 baseEnd_729606 := by
    simpa [prefixWord, tailWord_729606, baseEnd_729606] using wordTrace_append hprefix tailTrace_729606
  have hstable : (prefixWord ++ tailWord_729606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729606).length < 2 ^ (prefixWord ++ tailWord_729606).sum := by decide
  have hdescent : baseEnd_729606 < baseStart_729606 := by decide
  rcases family_descends (prefixWord ++ tailWord_729606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729623 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 1, 4]
def baseStart_729623 : Nat := 118140960795 + 729623 * 2 ^ 59
def prefixEnd_729623 : Nat := 4983230072969 + 3 ^ 40 * 729623 * 2
def baseEnd_729623 : Nat := 249764863717002720238021

theorem tailTrace_729623 : CollatzResearch.WordTrace tailWord_729623 prefixEnd_729623 249764863717002720238021 := by
  unfold tailWord_729623
  simp only [CollatzResearch.WordTrace]
  refine ⟨26611537035707955532825523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17741024690471970355217015 26611537035707955532825523)
  ·
    refine ⟨39917305553561933299238285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26611537035707955532825523 39917305553561933299238285)
    ·
      refine ⟨14968989582585724987214357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39917305553561933299238285 14968989582585724987214357)
      ·
        refine ⟨701671386683705858775673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14968989582585724987214357 701671386683705858775673)
        ·
          refine ⟨526253540012779394081755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701671386683705858775673 526253540012779394081755)
          ·
            refine ⟨789380310019169091122633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526253540012779394081755 789380310019169091122633)
            ·
              refine ⟨592035232514376818341975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789380310019169091122633 592035232514376818341975)
              ·
                refine ⟨888052848771565227512963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592035232514376818341975 888052848771565227512963)
                ·
                  refine ⟨1332079273157347841269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888052848771565227512963 1332079273157347841269445)
                  ·
                    refine ⟨249764863717002720238021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332079273157347841269445 249764863717002720238021)
                    ·
                      rfl

theorem cell22_729623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_729623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729623 prefixEnd_729623 := by exact prefixLift 729623
  have htrace : WordTrace (prefixWord ++ tailWord_729623) baseStart_729623 baseEnd_729623 := by
    simpa [prefixWord, tailWord_729623, baseEnd_729623] using wordTrace_append hprefix tailTrace_729623
  have hstable : (prefixWord ++ tailWord_729623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729623).length < 2 ^ (prefixWord ++ tailWord_729623).sum := by decide
  have hdescent : baseEnd_729623 < baseStart_729623 := by decide
  rcases family_descends (prefixWord ++ tailWord_729623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729677 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 7]
def baseStart_729677 : Nat := 118140960795 + 729677 * 2 ^ 59
def prefixEnd_729677 : Nat := 4983230072969 + 3 ^ 40 * 729677 * 2
def baseEnd_729677 : Nat := 83261116340188193129285

theorem tailTrace_729677 : CollatzResearch.WordTrace tailWord_729677 prefixEnd_729677 83261116340188193129285 := by
  unfold tailWord_729677
  simp only [CollatzResearch.WordTrace]
  refine ⟨26613506577512322755291285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17742337718341548503527523 26613506577512322755291285)
  ·
    refine ⟨1247508120820890129154279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26613506577512322755291285 1247508120820890129154279)
    ·
      refine ⟨1871262181231335193731419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247508120820890129154279 1871262181231335193731419)
      ·
        refine ⟨2806893271847002790597129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871262181231335193731419 2806893271847002790597129)
        ·
          refine ⟨2105169953885252092947847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2806893271847002790597129 2105169953885252092947847)
          ·
            refine ⟨3157754930827878139421771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105169953885252092947847 3157754930827878139421771)
            ·
              refine ⟨4736632396241817209132657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157754930827878139421771 4736632396241817209132657)
              ·
                refine ⟨3552474297181362906849493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4736632396241817209132657 3552474297181362906849493)
                ·
                  refine ⟨83261116340188193129285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3552474297181362906849493 83261116340188193129285)
                  ·
                    rfl

theorem cell22_729677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_729677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729677 prefixEnd_729677 := by exact prefixLift 729677
  have htrace : WordTrace (prefixWord ++ tailWord_729677) baseStart_729677 baseEnd_729677 := by
    simpa [prefixWord, tailWord_729677, baseEnd_729677] using wordTrace_append hprefix tailTrace_729677
  have hstable : (prefixWord ++ tailWord_729677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729677).length < 2 ^ (prefixWord ++ tailWord_729677).sum := by decide
  have hdescent : baseEnd_729677 < baseStart_729677 := by decide
  rcases family_descends (prefixWord ++ tailWord_729677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729681 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 1, 3]
def baseStart_729681 : Nat := 118140960795 + 729681 * 2 ^ 59
def prefixEnd_729681 : Nat := 4983230072969 + 3 ^ 40 * 729681 * 2
def baseEnd_729681 : Nat := 249784718302309902287843

theorem tailTrace_729681 : CollatzResearch.WordTrace tailWord_729681 prefixEnd_729681 249784718302309902287843 := by
  unfold tailWord_729681
  simp only [CollatzResearch.WordTrace]
  refine ⟨26613652469497831438436897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17742434979665220958957931 26613652469497831438436897)
  ·
    refine ⟨19960239352123373578827673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26613652469497831438436897 19960239352123373578827673)
    ·
      refine ⟨14970179514092530184120755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19960239352123373578827673 14970179514092530184120755)
      ·
        refine ⟨22455269271138795276181133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14970179514092530184120755 22455269271138795276181133)
        ·
          refine ⟨8420725976677048228567925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22455269271138795276181133 8420725976677048228567925)
          ·
            refine ⟨789443060313473271428243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8420725976677048228567925 789443060313473271428243)
            ·
              refine ⟨1184164590470209907142365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789443060313473271428243 1184164590470209907142365)
              ·
                refine ⟨444061721426328715178387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1184164590470209907142365 444061721426328715178387)
                ·
                  refine ⟨666092582139493072767581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444061721426328715178387 666092582139493072767581)
                  ·
                    refine ⟨249784718302309902287843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666092582139493072767581 249784718302309902287843)
                    ·
                      rfl

theorem cell22_729681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_729681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729681 prefixEnd_729681 := by exact prefixLift 729681
  have htrace : WordTrace (prefixWord ++ tailWord_729681) baseStart_729681 baseEnd_729681 := by
    simpa [prefixWord, tailWord_729681, baseEnd_729681] using wordTrace_append hprefix tailTrace_729681
  have hstable : (prefixWord ++ tailWord_729681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729681).length < 2 ^ (prefixWord ++ tailWord_729681).sum := by decide
  have hdescent : baseEnd_729681 < baseStart_729681 := by decide
  rcases family_descends (prefixWord ++ tailWord_729681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729690 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_729690 : Nat := 118140960795 + 729690 * 2 ^ 59
def prefixEnd_729690 : Nat := 4983230072969 + 3 ^ 40 * 729690 * 2
def baseEnd_729690 : Nat := 249787799186236878812815

theorem tailTrace_729690 : CollatzResearch.WordTrace tailWord_729690 prefixEnd_729690 249787799186236878812815 := by
  unfold tailWord_729690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653495181616306493878631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17742653817643483983676349 6653495181616306493878631)
  ·
    refine ⟨9980242772424459740817947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6653495181616306493878631 9980242772424459740817947)
    ·
      refine ⟨14970364158636689611226921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980242772424459740817947 14970364158636689611226921)
      ·
        refine ⟨11227773118977517208420191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14970364158636689611226921 11227773118977517208420191)
        ·
          refine ⟨16841659678466275812630287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11227773118977517208420191 16841659678466275812630287)
          ·
            refine ⟨25262489517699413718945431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16841659678466275812630287 25262489517699413718945431)
            ·
              refine ⟨37893734276549120578418147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25262489517699413718945431 37893734276549120578418147)
              ·
                refine ⟨56840601414823680867627221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37893734276549120578418147 56840601414823680867627221)
                ·
                  refine ⟨1332201595659930020335013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56840601414823680867627221 1332201595659930020335013)
                  ·
                    refine ⟨249787799186236878812815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332201595659930020335013 249787799186236878812815)
                    ·
                      rfl

theorem cell22_729690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_729690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729690 prefixEnd_729690 := by exact prefixLift 729690
  have htrace : WordTrace (prefixWord ++ tailWord_729690) baseStart_729690 baseEnd_729690 := by
    simpa [prefixWord, tailWord_729690, baseEnd_729690] using wordTrace_append hprefix tailTrace_729690
  have hstable : (prefixWord ++ tailWord_729690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729690).length < 2 ^ (prefixWord ++ tailWord_729690).sum := by decide
  have hdescent : baseEnd_729690 < baseStart_729690 := by decide
  rcases family_descends (prefixWord ++ tailWord_729690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729698 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_729698 : Nat := 118140960795 + 729698 * 2 ^ 59
def prefixEnd_729698 : Nat := 4983230072969 + 3 ^ 40 * 729698 * 2
def baseEnd_729698 : Nat := 249790537749727524612791

theorem tailTrace_729698 : CollatzResearch.WordTrace tailWord_729698 prefixEnd_729698 249790537749727524612791 := by
  unfold tailWord_729698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653568127609060835451437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17742848340290828894537165 6653568127609060835451437)
  ·
    refine ⟨2495088047853397813294289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6653568127609060835451437 2495088047853397813294289)
    ·
      refine ⟨1871316035890048359970717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2495088047853397813294289 1871316035890048359970717)
      ·
        refine ⟨701743513458768134989019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1871316035890048359970717 701743513458768134989019)
        ·
          refine ⟨1052615270188152202483529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701743513458768134989019 1052615270188152202483529)
          ·
            refine ⟨789461452641114151862647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052615270188152202483529 789461452641114151862647)
            ·
              refine ⟨1184192178961671227793971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789461452641114151862647 1184192178961671227793971)
              ·
                refine ⟨1776288268442506841690957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184192178961671227793971 1776288268442506841690957)
                ·
                  refine ⟨666108100665940065634109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1776288268442506841690957 666108100665940065634109)
                  ·
                    refine ⟨249790537749727524612791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666108100665940065634109 249790537749727524612791)
                    ·
                      rfl

theorem cell22_729698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_729698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729698 prefixEnd_729698 := by exact prefixLift 729698
  have htrace : WordTrace (prefixWord ++ tailWord_729698) baseStart_729698 baseEnd_729698 := by
    simpa [prefixWord, tailWord_729698, baseEnd_729698] using wordTrace_append hprefix tailTrace_729698
  have hstable : (prefixWord ++ tailWord_729698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729698).length < 2 ^ (prefixWord ++ tailWord_729698).sum := by decide
  have hdescent : baseEnd_729698 < baseStart_729698 := by decide
  rcases family_descends (prefixWord ++ tailWord_729698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729752 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_729752 : Nat := 118140960795 + 729752 * 2 ^ 59
def prefixEnd_729752 : Nat := 4983230072969 + 3 ^ 40 * 729752 * 2
def baseEnd_729752 : Nat := 249809023053289383762625

theorem tailTrace_729752 : CollatzResearch.WordTrace tailWord_729752 prefixEnd_729752 249809023053289383762625 := by
  unfold tailWord_729752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308121026120305282135755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17744161368160407042847673 13308121026120305282135755)
  ·
    refine ⟨19962181539180457923203633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13308121026120305282135755 19962181539180457923203633)
    ·
      refine ⟨14971636154385343442402725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19962181539180457923203633 14971636154385343442402725)
      ·
        refine ⟨2807181778947251895450511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14971636154385343442402725 2807181778947251895450511)
        ·
          refine ⟨4210772668420877843175767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807181778947251895450511 4210772668420877843175767)
          ·
            refine ⟨6316159002631316764763651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210772668420877843175767 6316159002631316764763651)
            ·
              refine ⟨9474238503946975147145477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316159002631316764763651 9474238503946975147145477)
              ·
                refine ⟨1776419719490057840089777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9474238503946975147145477 1776419719490057840089777)
                ·
                  refine ⟨1332314789617543380067333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776419719490057840089777 1332314789617543380067333)
                  ·
                    refine ⟨249809023053289383762625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332314789617543380067333 249809023053289383762625)
                    ·
                      rfl

theorem cell22_729752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_729752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729752 prefixEnd_729752 := by exact prefixLift 729752
  have htrace : WordTrace (prefixWord ++ tailWord_729752) baseStart_729752 baseEnd_729752 := by
    simpa [prefixWord, tailWord_729752, baseEnd_729752] using wordTrace_append hprefix tailTrace_729752
  have hstable : (prefixWord ++ tailWord_729752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729752).length < 2 ^ (prefixWord ++ tailWord_729752).sum := by decide
  have hdescent : baseEnd_729752 < baseStart_729752 := by decide
  rcases family_descends (prefixWord ++ tailWord_729752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729756 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_729756 : Nat := 118140960795 + 729756 * 2 ^ 59
def prefixEnd_729756 : Nat := 4983230072969 + 3 ^ 40 * 729756 * 2
def baseEnd_729756 : Nat := 83270130778344902220871

theorem tailTrace_729756 : CollatzResearch.WordTrace tailWord_729756 prefixEnd_729756 83270130778344902220871 := by
  unfold tailWord_729756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308193972113059623708561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17744258629484079498278081 13308193972113059623708561)
  ·
    refine ⟨9981145479084794717781421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13308193972113059623708561 9981145479084794717781421)
    ·
      refine ⟨3742929554656798019168033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9981145479084794717781421 3742929554656798019168033)
      ·
        refine ⟨2807197165992598514376025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3742929554656798019168033 2807197165992598514376025)
        ·
          refine ⟨2105397874494448885782019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807197165992598514376025 2105397874494448885782019)
          ·
            refine ⟨3158096811741673328673029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105397874494448885782019 3158096811741673328673029)
            ·
              refine ⟨592143152201563749126193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3158096811741673328673029 592143152201563749126193)
              ·
                refine ⟨444107364151172811844645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592143152201563749126193 444107364151172811844645)
                ·
                  refine ⟨83270130778344902220871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444107364151172811844645 83270130778344902220871)
                  ·
                    rfl

theorem cell22_729756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_729756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729756 prefixEnd_729756 := by exact prefixLift 729756
  have htrace : WordTrace (prefixWord ++ tailWord_729756) baseStart_729756 baseEnd_729756 := by
    simpa [prefixWord, tailWord_729756, baseEnd_729756] using wordTrace_append hprefix tailTrace_729756
  have hstable : (prefixWord ++ tailWord_729756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729756).length < 2 ^ (prefixWord ++ tailWord_729756).sum := by decide
  have hdescent : baseEnd_729756 < baseStart_729756 := by decide
  rcases family_descends (prefixWord ++ tailWord_729756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729765 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_729765 : Nat := 118140960795 + 729765 * 2 ^ 59
def prefixEnd_729765 : Nat := 4983230072969 + 3 ^ 40 * 729765 * 2
def baseEnd_729765 : Nat := 249813473218961683187585

theorem tailTrace_729765 : CollatzResearch.WordTrace tailWord_729765 prefixEnd_729765 249813473218961683187585 := by
  unfold tailWord_729765
  simp only [CollatzResearch.WordTrace]
  refine ⟨26616716201193513784494749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17744477467462342522996499 26616716201193513784494749)
  ·
    refine ⟨9981268575447567669185531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26616716201193513784494749 9981268575447567669185531)
    ·
      refine ⟨14971902863171351503778297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9981268575447567669185531 14971902863171351503778297)
      ·
        refine ⟨11228927147378513627833723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14971902863171351503778297 11228927147378513627833723)
        ·
          refine ⟨16843390721067770441750585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11228927147378513627833723 16843390721067770441750585)
          ·
            refine ⟨12632543040800827831312939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16843390721067770441750585 12632543040800827831312939)
            ·
              refine ⟨18948814561201241746969409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12632543040800827831312939 18948814561201241746969409)
              ·
                refine ⟨14211610920900931310227057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18948814561201241746969409 14211610920900931310227057)
                ·
                  refine ⟨10658708190675698482670293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14211610920900931310227057 10658708190675698482670293)
                  ·
                    refine ⟨249813473218961683187585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10658708190675698482670293 249813473218961683187585)
                    ·
                      rfl

theorem cell22_729765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_729765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729765 prefixEnd_729765 := by exact prefixLift 729765
  have htrace : WordTrace (prefixWord ++ tailWord_729765) baseStart_729765 baseEnd_729765 := by
    simpa [prefixWord, tailWord_729765, baseEnd_729765] using wordTrace_append hprefix tailTrace_729765
  have hstable : (prefixWord ++ tailWord_729765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729765).length < 2 ^ (prefixWord ++ tailWord_729765).sum := by decide
  have hdescent : baseEnd_729765 < baseStart_729765 := by decide
  rcases family_descends (prefixWord ++ tailWord_729765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729805 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_729805 : Nat := 118140960795 + 729805 * 2 ^ 59
def prefixEnd_729805 : Nat := 4983230072969 + 3 ^ 40 * 729805 * 2
def baseEnd_729805 : Nat := 249827166036414912187463

theorem tailTrace_729805 : CollatzResearch.WordTrace tailWord_729805 prefixEnd_729805 249827166036414912187463 := by
  unfold tailWord_729805
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618175121048600615950869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17745450080699067077300579 26618175121048600615950869)
  ·
    refine ⟨1247726958799153153872697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26618175121048600615950869 1247726958799153153872697)
    ·
      refine ⟨935795219099364865404523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247726958799153153872697 935795219099364865404523)
      ·
        refine ⟨1403692828649047298106785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935795219099364865404523 1403692828649047298106785)
        ·
          refine ⟨1052769621486785473580089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403692828649047298106785 1052769621486785473580089)
          ·
            refine ⟨789577216115089105185067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052769621486785473580089 789577216115089105185067)
            ·
              refine ⟨1184365824172633657777601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789577216115089105185067 1184365824172633657777601)
              ·
                refine ⟨888274368129475243333201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184365824172633657777601 888274368129475243333201)
                ·
                  refine ⟨666205776097106432499901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888274368129475243333201 666205776097106432499901)
                  ·
                    refine ⟨249827166036414912187463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666205776097106432499901 249827166036414912187463)
                    ·
                      rfl

theorem cell22_729805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_729805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729805 prefixEnd_729805 := by exact prefixLift 729805
  have htrace : WordTrace (prefixWord ++ tailWord_729805) baseStart_729805 baseEnd_729805 := by
    simpa [prefixWord, tailWord_729805, baseEnd_729805] using wordTrace_append hprefix tailTrace_729805
  have hstable : (prefixWord ++ tailWord_729805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729805).length < 2 ^ (prefixWord ++ tailWord_729805).sum := by decide
  have hdescent : baseEnd_729805 < baseStart_729805 := by decide
  rcases family_descends (prefixWord ++ tailWord_729805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729816 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 1, 3]
def baseStart_729816 : Nat := 118140960795 + 729816 * 2 ^ 59
def prefixEnd_729816 : Nat := 4983230072969 + 3 ^ 40 * 729816 * 2
def baseEnd_729816 : Nat := 249830931561214550162429

theorem tailTrace_729816 : CollatzResearch.WordTrace tailWord_729816 prefixEnd_729816 249830931561214550162429 := by
  unfold tailWord_729816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309288162004374747300651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17745717549339166329734201 13309288162004374747300651)
  ·
    refine ⟨19963932243006562120950977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13309288162004374747300651 19963932243006562120950977)
    ·
      refine ⟨14972949182254921590713233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19963932243006562120950977 14972949182254921590713233)
      ·
        refine ⟨11229711886691191193034925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14972949182254921590713233 11229711886691191193034925)
        ·
          refine ⟨4211141957509196697388097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11229711886691191193034925 4211141957509196697388097)
          ·
            refine ⟨3158356468131897523041073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211141957509196697388097 3158356468131897523041073)
            ·
              refine ⟨2368767351098923142280805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158356468131897523041073 2368767351098923142280805)
              ·
                refine ⟨444143878331048089177651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2368767351098923142280805 444143878331048089177651)
                ·
                  refine ⟨666215817496572133766477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444143878331048089177651 666215817496572133766477)
                  ·
                    refine ⟨249830931561214550162429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666215817496572133766477 249830931561214550162429)
                    ·
                      rfl

theorem cell22_729816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_729816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729816 prefixEnd_729816 := by exact prefixLift 729816
  have htrace : WordTrace (prefixWord ++ tailWord_729816) baseStart_729816 baseEnd_729816 := by
    simpa [prefixWord, tailWord_729816, baseEnd_729816] using wordTrace_append hprefix tailTrace_729816
  have hstable : (prefixWord ++ tailWord_729816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729816).length < 2 ^ (prefixWord ++ tailWord_729816).sum := by decide
  have hdescent : baseEnd_729816 < baseStart_729816 := by decide
  rcases family_descends (prefixWord ++ tailWord_729816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729910 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_729910 : Nat := 118140960795 + 729910 * 2 ^ 59
def prefixEnd_729910 : Nat := 4983230072969 + 3 ^ 40 * 729910 * 2
def baseEnd_729910 : Nat := 249863109682229638312141

theorem tailTrace_729910 : CollatzResearch.WordTrace tailWord_729910 prefixEnd_729910 249863109682229638312141 := by
  unfold tailWord_729910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663875299104262721782699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17748003190445469032348789 1663875299104262721782699)
  ·
    refine ⟨2495812948656394082674049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663875299104262721782699 2495812948656394082674049)
    ·
      refine ⟨1871859711492295562005537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2495812948656394082674049 1871859711492295562005537)
      ·
        refine ⟨1403894783619221671504153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1871859711492295562005537 1403894783619221671504153)
        ·
          refine ⟨1052921087714416253628115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403894783619221671504153 1052921087714416253628115)
          ·
            refine ⟨1579381631571624380442173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052921087714416253628115 1579381631571624380442173)
            ·
              refine ⟨592268111839359142665815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1579381631571624380442173 592268111839359142665815)
              ·
                refine ⟨888402167759038713998723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592268111839359142665815 888402167759038713998723)
                ·
                  refine ⟨1332603251638558070998085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888402167759038713998723 1332603251638558070998085)
                  ·
                    refine ⟨249863109682229638312141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332603251638558070998085 249863109682229638312141)
                    ·
                      rfl

theorem cell22_729910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_729910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729910 prefixEnd_729910 := by exact prefixLift 729910
  have htrace : WordTrace (prefixWord ++ tailWord_729910) baseStart_729910 baseEnd_729910 := by
    simpa [prefixWord, tailWord_729910, baseEnd_729910] using wordTrace_append hprefix tailTrace_729910
  have hstable : (prefixWord ++ tailWord_729910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729910).length < 2 ^ (prefixWord ++ tailWord_729910).sum := by decide
  have hdescent : baseEnd_729910 < baseStart_729910 := by decide
  rcases family_descends (prefixWord ++ tailWord_729910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729934 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_729934 : Nat := 118140960795 + 729934 * 2 ^ 59
def prefixEnd_729934 : Nat := 4983230072969 + 3 ^ 40 * 729934 * 2
def baseEnd_729934 : Nat := 249871325372701575712067

theorem tailTrace_729934 : CollatzResearch.WordTrace tailWord_729934 prefixEnd_729934 249871325372701575712067 := by
  unfold tailWord_729934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327860017197656955924607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17748586758387503764931237 3327860017197656955924607)
  ·
    refine ⟨4991790025796485433886911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3327860017197656955924607 4991790025796485433886911)
    ·
      refine ⟨7487685038694728150830367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991790025796485433886911 7487685038694728150830367)
      ·
        refine ⟨11231527558042092226245551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487685038694728150830367 11231527558042092226245551)
        ·
          refine ⟨16847291337063138339368327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11231527558042092226245551 16847291337063138339368327)
          ·
            refine ⟨25270937005594707509052491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16847291337063138339368327 25270937005594707509052491)
            ·
              refine ⟨37906405508392061263578737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25270937005594707509052491 37906405508392061263578737)
              ·
                refine ⟨28429804131294045947684053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37906405508392061263578737 28429804131294045947684053)
                ·
                  refine ⟨666323534327204201898845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28429804131294045947684053 666323534327204201898845)
                  ·
                    refine ⟨249871325372701575712067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666323534327204201898845 249871325372701575712067)
                    ·
                      rfl

theorem cell22_729934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_729934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_729934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_729934 prefixEnd_729934 := by exact prefixLift 729934
  have htrace : WordTrace (prefixWord ++ tailWord_729934) baseStart_729934 baseEnd_729934 := by
    simpa [prefixWord, tailWord_729934, baseEnd_729934] using wordTrace_append hprefix tailTrace_729934
  have hstable : (prefixWord ++ tailWord_729934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729934).length < 2 ^ (prefixWord ++ tailWord_729934).sum := by decide
  have hdescent : baseEnd_729934 < baseStart_729934 := by decide
  rcases family_descends (prefixWord ++ tailWord_729934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730039 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_730039 : Nat := 118140960795 + 730039 * 2 ^ 59
def prefixEnd_730039 : Nat := 4983230072969 + 3 ^ 40 * 730039 * 2
def baseEnd_730039 : Nat := 249907269018516301836745

theorem tailTrace_730039 : CollatzResearch.WordTrace tailWord_730039 prefixEnd_730039 249907269018516301836745 := by
  unfold tailWord_730039
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626709802200858579969171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17751139868133905719979447 26626709802200858579969171)
  ·
    refine ⟨39940064703301287869953757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26626709802200858579969171 39940064703301287869953757)
    ·
      refine ⟨14977524263737982951232659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39940064703301287869953757 14977524263737982951232659)
      ·
        refine ⟨22466286395606974426848989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14977524263737982951232659 22466286395606974426848989)
        ·
          refine ⟨8424857398352615410068371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22466286395606974426848989 8424857398352615410068371)
          ·
            refine ⟨12637286097528923115102557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424857398352615410068371 12637286097528923115102557)
            ·
              refine ⟨4738982286573346168163459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12637286097528923115102557 4738982286573346168163459)
              ·
                refine ⟨7108473429860019252245189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738982286573346168163459 7108473429860019252245189)
                ·
                  refine ⟨1332838768098753609795973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7108473429860019252245189 1332838768098753609795973)
                  ·
                    refine ⟨249907269018516301836745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332838768098753609795973 249907269018516301836745)
                    ·
                      rfl

theorem cell22_730039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_730039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730039 prefixEnd_730039 := by exact prefixLift 730039
  have htrace : WordTrace (prefixWord ++ tailWord_730039) baseStart_730039 baseEnd_730039 := by
    simpa [prefixWord, tailWord_730039, baseEnd_730039] using wordTrace_append hprefix tailTrace_730039
  have hstable : (prefixWord ++ tailWord_730039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730039).length < 2 ^ (prefixWord ++ tailWord_730039).sum := by decide
  have hdescent : baseEnd_730039 < baseStart_730039 := by decide
  rcases family_descends (prefixWord ++ tailWord_730039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730041 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_730041 : Nat := 118140960795 + 730041 * 2 ^ 59
def prefixEnd_730041 : Nat := 4983230072969 + 3 ^ 40 * 730041 * 2
def baseEnd_730041 : Nat := 249907953659388963286739

theorem tailTrace_730041 : CollatzResearch.WordTrace tailWord_730041 prefixEnd_730041 249907953659388963286739 := by
  unfold tailWord_730041
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626782748193612921541977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17751188498795741947694651 26626782748193612921541977)
  ·
    refine ⟨19970087061145209691156483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26626782748193612921541977 19970087061145209691156483)
    ·
      refine ⟨29955130591717814536734725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19970087061145209691156483 29955130591717814536734725)
      ·
        refine ⟨5616586985947090225637761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29955130591717814536734725 5616586985947090225637761)
        ·
          refine ⟨4212440239460317669228321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616586985947090225637761 4212440239460317669228321)
          ·
            refine ⟨3159330179595238251921241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212440239460317669228321 3159330179595238251921241)
            ·
              refine ⟨2369497634696428688940931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159330179595238251921241 2369497634696428688940931)
              ·
                refine ⟨3554246452044643033411397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369497634696428688940931 3554246452044643033411397)
                ·
                  refine ⟨666421209758370568764637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3554246452044643033411397 666421209758370568764637)
                  ·
                    refine ⟨249907953659388963286739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666421209758370568764637 249907953659388963286739)
                    ·
                      rfl

theorem cell22_730041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_730041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730041 prefixEnd_730041 := by exact prefixLift 730041
  have htrace : WordTrace (prefixWord ++ tailWord_730041) baseStart_730041 baseEnd_730041 := by
    simpa [prefixWord, tailWord_730041, baseEnd_730041] using wordTrace_append hprefix tailTrace_730041
  have hstable : (prefixWord ++ tailWord_730041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730041).length < 2 ^ (prefixWord ++ tailWord_730041).sum := by decide
  have hdescent : baseEnd_730041 < baseStart_730041 := by decide
  rcases family_descends (prefixWord ++ tailWord_730041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730161 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 6]
def baseStart_730161 : Nat := 118140960795 + 730161 * 2 ^ 59
def prefixEnd_730161 : Nat := 4983230072969 + 3 ^ 40 * 730161 * 2
def baseEnd_730161 : Nat := 83316344037249550095457

theorem tailTrace_730161 : CollatzResearch.WordTrace tailWord_730161 prefixEnd_730161 83316344037249550095457 := by
  unfold tailWord_730161
  simp only [CollatzResearch.WordTrace]
  refine ⟨26631159507758873415910337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17754106338505915610606891 26631159507758873415910337)
  ·
    refine ⟨19973369630819155061932753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26631159507758873415910337 19973369630819155061932753)
    ·
      refine ⟨14980027223114366296449565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19973369630819155061932753 14980027223114366296449565)
      ·
        refine ⟨5617510208667887361168587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14980027223114366296449565 5617510208667887361168587)
        ·
          refine ⟨8426265313001831041752881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617510208667887361168587 8426265313001831041752881)
          ·
            refine ⟨6319698984751373281314661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8426265313001831041752881 6319698984751373281314661)
            ·
              refine ⟨1184943559640882490246499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6319698984751373281314661 1184943559640882490246499)
              ·
                refine ⟨1777415339461323735369749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184943559640882490246499 1777415339461323735369749)
                ·
                  refine ⟨83316344037249550095457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1777415339461323735369749 83316344037249550095457)
                  ·
                    rfl

theorem cell22_730161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_730161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730161 prefixEnd_730161 := by exact prefixLift 730161
  have htrace : WordTrace (prefixWord ++ tailWord_730161) baseStart_730161 baseEnd_730161 := by
    simpa [prefixWord, tailWord_730161, baseEnd_730161] using wordTrace_append hprefix tailTrace_730161
  have hstable : (prefixWord ++ tailWord_730161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730161).length < 2 ^ (prefixWord ++ tailWord_730161).sum := by decide
  have hdescent : baseEnd_730161 < baseStart_730161 := by decide
  rcases family_descends (prefixWord ++ tailWord_730161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730210 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_730210 : Nat := 118140960795 + 730210 * 2 ^ 59
def prefixEnd_730210 : Nat := 4983230072969 + 3 ^ 40 * 730210 * 2
def baseEnd_730210 : Nat := 249965805813128855811221

theorem tailTrace_730210 : CollatzResearch.WordTrace tailWord_730210 prefixEnd_730210 249965805813128855811221 := by
  unfold tailWord_730210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658236671145338696111021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17755297789720903189629389 6658236671145338696111021)
  ·
    refine ⟨2496838751679502011041633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6658236671145338696111021 2496838751679502011041633)
    ·
      refine ⟨1872629063759626508281225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496838751679502011041633 1872629063759626508281225)
      ·
        refine ⟨1404471797819719881210919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1872629063759626508281225 1404471797819719881210919)
        ·
          refine ⟨2106707696729579821816379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404471797819719881210919 2106707696729579821816379)
          ·
            refine ⟨3160061545094369732724569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106707696729579821816379 3160061545094369732724569)
            ·
              refine ⟨2370046158820777299543427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160061545094369732724569 2370046158820777299543427)
              ·
                refine ⟨3555069238231165949315141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370046158820777299543427 3555069238231165949315141)
                ·
                  refine ⟨666575482168343615496589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3555069238231165949315141 666575482168343615496589)
                  ·
                    refine ⟨249965805813128855811221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666575482168343615496589 249965805813128855811221)
                    ·
                      rfl

theorem cell22_730210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_730210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730210 prefixEnd_730210 := by exact prefixLift 730210
  have htrace : WordTrace (prefixWord ++ tailWord_730210) baseStart_730210 baseEnd_730210 := by
    simpa [prefixWord, tailWord_730210, baseEnd_730210] using wordTrace_append hprefix tailTrace_730210
  have hstable : (prefixWord ++ tailWord_730210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730210).length < 2 ^ (prefixWord ++ tailWord_730210).sum := by decide
  have hdescent : baseEnd_730210 < baseStart_730210 := by decide
  rcases family_descends (prefixWord ++ tailWord_730210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730268 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_730268 : Nat := 118140960795 + 730268 * 2 ^ 59
def prefixEnd_730268 : Nat := 4983230072969 + 3 ^ 40 * 730268 * 2
def baseEnd_730268 : Nat := 83328553466145345953681

theorem tailTrace_730268 : CollatzResearch.WordTrace tailWord_730268 prefixEnd_730268 83328553466145345953681 := by
  unfold tailWord_730268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317531059185615345027729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17756708078914153793370305 13317531059185615345027729)
  ·
    refine ⟨9988148294389211508770797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13317531059185615345027729 9988148294389211508770797)
    ·
      refine ⟨3745555610395954315789049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9988148294389211508770797 3745555610395954315789049)
      ·
        refine ⟨2809166707796965736841787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745555610395954315789049 2809166707796965736841787)
        ·
          refine ⟨4213750061695448605262681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809166707796965736841787 4213750061695448605262681)
          ·
            refine ⟨3160312546271586453947011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213750061695448605262681 3160312546271586453947011)
            ·
              refine ⟨4740468819407379680920517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160312546271586453947011 4740468819407379680920517)
              ·
                refine ⟨888837903638883690172597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4740468819407379680920517 888837903638883690172597)
                ·
                  refine ⟨83328553466145345953681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 888837903638883690172597 83328553466145345953681)
                  ·
                    rfl

theorem cell22_730268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_730268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730268 prefixEnd_730268 := by exact prefixLift 730268
  have htrace : WordTrace (prefixWord ++ tailWord_730268) baseStart_730268 baseEnd_730268 := by
    simpa [prefixWord, tailWord_730268, baseEnd_730268] using wordTrace_append hprefix tailTrace_730268
  have hstable : (prefixWord ++ tailWord_730268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730268).length < 2 ^ (prefixWord ++ tailWord_730268).sum := by decide
  have hdescent : baseEnd_730268 < baseStart_730268 := by decide
  rcases family_descends (prefixWord ++ tailWord_730268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730298 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_730298 : Nat := 118140960795 + 730298 * 2 ^ 59
def prefixEnd_730298 : Nat := 4983230072969 + 3 ^ 40 * 730298 * 2
def baseEnd_730298 : Nat := 249995930011525959610951

theorem tailTrace_730298 : CollatzResearch.WordTrace tailWord_730298 prefixEnd_730298 249995930011525959610951 := by
  unfold tailWord_730298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659039077065636453411887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17757437538841697209098365 6659039077065636453411887)
  ·
    refine ⟨9988558615598454680117831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6659039077065636453411887 9988558615598454680117831)
    ·
      refine ⟨14982837923397682020176747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988558615598454680117831 14982837923397682020176747)
      ·
        refine ⟨22474256885096523030265121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982837923397682020176747 22474256885096523030265121)
        ·
          refine ⟨16855692663822392272698841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22474256885096523030265121 16855692663822392272698841)
          ·
            refine ⟨12641769497866794204524131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16855692663822392272698841 12641769497866794204524131)
            ·
              refine ⟨18962654246800191306786197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12641769497866794204524131 18962654246800191306786197)
              ·
                refine ⟨888874417818758967505603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18962654246800191306786197 888874417818758967505603)
                ·
                  refine ⟨1333311626728138451258405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888874417818758967505603 1333311626728138451258405)
                  ·
                    refine ⟨249995930011525959610951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1333311626728138451258405 249995930011525959610951)
                    ·
                      rfl

theorem cell22_730298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_730298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730298 prefixEnd_730298 := by exact prefixLift 730298
  have htrace : WordTrace (prefixWord ++ tailWord_730298) baseStart_730298 baseEnd_730298 := by
    simpa [prefixWord, tailWord_730298, baseEnd_730298] using wordTrace_append hprefix tailTrace_730298
  have hstable : (prefixWord ++ tailWord_730298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730298).length < 2 ^ (prefixWord ++ tailWord_730298).sum := by decide
  have hdescent : baseEnd_730298 < baseStart_730298 := by decide
  rcases family_descends (prefixWord ++ tailWord_730298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730364 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_730364 : Nat := 118140960795 + 730364 * 2 ^ 59
def prefixEnd_730364 : Nat := 4983230072969 + 3 ^ 40 * 730364 * 2
def baseEnd_730364 : Nat := 83339507720107929153583

theorem tailTrace_730364 : CollatzResearch.WordTrace tailWord_730364 prefixEnd_730364 83339507720107929153583 := by
  unfold tailWord_730364
  simp only [CollatzResearch.WordTrace]
  refine ⟨13319281763011719542775073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17759042350682292723700097 13319281763011719542775073)
  ·
    refine ⟨9989461322258789657081305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13319281763011719542775073 9989461322258789657081305)
    ·
      refine ⟨7492095991694092242810979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9989461322258789657081305 7492095991694092242810979)
      ·
        refine ⟨11238143987541138364216469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492095991694092242810979 11238143987541138364216469)
        ·
          refine ⟨526787999415990860822647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11238143987541138364216469 526787999415990860822647)
          ·
            refine ⟨790181999123986291233971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526787999415990860822647 790181999123986291233971)
            ·
              refine ⟨1185272998685979436850957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790181999123986291233971 1185272998685979436850957)
              ·
                refine ⟨444477374507242288819109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185272998685979436850957 444477374507242288819109)
                ·
                  refine ⟨83339507720107929153583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444477374507242288819109 83339507720107929153583)
                  ·
                    rfl

theorem cell22_730364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_730364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730364 prefixEnd_730364 := by exact prefixLift 730364
  have htrace : WordTrace (prefixWord ++ tailWord_730364) baseStart_730364 baseEnd_730364 := by
    simpa [prefixWord, tailWord_730364, baseEnd_730364] using wordTrace_append hprefix tailTrace_730364
  have hstable : (prefixWord ++ tailWord_730364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730364).length < 2 ^ (prefixWord ++ tailWord_730364).sum := by decide
  have hdescent : baseEnd_730364 < baseStart_730364 := by decide
  rcases family_descends (prefixWord ++ tailWord_730364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730448 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_730448 : Nat := 118140960795 + 730448 * 2 ^ 59
def prefixEnd_730448 : Nat := 4983230072969 + 3 ^ 40 * 730448 * 2
def baseEnd_730448 : Nat := 83349092692325189453497

theorem tailTrace_730448 : CollatzResearch.WordTrace tailWord_730448 prefixEnd_730448 83349092692325189453497 := by
  unfold tailWord_730448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320813628859560715803999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17761084838479414287738665 13320813628859560715803999)
  ·
    refine ⟨19981220443289341073705999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13320813628859560715803999 19981220443289341073705999)
    ·
      refine ⟨29971830664934011610558999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981220443289341073705999 29971830664934011610558999)
      ·
        refine ⟨44957745997401017415838499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29971830664934011610558999 44957745997401017415838499)
        ·
          refine ⟨67436618996101526123757749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44957745997401017415838499 67436618996101526123757749)
          ·
            refine ⟨6322183030884518074102289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67436618996101526123757749 6322183030884518074102289)
            ·
              refine ⟨4741637273163388555576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322183030884518074102289 4741637273163388555576717)
              ·
                refine ⟨1778113977436270708341269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4741637273163388555576717 1778113977436270708341269)
                ·
                  refine ⟨83349092692325189453497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1778113977436270708341269 83349092692325189453497)
                  ·
                    rfl

theorem cell22_730448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_730448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730448 prefixEnd_730448 := by exact prefixLift 730448
  have htrace : WordTrace (prefixWord ++ tailWord_730448) baseStart_730448 baseEnd_730448 := by
    simpa [prefixWord, tailWord_730448, baseEnd_730448] using wordTrace_append hprefix tailTrace_730448
  have hstable : (prefixWord ++ tailWord_730448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730448).length < 2 ^ (prefixWord ++ tailWord_730448).sum := by decide
  have hdescent : baseEnd_730448 < baseStart_730448 := by decide
  rcases family_descends (prefixWord ++ tailWord_730448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730480 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_730480 : Nat := 118140960795 + 730480 * 2 ^ 59
def prefixEnd_730480 : Nat := 4983230072969 + 3 ^ 40 * 730480 * 2
def baseEnd_730480 : Nat := 250058232330938151560393

theorem tailTrace_730480 : CollatzResearch.WordTrace tailWord_730480 prefixEnd_730480 250058232330938151560393 := by
  unfold tailWord_730480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13321397196801595448386447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17761862929068793931181929 13321397196801595448386447)
  ·
    refine ⟨19982095795202393172579671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13321397196801595448386447 19982095795202393172579671)
    ·
      refine ⟨29973143692803589758869507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19982095795202393172579671 29973143692803589758869507)
      ·
        refine ⟨44959715539205384638304261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29973143692803589758869507 44959715539205384638304261)
        ·
          refine ⟨8429946663601009619682049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44959715539205384638304261 8429946663601009619682049)
          ·
            refine ⟨6322459997700757214761537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8429946663601009619682049 6322459997700757214761537)
            ·
              refine ⟨4741844998275567911071153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322459997700757214761537 4741844998275567911071153)
              ·
                refine ⟨3556383748706675933303365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741844998275567911071153 3556383748706675933303365)
                ·
                  refine ⟨666821952882501737494381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3556383748706675933303365 666821952882501737494381)
                  ·
                    refine ⟨250058232330938151560393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 666821952882501737494381 250058232330938151560393)
                    ·
                      rfl

theorem cell22_730480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_730480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730480 prefixEnd_730480 := by exact prefixLift 730480
  have htrace : WordTrace (prefixWord ++ tailWord_730480) baseStart_730480 baseEnd_730480 := by
    simpa [prefixWord, tailWord_730480, baseEnd_730480] using wordTrace_append hprefix tailTrace_730480
  have hstable : (prefixWord ++ tailWord_730480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730480).length < 2 ^ (prefixWord ++ tailWord_730480).sum := by decide
  have hdescent : baseEnd_730480 < baseStart_730480 := by decide
  rcases family_descends (prefixWord ++ tailWord_730480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730482 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_730482 : Nat := 118140960795 + 730482 * 2 ^ 59
def prefixEnd_730482 : Nat := 4983230072969 + 3 ^ 40 * 730482 * 2
def baseEnd_730482 : Nat := 83352972323936937670129

theorem tailTrace_730482 : CollatzResearch.WordTrace tailWord_730482 prefixEnd_730482 83352972323936937670129 := by
  unfold tailWord_730482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6660716834898986309586425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17761911559730630158897133 6660716834898986309586425)
  ·
    refine ⟨4995537626174239732189819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6660716834898986309586425 4995537626174239732189819)
    ·
      refine ⟨7493306439261359598284729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995537626174239732189819 7493306439261359598284729)
      ·
        refine ⟨5619979829446019698713547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7493306439261359598284729 5619979829446019698713547)
        ·
          refine ⟨8429969744169029548070321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619979829446019698713547 8429969744169029548070321)
          ·
            refine ⟨6322477308126772161052741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8429969744169029548070321 6322477308126772161052741)
            ·
              refine ⟨1185464495273769780197389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6322477308126772161052741 1185464495273769780197389)
              ·
                refine ⟨444549185727663667574021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185464495273769780197389 444549185727663667574021)
                ·
                  refine ⟨83352972323936937670129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444549185727663667574021 83352972323936937670129)
                  ·
                    rfl

theorem cell22_730482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_730482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730482 prefixEnd_730482 := by exact prefixLift 730482
  have htrace : WordTrace (prefixWord ++ tailWord_730482) baseStart_730482 baseEnd_730482 := by
    simpa [prefixWord, tailWord_730482, baseEnd_730482] using wordTrace_append hprefix tailTrace_730482
  have hstable : (prefixWord ++ tailWord_730482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730482).length < 2 ^ (prefixWord ++ tailWord_730482).sum := by decide
  have hdescent : baseEnd_730482 < baseStart_730482 := by decide
  rcases family_descends (prefixWord ++ tailWord_730482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730493 : List Nat := [1, 4, 1, 1, 2, 2, 11]
def baseStart_730493 : Nat := 118140960795 + 730493 * 2 ^ 59
def prefixEnd_730493 : Nat := 4983230072969 + 3 ^ 40 * 730493 * 2
def baseEnd_730493 : Nat := 9261580833207794480939

theorem tailTrace_730493 : CollatzResearch.WordTrace tailWord_730493 prefixEnd_730493 9261580833207794480939 := by
  unfold tailWord_730493
  simp only [CollatzResearch.WordTrace]
  refine ⟨26643268542556094116996133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17762179028370729411330755 26643268542556094116996133)
  ·
    refine ⟨4995612851729267646936775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26643268542556094116996133 4995612851729267646936775)
    ·
      refine ⟨7493419277593901470405163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995612851729267646936775 7493419277593901470405163)
      ·
        refine ⟨11240128916390852205607745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7493419277593901470405163 11240128916390852205607745)
        ·
          refine ⟨8430096687293139154205809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11240128916390852205607745 8430096687293139154205809)
          ·
            refine ⟨6322572515469854365654357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8430096687293139154205809 6322572515469854365654357)
            ·
              refine ⟨9261580833207794480939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6322572515469854365654357 9261580833207794480939)
              ·
                rfl

theorem cell22_730493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 11].length) (baseStart_730493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730493 prefixEnd_730493 := by exact prefixLift 730493
  have htrace : WordTrace (prefixWord ++ tailWord_730493) baseStart_730493 baseEnd_730493 := by
    simpa [prefixWord, tailWord_730493, baseEnd_730493] using wordTrace_append hprefix tailTrace_730493
  have hstable : (prefixWord ++ tailWord_730493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730493).length < 2 ^ (prefixWord ++ tailWord_730493).sum := by decide
  have hdescent : baseEnd_730493 < baseStart_730493 := by decide
  rcases family_descends (prefixWord ++ tailWord_730493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730527 : List Nat := [1, 1, 2, 5, 1, 4, 2, 6]
def baseStart_730527 : Nat := 118140960795 + 730527 * 2 ^ 59
def prefixEnd_730527 : Nat := 4983230072969 + 3 ^ 40 * 730527 * 2
def baseEnd_730527 : Nat := 27786035710160632848361

theorem tailTrace_730527 : CollatzResearch.WordTrace tailWord_730527 prefixEnd_730527 27786035710160632848361 := by
  unfold tailWord_730527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644508624432917923733835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17763005749621945282489223 26644508624432917923733835)
  ·
    refine ⟨39966762936649376885600753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26644508624432917923733835 39966762936649376885600753)
    ·
      refine ⟨29975072202487032664200565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39966762936649376885600753 29975072202487032664200565)
      ·
        refine ⟨2810163018983159312268803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29975072202487032664200565 2810163018983159312268803)
        ·
          refine ⟨4215244528474738968403205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810163018983159312268803 4215244528474738968403205)
          ·
            refine ⟨790358349089013556575601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4215244528474738968403205 790358349089013556575601)
            ·
              refine ⟨592768761816760167431701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790358349089013556575601 592768761816760167431701)
              ·
                refine ⟨27786035710160632848361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592768761816760167431701 27786035710160632848361)
                ·
                  rfl

theorem cell22_730527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 6].length) (baseStart_730527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730527 prefixEnd_730527 := by exact prefixLift 730527
  have htrace : WordTrace (prefixWord ++ tailWord_730527) baseStart_730527 baseEnd_730527 := by
    simpa [prefixWord, tailWord_730527, baseEnd_730527] using wordTrace_append hprefix tailTrace_730527
  have hstable : (prefixWord ++ tailWord_730527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730527).length < 2 ^ (prefixWord ++ tailWord_730527).sum := by decide
  have hdescent : baseEnd_730527 < baseStart_730527 := by decide
  rcases family_descends (prefixWord ++ tailWord_730527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730572 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_730572 : Nat := 118140960795 + 730572 * 2 ^ 59
def prefixEnd_730572 : Nat := 4983230072969 + 3 ^ 40 * 730572 * 2
def baseEnd_730572 : Nat := 83363241937026859420037

theorem tailTrace_730572 : CollatzResearch.WordTrace tailWord_730572 prefixEnd_730572 83363241937026859420037 := by
  unfold tailWord_730572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323074954634945304560985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17764099939513260406081313 13323074954634945304560985)
  ·
    refine ⟨9992306215976208978420739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13323074954634945304560985 9992306215976208978420739)
    ·
      refine ⟨14988459323964313467631109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992306215976208978420739 14988459323964313467631109)
      ·
        refine ⟨2810336123243308775180833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14988459323964313467631109 2810336123243308775180833)
        ·
          refine ⟨2107752092432481581385625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2810336123243308775180833 2107752092432481581385625)
          ·
            refine ⟨1580814069324361186039219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107752092432481581385625 1580814069324361186039219)
            ·
              refine ⟨2371221103986541779058829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580814069324361186039219 2371221103986541779058829)
              ·
                refine ⟨889207913994953167147061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371221103986541779058829 889207913994953167147061)
                ·
                  refine ⟨83363241937026859420037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889207913994953167147061 83363241937026859420037)
                  ·
                    rfl

theorem cell22_730572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_730572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730572 prefixEnd_730572 := by exact prefixLift 730572
  have htrace : WordTrace (prefixWord ++ tailWord_730572) baseStart_730572 baseEnd_730572 := by
    simpa [prefixWord, tailWord_730572, baseEnd_730572] using wordTrace_append hprefix tailTrace_730572
  have hstable : (prefixWord ++ tailWord_730572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730572).length < 2 ^ (prefixWord ++ tailWord_730572).sum := by decide
  have hdescent : baseEnd_730572 < baseStart_730572 := by decide
  rcases family_descends (prefixWord ++ tailWord_730572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730711 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 1, 3]
def baseStart_730711 : Nat := 118140960795 + 730711 * 2 ^ 59
def prefixEnd_730711 : Nat := 4983230072969 + 3 ^ 40 * 730711 * 2
def baseEnd_730711 : Nat := 250137308351730549034685

theorem tailTrace_730711 : CollatzResearch.WordTrace tailWord_730711 prefixEnd_730711 250137308351730549034685 := by
  unfold tailWord_730711
  simp only [CollatzResearch.WordTrace]
  refine ⟨26651219655766317348431987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17767479770510878232287991 26651219655766317348431987)
  ·
    refine ⟨39976829483649476022647981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26651219655766317348431987 39976829483649476022647981)
    ·
      refine ⟨14991311056368553508492993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39976829483649476022647981 14991311056368553508492993)
      ·
        refine ⟨11243483292276415131369745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14991311056368553508492993 11243483292276415131369745)
        ·
          refine ⟨8432612469207311348527309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11243483292276415131369745 8432612469207311348527309)
          ·
            refine ⟨3162229675952741755697741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8432612469207311348527309 3162229675952741755697741)
            ·
              refine ⟨1185836128482278158386653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3162229675952741755697741 1185836128482278158386653)
              ·
                refine ⟨444688548180854309394995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185836128482278158386653 444688548180854309394995)
                ·
                  refine ⟨667032822271281464092493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444688548180854309394995 667032822271281464092493)
                  ·
                    refine ⟨250137308351730549034685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667032822271281464092493 250137308351730549034685)
                    ·
                      rfl

theorem cell22_730711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_730711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730711 prefixEnd_730711 := by exact prefixLift 730711
  have htrace : WordTrace (prefixWord ++ tailWord_730711) baseStart_730711 baseEnd_730711 := by
    simpa [prefixWord, tailWord_730711, baseEnd_730711] using wordTrace_append hprefix tailTrace_730711
  have hstable : (prefixWord ++ tailWord_730711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730711).length < 2 ^ (prefixWord ++ tailWord_730711).sum := by decide
  have hdescent : baseEnd_730711 < baseStart_730711 := by decide
  rcases family_descends (prefixWord ++ tailWord_730711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730741 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 5]
def baseStart_730741 : Nat := 118140960795 + 730741 * 2 ^ 59
def prefixEnd_730741 : Nat := 4983230072969 + 3 ^ 40 * 730741 * 2
def baseEnd_730741 : Nat := 83382525988273490261531

theorem tailTrace_730741 : CollatzResearch.WordTrace tailWord_730741 prefixEnd_730741 83382525988273490261531 := by
  unfold tailWord_730741
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652313845657632472024077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17768209230438421648016051 26652313845657632472024077)
  ·
    refine ⟨9994617692121612177009029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26652313845657632472024077 9994617692121612177009029)
    ·
      refine ⟨1873990817272802283189193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9994617692121612177009029 1873990817272802283189193)
      ·
        refine ⟨1405493112954601712391895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1873990817272802283189193 1405493112954601712391895)
        ·
          refine ⟨2108239669431902568587843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405493112954601712391895 2108239669431902568587843)
          ·
            refine ⟨3162359504147853852881765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108239669431902568587843 3162359504147853852881765)
            ·
              refine ⟨592942407027722597415331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3162359504147853852881765 592942407027722597415331)
              ·
                refine ⟨889413610541583896122997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592942407027722597415331 889413610541583896122997)
                ·
                  refine ⟨83382525988273490261531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889413610541583896122997 83382525988273490261531)
                  ·
                    rfl

theorem cell22_730741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_730741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730741 prefixEnd_730741 := by exact prefixLift 730741
  have htrace : WordTrace (prefixWord ++ tailWord_730741) baseStart_730741 baseEnd_730741 := by
    simpa [prefixWord, tailWord_730741, baseEnd_730741] using wordTrace_append hprefix tailTrace_730741
  have hstable : (prefixWord ++ tailWord_730741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730741).length < 2 ^ (prefixWord ++ tailWord_730741).sum := by decide
  have hdescent : baseEnd_730741 < baseStart_730741 := by decide
  rcases family_descends (prefixWord ++ tailWord_730741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730822 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_730822 : Nat := 118140960795 + 730822 * 2 ^ 59
def prefixEnd_730822 : Nat := 4983230072969 + 3 ^ 40 * 730822 * 2
def baseEnd_730822 : Nat := 250175305920163259509345

theorem tailTrace_730822 : CollatzResearch.WordTrace tailWord_730822 prefixEnd_730822 250175305920163259509345 := by
  unfold tailWord_730822
  simp only [CollatzResearch.WordTrace]
  refine ⟨832977129948880728303835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17770178772242788870481813 832977129948880728303835)
  ·
    refine ⟨1249465694923321092455753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832977129948880728303835 1249465694923321092455753)
    ·
      refine ⟨937099271192490819341815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1249465694923321092455753 937099271192490819341815)
      ·
        refine ⟨1405648906788736229012723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937099271192490819341815 1405648906788736229012723)
        ·
          refine ⟨2108473360183104343519085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405648906788736229012723 2108473360183104343519085)
          ·
            refine ⟨790677510068664128819657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2108473360183104343519085 790677510068664128819657)
            ·
              refine ⟨593008132551498096614743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790677510068664128819657 593008132551498096614743)
              ·
                refine ⟨889512198827247144922115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593008132551498096614743 889512198827247144922115)
                ·
                  refine ⟨1334268298240870717383173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889512198827247144922115 1334268298240870717383173)
                  ·
                    refine ⟨250175305920163259509345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334268298240870717383173 250175305920163259509345)
                    ·
                      rfl

theorem cell22_730822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_730822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730822 prefixEnd_730822 := by exact prefixLift 730822
  have htrace : WordTrace (prefixWord ++ tailWord_730822) baseStart_730822 baseEnd_730822 := by
    simpa [prefixWord, tailWord_730822, baseEnd_730822] using wordTrace_append hprefix tailTrace_730822
  have hstable : (prefixWord ++ tailWord_730822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730822).length < 2 ^ (prefixWord ++ tailWord_730822).sum := by decide
  have hdescent : baseEnd_730822 < baseStart_730822 := by decide
  rcases family_descends (prefixWord ++ tailWord_730822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730904 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_730904 : Nat := 118140960795 + 730904 * 2 ^ 59
def prefixEnd_730904 : Nat := 4983230072969 + 3 ^ 40 * 730904 * 2
def baseEnd_730904 : Nat := 83401125398647459653031

theorem tailTrace_730904 : CollatzResearch.WordTrace tailWord_730904 prefixEnd_730904 83401125398647459653031 := by
  unfold tailWord_730904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329129472033555655103883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17772172629378074206805177 13329129472033555655103883)
  ·
    refine ⟨19993694208050333482655825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13329129472033555655103883 19993694208050333482655825)
    ·
      refine ⟨14995270656037750111991869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19993694208050333482655825 14995270656037750111991869)
      ·
        refine ⟨5623226496014156291996951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14995270656037750111991869 5623226496014156291996951)
        ·
          refine ⟨8434839744021234437995427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623226496014156291996951 8434839744021234437995427)
          ·
            refine ⟨12652259616031851656993141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434839744021234437995427 12652259616031851656993141)
            ·
              refine ⟨1186149339002986092843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12652259616031851656993141 1186149339002986092843107)
              ·
                refine ⟨1779224008504479139264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186149339002986092843107 1779224008504479139264661)
                ·
                  refine ⟨83401125398647459653031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1779224008504479139264661 83401125398647459653031)
                  ·
                    rfl

theorem cell22_730904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_730904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730904 prefixEnd_730904 := by exact prefixLift 730904
  have htrace : WordTrace (prefixWord ++ tailWord_730904) baseStart_730904 baseEnd_730904 := by
    simpa [prefixWord, tailWord_730904, baseEnd_730904] using wordTrace_append hprefix tailTrace_730904
  have hstable : (prefixWord ++ tailWord_730904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730904).length < 2 ^ (prefixWord ++ tailWord_730904).sum := by decide
  have hdescent : baseEnd_730904 < baseStart_730904 := by decide
  rcases family_descends (prefixWord ++ tailWord_730904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730910 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_730910 : Nat := 118140960795 + 730910 * 2 ^ 59
def prefixEnd_730910 : Nat := 4983230072969 + 3 ^ 40 * 730910 * 2
def baseEnd_730910 : Nat := 83401810039520121103025

theorem tailTrace_730910 : CollatzResearch.WordTrace tailWord_730910 prefixEnd_730910 83401810039520121103025 := by
  unfold tailWord_730910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332309722755671791865773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17772318521363582889950789 3332309722755671791865773)
  ·
    refine ⟨1249616146033376921949665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3332309722755671791865773 1249616146033376921949665)
    ·
      refine ⟨937212109525032691462249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1249616146033376921949665 937212109525032691462249)
      ·
        refine ⟨702909082143774518596687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 937212109525032691462249 702909082143774518596687)
        ·
          refine ⟨1054363623215661777895031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702909082143774518596687 1054363623215661777895031)
          ·
            refine ⟨1581545434823492666842547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054363623215661777895031 1581545434823492666842547)
            ·
              refine ⟨2372318152235239000263821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581545434823492666842547 2372318152235239000263821)
              ·
                refine ⟨889619307088214625098933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372318152235239000263821 889619307088214625098933)
                ·
                  refine ⟨83401810039520121103025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889619307088214625098933 83401810039520121103025)
                  ·
                    rfl

theorem cell22_730910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_730910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730910 prefixEnd_730910 := by exact prefixLift 730910
  have htrace : WordTrace (prefixWord ++ tailWord_730910) baseStart_730910 baseEnd_730910 := by
    simpa [prefixWord, tailWord_730910, baseEnd_730910] using wordTrace_append hprefix tailTrace_730910
  have hstable : (prefixWord ++ tailWord_730910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730910).length < 2 ^ (prefixWord ++ tailWord_730910).sum := by decide
  have hdescent : baseEnd_730910 < baseStart_730910 := by decide
  rcases family_descends (prefixWord ++ tailWord_730910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730994 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_730994 : Nat := 118140960795 + 730994 * 2 ^ 59
def prefixEnd_730994 : Nat := 4983230072969 + 3 ^ 40 * 730994 * 2
def baseEnd_730994 : Nat := 83411395011737381402939

theorem tailTrace_730994 : CollatzResearch.WordTrace tailWord_730994 prefixEnd_730994 83411395011737381402939 := by
  unfold tailWord_730994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665385378435264170246009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17774361009160704453989357 6665385378435264170246009)
  ·
    refine ⟨4999039033826448127684507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6665385378435264170246009 4999039033826448127684507)
    ·
      refine ⟨7498558550739672191526761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999039033826448127684507 7498558550739672191526761)
      ·
        refine ⟨5623918913054754143645071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7498558550739672191526761 5623918913054754143645071)
        ·
          refine ⟨8435878369582131215467607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623918913054754143645071 8435878369582131215467607)
          ·
            refine ⟨12653817554373196823201411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435878369582131215467607 12653817554373196823201411)
            ·
              refine ⟨18980726331559795234802117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12653817554373196823201411 18980726331559795234802117)
              ·
                refine ⟨3558886187167461606525397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18980726331559795234802117 3558886187167461606525397)
                ·
                  refine ⟨83411395011737381402939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3558886187167461606525397 83411395011737381402939)
                  ·
                    rfl

theorem cell22_730994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_730994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_730994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_730994 prefixEnd_730994 := by exact prefixLift 730994
  have htrace : WordTrace (prefixWord ++ tailWord_730994) baseStart_730994 baseEnd_730994 := by
    simpa [prefixWord, tailWord_730994, baseEnd_730994] using wordTrace_append hprefix tailTrace_730994
  have hstable : (prefixWord ++ tailWord_730994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730994).length < 2 ^ (prefixWord ++ tailWord_730994).sum := by decide
  have hdescent : baseEnd_730994 < baseStart_730994 := by decide
  rcases family_descends (prefixWord ++ tailWord_730994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731011 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 5]
def baseStart_731011 : Nat := 118140960795 + 731011 * 2 ^ 59
def prefixEnd_731011 : Nat := 4983230072969 + 3 ^ 40 * 731011 * 2
def baseEnd_731011 : Nat := 83413334827543255511255

theorem tailTrace_731011 : CollatzResearch.WordTrace tailWord_731011 prefixEnd_731011 83413334827543255511255 := by
  unfold tailWord_731011
  simp only [CollatzResearch.WordTrace]
  refine ⟨26662161554679468584352887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774774369786312389568591 26662161554679468584352887)
  ·
    refine ⟨39993242332019202876529331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26662161554679468584352887 39993242332019202876529331)
    ·
      refine ⟨59989863498028804314793997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39993242332019202876529331 59989863498028804314793997)
      ·
        refine ⟨22496198811760801618047749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59989863498028804314793997 22496198811760801618047749)
        ·
          refine ⟨4218037277205150303383953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22496198811760801618047749 4218037277205150303383953)
          ·
            refine ⟨3163527957903862727537965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4218037277205150303383953 3163527957903862727537965)
            ·
              refine ⟨1186322984213948522826737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3163527957903862727537965 1186322984213948522826737)
              ·
                refine ⟨889742238160461392120053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186322984213948522826737 889742238160461392120053)
                ·
                  refine ⟨83413334827543255511255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889742238160461392120053 83413334827543255511255)
                  ·
                    rfl

theorem cell22_731011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 5].length) (baseStart_731011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731011 prefixEnd_731011 := by exact prefixLift 731011
  have htrace : WordTrace (prefixWord ++ tailWord_731011) baseStart_731011 baseEnd_731011 := by
    simpa [prefixWord, tailWord_731011, baseEnd_731011] using wordTrace_append hprefix tailTrace_731011
  have hstable : (prefixWord ++ tailWord_731011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731011).length < 2 ^ (prefixWord ++ tailWord_731011).sum := by decide
  have hdescent : baseEnd_731011 < baseStart_731011 := by decide
  rcases family_descends (prefixWord ++ tailWord_731011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731071 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 4, 3]
def baseStart_731071 : Nat := 118140960795 + 731071 * 2 ^ 59
def prefixEnd_731071 : Nat := 4983230072969 + 3 ^ 40 * 731071 * 2
def baseEnd_731071 : Nat := 250260543708809610033581

theorem tailTrace_731071 : CollatzResearch.WordTrace tailWord_731071 prefixEnd_731071 250260543708809610033581 := by
  unfold tailWord_731071
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664349934462098831537067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17776233289641399221024711 26664349934462098831537067)
  ·
    refine ⟨39996524901693148247305601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26664349934462098831537067 39996524901693148247305601)
    ·
      refine ⟨29997393676269861185479201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39996524901693148247305601 29997393676269861185479201)
      ·
        refine ⟨22498045257202395889109401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29997393676269861185479201 22498045257202395889109401)
        ·
          refine ⟨16873533942901796916832051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22498045257202395889109401 16873533942901796916832051)
          ·
            refine ⟨25310300914352695375248077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873533942901796916832051 25310300914352695375248077)
            ·
              refine ⟨9491362842882260765718029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25310300914352695375248077 9491362842882260765718029)
              ·
                refine ⟨3559261066080847787144261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9491362842882260765718029 3559261066080847787144261)
                ·
                  refine ⟨667361449890158960089549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3559261066080847787144261 667361449890158960089549)
                  ·
                    refine ⟨250260543708809610033581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667361449890158960089549 250260543708809610033581)
                    ·
                      rfl

theorem cell22_731071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_731071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731071 prefixEnd_731071 := by exact prefixLift 731071
  have htrace : WordTrace (prefixWord ++ tailWord_731071) baseStart_731071 baseEnd_731071 := by
    simpa [prefixWord, tailWord_731071, baseEnd_731071] using wordTrace_append hprefix tailTrace_731071
  have hstable : (prefixWord ++ tailWord_731071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731071).length < 2 ^ (prefixWord ++ tailWord_731071).sum := by decide
  have hdescent : baseEnd_731071 < baseStart_731071 := by decide
  rcases family_descends (prefixWord ++ tailWord_731071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731086 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_731086 : Nat := 118140960795 + 731086 * 2 ^ 59
def prefixEnd_731086 : Nat := 4983230072969 + 3 ^ 40 * 731086 * 2
def baseEnd_731086 : Nat := 250265678515354570908535

theorem tailTrace_731086 : CollatzResearch.WordTrace tailWord_731086 prefixEnd_731086 250265678515354570908535 := by
  unfold tailWord_731086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333112128675969549166639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17776598019605170928888741 3333112128675969549166639)
  ·
    refine ⟨4999668193013954323749959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333112128675969549166639 4999668193013954323749959)
    ·
      refine ⟨7499502289520931485624939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999668193013954323749959 7499502289520931485624939)
      ·
        refine ⟨11249253434281397228437409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499502289520931485624939 11249253434281397228437409)
        ·
          refine ⟨8436940075711047921328057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11249253434281397228437409 8436940075711047921328057)
          ·
            refine ⟨6327705056783285940996043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8436940075711047921328057 6327705056783285940996043)
            ·
              refine ⟨9491557585174928911494065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327705056783285940996043 9491557585174928911494065)
              ·
                refine ⟨7118668188881196683620549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9491557585174928911494065 7118668188881196683620549)
                ·
                  refine ⟨1334750285415224378178853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7118668188881196683620549 1334750285415224378178853)
                  ·
                    refine ⟨250265678515354570908535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334750285415224378178853 250265678515354570908535)
                    ·
                      rfl

theorem cell22_731086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_731086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731086 prefixEnd_731086 := by exact prefixLift 731086
  have htrace : WordTrace (prefixWord ++ tailWord_731086) baseStart_731086 baseEnd_731086 := by
    simpa [prefixWord, tailWord_731086, baseEnd_731086] using wordTrace_append hprefix tailTrace_731086
  have hstable : (prefixWord ++ tailWord_731086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731086).length < 2 ^ (prefixWord ++ tailWord_731086).sum := by decide
  have hdescent : baseEnd_731086 < baseStart_731086 := by decide
  rcases family_descends (prefixWord ++ tailWord_731086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731103 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 2, 4]
def baseStart_731103 : Nat := 118140960795 + 731103 * 2 ^ 59
def prefixEnd_731103 : Nat := 4983230072969 + 3 ^ 40 * 731103 * 2
def baseEnd_731103 : Nat := 250271497962772193233483

theorem tailTrace_731103 : CollatzResearch.WordTrace tailWord_731103 prefixEnd_731103 250271497962772193233483 := by
  unfold tailWord_731103
  simp only [CollatzResearch.WordTrace]
  refine ⟨26665517070346168296701963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17777011380230778864467975 26665517070346168296701963)
  ·
    refine ⟨39998275605519252445052945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26665517070346168296701963 39998275605519252445052945)
    ·
      refine ⟨29998706704139439333789709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39998275605519252445052945 29998706704139439333789709)
      ·
        refine ⟨11249515014052289750171141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29998706704139439333789709 11249515014052289750171141)
        ·
          refine ⟨2109284065134804328157089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11249515014052289750171141 2109284065134804328157089)
          ·
            refine ⟨1581963048851103246117817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109284065134804328157089 1581963048851103246117817)
            ·
              refine ⟨1186472286638327434588363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581963048851103246117817 1186472286638327434588363)
              ·
                refine ⟨1779708429957491151882545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186472286638327434588363 1779708429957491151882545)
                ·
                  refine ⟨1334781322468118363911909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779708429957491151882545 1334781322468118363911909)
                  ·
                    refine ⟨250271497962772193233483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334781322468118363911909 250271497962772193233483)
                    ·
                      rfl

theorem cell22_731103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_731103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731103 prefixEnd_731103 := by exact prefixLift 731103
  have htrace : WordTrace (prefixWord ++ tailWord_731103) baseStart_731103 baseEnd_731103 := by
    simpa [prefixWord, tailWord_731103, baseEnd_731103] using wordTrace_append hprefix tailTrace_731103
  have hstable : (prefixWord ++ tailWord_731103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731103).length < 2 ^ (prefixWord ++ tailWord_731103).sum := by decide
  have hdescent : baseEnd_731103 < baseStart_731103 := by decide
  rcases family_descends (prefixWord ++ tailWord_731103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731178 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_731178 : Nat := 118140960795 + 731178 * 2 ^ 59
def prefixEnd_731178 : Nat := 4983230072969 + 3 ^ 40 * 731178 * 2
def baseEnd_731178 : Nat := 250297171995496997608253

theorem tailTrace_731178 : CollatzResearch.WordTrace tailWord_731178 prefixEnd_731178 250297171995496997608253 := by
  unfold tailWord_731178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667063136268614026420547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17778835030049637403788125 6667063136268614026420547)
  ·
    refine ⟨10000594704402921039630821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667063136268614026420547 10000594704402921039630821)
    ·
      refine ⟨1875111507075547694930779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10000594704402921039630821 1875111507075547694930779)
      ·
        refine ⟨2812667260613321542396169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875111507075547694930779 2812667260613321542396169)
        ·
          refine ⟨2109500445459991156797127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2812667260613321542396169 2109500445459991156797127)
          ·
            refine ⟨3164250668189986735195691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109500445459991156797127 3164250668189986735195691)
            ·
              refine ⟨4746376002284980102793537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164250668189986735195691 4746376002284980102793537)
              ·
                refine ⟨3559782001713735077095153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4746376002284980102793537 3559782001713735077095153)
                ·
                  refine ⟨2669836501285301307821365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559782001713735077095153 2669836501285301307821365)
                  ·
                    refine ⟨250297171995496997608253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2669836501285301307821365 250297171995496997608253)
                    ·
                      rfl

theorem cell22_731178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_731178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731178 prefixEnd_731178 := by exact prefixLift 731178
  have htrace : WordTrace (prefixWord ++ tailWord_731178) baseStart_731178 baseEnd_731178 := by
    simpa [prefixWord, tailWord_731178, baseEnd_731178] using wordTrace_append hprefix tailTrace_731178
  have hstable : (prefixWord ++ tailWord_731178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731178).length < 2 ^ (prefixWord ++ tailWord_731178).sum := by decide
  have hdescent : baseEnd_731178 < baseStart_731178 := by decide
  rcases family_descends (prefixWord ++ tailWord_731178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731191 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 6]
def baseStart_731191 : Nat := 118140960795 + 731191 * 2 ^ 59
def prefixEnd_731191 : Nat := 4983230072969 + 3 ^ 40 * 731191 * 2
def baseEnd_731191 : Nat := 83433874053723099011071

theorem tailTrace_731191 : CollatzResearch.WordTrace tailWord_731191 prefixEnd_731191 83433874053723099011071 := by
  unfold tailWord_731191
  simp only [CollatzResearch.WordTrace]
  refine ⟨26668726694027359325905427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17779151129351572883936951 26668726694027359325905427)
  ·
    refine ⟨40003090041041038988858141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26668726694027359325905427 40003090041041038988858141)
    ·
      refine ⟨15001158765390389620821803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40003090041041038988858141 15001158765390389620821803)
      ·
        refine ⟨22501738148085584431232705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15001158765390389620821803 22501738148085584431232705)
        ·
          refine ⟨16876303611064188323424529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22501738148085584431232705 16876303611064188323424529)
          ·
            refine ⟨12657227708298141242568397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16876303611064188323424529 12657227708298141242568397)
            ·
              refine ⟨4746460390611802965963149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12657227708298141242568397 4746460390611802965963149)
              ·
                refine ⟨1779922646479426112236181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4746460390611802965963149 1779922646479426112236181)
                ·
                  refine ⟨83433874053723099011071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1779922646479426112236181 83433874053723099011071)
                  ·
                    rfl

theorem cell22_731191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_731191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731191 prefixEnd_731191 := by exact prefixLift 731191
  have htrace : WordTrace (prefixWord ++ tailWord_731191) baseStart_731191 baseEnd_731191 := by
    simpa [prefixWord, tailWord_731191, baseEnd_731191] using wordTrace_append hprefix tailTrace_731191
  have hstable : (prefixWord ++ tailWord_731191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731191).length < 2 ^ (prefixWord ++ tailWord_731191).sum := by decide
  have hdescent : baseEnd_731191 < baseStart_731191 := by decide
  rcases family_descends (prefixWord ++ tailWord_731191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731223 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 4, 3]
def baseStart_731223 : Nat := 118140960795 + 731223 * 2 ^ 59
def prefixEnd_731223 : Nat := 4983230072969 + 3 ^ 40 * 731223 * 2
def baseEnd_731223 : Nat := 250312576415131880233115

theorem tailTrace_731223 : CollatzResearch.WordTrace tailWord_731223 prefixEnd_731223 250312576415131880233115 := by
  unfold tailWord_731223
  simp only [CollatzResearch.WordTrace]
  refine ⟨26669893829911428791070323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17779929219940952527380215 26669893829911428791070323)
  ·
    refine ⟨40004840744867143186605485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26669893829911428791070323 40004840744867143186605485)
    ·
      refine ⟨15001815279325178694977057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40004840744867143186605485 15001815279325178694977057)
      ·
        refine ⟨11251361459493884021232793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15001815279325178694977057 11251361459493884021232793)
        ·
          refine ⟨8438521094620413015924595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11251361459493884021232793 8438521094620413015924595)
          ·
            refine ⟨12657781641930619523886893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8438521094620413015924595 12657781641930619523886893)
            ·
              refine ⟨4746668115723982321457585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12657781641930619523886893 4746668115723982321457585)
              ·
                refine ⟨3560001086792986741093189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4746668115723982321457585 3560001086792986741093189)
                ·
                  refine ⟨667500203773685013954973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3560001086792986741093189 667500203773685013954973)
                  ·
                    refine ⟨250312576415131880233115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667500203773685013954973 250312576415131880233115)
                    ·
                      rfl

theorem cell22_731223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_731223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731223 prefixEnd_731223 := by exact prefixLift 731223
  have htrace : WordTrace (prefixWord ++ tailWord_731223) baseStart_731223 baseEnd_731223 := by
    simpa [prefixWord, tailWord_731223, baseEnd_731223] using wordTrace_append hprefix tailTrace_731223
  have hstable : (prefixWord ++ tailWord_731223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731223).length < 2 ^ (prefixWord ++ tailWord_731223).sum := by decide
  have hdescent : baseEnd_731223 < baseStart_731223 := by decide
  rcases family_descends (prefixWord ++ tailWord_731223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731236 : List Nat := [2, 3, 1, 1, 2, 1, 12]
def baseStart_731236 : Nat := 118140960795 + 731236 * 2 ^ 59
def prefixEnd_731236 : Nat := 4983230072969 + 3 ^ 40 * 731236 * 2
def baseEnd_731236 : Nat := 9271000984474228876225

theorem tailTrace_731236 : CollatzResearch.WordTrace tailWord_731236 prefixEnd_731236 9271000984474228876225 := by
  unfold tailWord_731236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335183989432166005646781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17780245319242888007529041 13335183989432166005646781)
  ·
    refine ⟨5000693996037062252117543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13335183989432166005646781 5000693996037062252117543)
    ·
      refine ⟨7501040994055593378176315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5000693996037062252117543 7501040994055593378176315)
      ·
        refine ⟨11251561491083390067264473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501040994055593378176315 11251561491083390067264473)
        ·
          refine ⟨8438671118312542550448355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11251561491083390067264473 8438671118312542550448355)
          ·
            refine ⟨12658006677468813825672533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8438671118312542550448355 12658006677468813825672533)
            ·
              refine ⟨9271000984474228876225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 12658006677468813825672533 9271000984474228876225)
              ·
                rfl

theorem cell22_731236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 12].length) (baseStart_731236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731236 prefixEnd_731236 := by exact prefixLift 731236
  have htrace : WordTrace (prefixWord ++ tailWord_731236) baseStart_731236 baseEnd_731236 := by
    simpa [prefixWord, tailWord_731236, baseEnd_731236] using wordTrace_append hprefix tailTrace_731236
  have hstable : (prefixWord ++ tailWord_731236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731236).length < 2 ^ (prefixWord ++ tailWord_731236).sum := by decide
  have hdescent : baseEnd_731236 < baseStart_731236 := by decide
  rcases family_descends (prefixWord ++ tailWord_731236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731242 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_731242 : Nat := 118140960795 + 731242 * 2 ^ 59
def prefixEnd_731242 : Nat := 4983230072969 + 3 ^ 40 * 731242 * 2
def baseEnd_731242 : Nat := 83439693501140721336019

theorem tailTrace_731242 : CollatzResearch.WordTrace tailWord_731242 prefixEnd_731242 83439693501140721336019 := by
  unfold tailWord_731242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667646704210648759002995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17780391211228396690674653 6667646704210648759002995)
  ·
    refine ⟨10001470056315973138504493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667646704210648759002995 10001470056315973138504493)
    ·
      refine ⟨3750551271118489926939185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10001470056315973138504493 3750551271118489926939185)
      ·
        refine ⟨2812913453338867445204389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3750551271118489926939185 2812913453338867445204389)
        ·
          refine ⟨527421272501037645975823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2812913453338867445204389 527421272501037645975823)
          ·
            refine ⟨791131908751556468963735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527421272501037645975823 791131908751556468963735)
            ·
              refine ⟨1186697863127334703445603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791131908751556468963735 1186697863127334703445603)
              ·
                refine ⟨1780046794691002055168405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186697863127334703445603 1780046794691002055168405)
                ·
                  refine ⟨83439693501140721336019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1780046794691002055168405 83439693501140721336019)
                  ·
                    rfl

theorem cell22_731242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_731242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731242 prefixEnd_731242 := by exact prefixLift 731242
  have htrace : WordTrace (prefixWord ++ tailWord_731242) baseStart_731242 baseEnd_731242 := by
    simpa [prefixWord, tailWord_731242, baseEnd_731242] using wordTrace_append hprefix tailTrace_731242
  have hstable : (prefixWord ++ tailWord_731242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731242).length < 2 ^ (prefixWord ++ tailWord_731242).sum := by decide
  have hdescent : baseEnd_731242 < baseStart_731242 := by decide
  rcases family_descends (prefixWord ++ tailWord_731242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731257 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_731257 : Nat := 118140960795 + 731257 * 2 ^ 59
def prefixEnd_731257 : Nat := 4983230072969 + 3 ^ 40 * 731257 * 2
def baseEnd_731257 : Nat := 250324215309967124883011

theorem tailTrace_731257 : CollatzResearch.WordTrace tailWord_731257 prefixEnd_731257 250324215309967124883011 := by
  unfold tailWord_731257
  simp only [CollatzResearch.WordTrace]
  refine ⟨26671133911788252597808025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17780755941192168398538683 26671133911788252597808025)
  ·
    refine ⟨20003350433841189448356019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26671133911788252597808025 20003350433841189448356019)
    ·
      refine ⟨30005025650761784172534029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20003350433841189448356019 30005025650761784172534029)
      ·
        refine ⟨11251884619035669064700261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30005025650761784172534029 11251884619035669064700261)
        ·
          refine ⟨2109728366069187949631299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11251884619035669064700261 2109728366069187949631299)
          ·
            refine ⟨3164592549103781924446949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109728366069187949631299 3164592549103781924446949)
            ·
              refine ⟨593361102956959110833803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3164592549103781924446949 593361102956959110833803)
              ·
                refine ⟨890041654435438666250705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593361102956959110833803 890041654435438666250705)
                ·
                  refine ⟨667531240826578999688029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890041654435438666250705 667531240826578999688029)
                  ·
                    refine ⟨250324215309967124883011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667531240826578999688029 250324215309967124883011)
                    ·
                      rfl

theorem cell22_731257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_731257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731257 prefixEnd_731257 := by exact prefixLift 731257
  have htrace : WordTrace (prefixWord ++ tailWord_731257) baseStart_731257 baseEnd_731257 := by
    simpa [prefixWord, tailWord_731257, baseEnd_731257] using wordTrace_append hprefix tailTrace_731257
  have hstable : (prefixWord ++ tailWord_731257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731257).length < 2 ^ (prefixWord ++ tailWord_731257).sum := by decide
  have hdescent : baseEnd_731257 < baseStart_731257 := by decide
  rcases family_descends (prefixWord ++ tailWord_731257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731349 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 5]
def baseStart_731349 : Nat := 118140960795 + 731349 * 2 ^ 59
def prefixEnd_731349 : Nat := 4983230072969 + 3 ^ 40 * 731349 * 2
def baseEnd_731349 : Nat := 83451902930036517194243

theorem tailTrace_731349 : CollatzResearch.WordTrace tailWord_731349 prefixEnd_731349 83451902930036517194243 := by
  unfold tailWord_731349
  simp only [CollatzResearch.WordTrace]
  refine ⟨26674489427454952310157101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17782992951636634873438067 26674489427454952310157101)
  ·
    refine ⟨10002933535295607116308913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26674489427454952310157101 10002933535295607116308913)
    ·
      refine ⟨7502200151471705337231685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10002933535295607116308913 7502200151471705337231685)
      ·
        refine ⟨1406662528400944750730941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7502200151471705337231685 1406662528400944750730941)
        ·
          refine ⟨527498448150354281524103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1406662528400944750730941 527498448150354281524103)
          ·
            refine ⟨791247672225531422286155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527498448150354281524103 791247672225531422286155)
            ·
              refine ⟨1186871508338297133429233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791247672225531422286155 1186871508338297133429233)
              ·
                refine ⟨890153631253722850071925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186871508338297133429233 890153631253722850071925)
                ·
                  refine ⟨83451902930036517194243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890153631253722850071925 83451902930036517194243)
                  ·
                    rfl

theorem cell22_731349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_731349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731349 prefixEnd_731349 := by exact prefixLift 731349
  have htrace : WordTrace (prefixWord ++ tailWord_731349) baseStart_731349 baseEnd_731349 := by
    simpa [prefixWord, tailWord_731349, baseEnd_731349] using wordTrace_append hprefix tailTrace_731349
  have hstable : (prefixWord ++ tailWord_731349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731349).length < 2 ^ (prefixWord ++ tailWord_731349).sum := by decide
  have hdescent : baseEnd_731349 < baseStart_731349 := by decide
  rcases family_descends (prefixWord ++ tailWord_731349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731360 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_731360 : Nat := 118140960795 + 731360 * 2 ^ 59
def prefixEnd_731360 : Nat := 4983230072969 + 3 ^ 40 * 731360 * 2
def baseEnd_731360 : Nat := 83453158104969729852565

theorem tailTrace_731360 : CollatzResearch.WordTrace tailWord_731360 prefixEnd_731360 83453158104969729852565 := by
  unfold tailWord_731360
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337445315207550594403767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17783260420276734125871689 13337445315207550594403767)
  ·
    refine ⟨20006167972811325891605651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13337445315207550594403767 20006167972811325891605651)
    ·
      refine ⟨30009251959216988837408477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20006167972811325891605651 30009251959216988837408477)
      ·
        refine ⟨11253469484706370814028179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30009251959216988837408477 11253469484706370814028179)
        ·
          refine ⟨16880204227059556221042269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11253469484706370814028179 16880204227059556221042269)
          ·
            refine ⟨6330076585147333582890851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16880204227059556221042269 6330076585147333582890851)
            ·
              refine ⟨9495114877721000374336277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330076585147333582890851 9495114877721000374336277)
              ·
                refine ⟨445083509893171892547013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9495114877721000374336277 445083509893171892547013)
                ·
                  refine ⟨83453158104969729852565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445083509893171892547013 83453158104969729852565)
                  ·
                    rfl

theorem cell22_731360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_731360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731360 prefixEnd_731360 := by exact prefixLift 731360
  have htrace : WordTrace (prefixWord ++ tailWord_731360) baseStart_731360 baseEnd_731360 := by
    simpa [prefixWord, tailWord_731360, baseEnd_731360] using wordTrace_append hprefix tailTrace_731360
  have hstable : (prefixWord ++ tailWord_731360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731360).length < 2 ^ (prefixWord ++ tailWord_731360).sum := by decide
  have hdescent : baseEnd_731360 < baseStart_731360 := by decide
  rcases family_descends (prefixWord ++ tailWord_731360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731375 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 1, 5]
def baseStart_731375 : Nat := 118140960795 + 731375 * 2 ^ 59
def prefixEnd_731375 : Nat := 4983230072969 + 3 ^ 40 * 731375 * 2
def baseEnd_731375 : Nat := 250364609121454150432649

theorem tailTrace_731375 : CollatzResearch.WordTrace tailWord_731375 prefixEnd_731375 250364609121454150432649 := by
  unfold tailWord_731375
  simp only [CollatzResearch.WordTrace]
  refine ⟨26675437725360758750603579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17783625150240505833735719 26675437725360758750603579)
  ·
    refine ⟨40013156588041138125905369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26675437725360758750603579 40013156588041138125905369)
    ·
      refine ⟨30009867441030853594429027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40013156588041138125905369 30009867441030853594429027)
      ·
        refine ⟨45014801161546280391643541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30009867441030853594429027 45014801161546280391643541)
        ·
          refine ⟨2110068804447481893358291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45014801161546280391643541 2110068804447481893358291)
          ·
            refine ⟨3165103206671222840037437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110068804447481893358291 3165103206671222840037437)
            ·
              refine ⟨1186913702501708565014039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3165103206671222840037437 1186913702501708565014039)
              ·
                refine ⟨1780370553752562847521059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186913702501708565014039 1780370553752562847521059)
                ·
                  refine ⟨2670555830628844271281589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780370553752562847521059 2670555830628844271281589)
                  ·
                    refine ⟨250364609121454150432649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2670555830628844271281589 250364609121454150432649)
                    ·
                      rfl

theorem cell22_731375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_731375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731375 prefixEnd_731375 := by exact prefixLift 731375
  have htrace : WordTrace (prefixWord ++ tailWord_731375) baseStart_731375 baseEnd_731375 := by
    simpa [prefixWord, tailWord_731375, baseEnd_731375] using wordTrace_append hprefix tailTrace_731375
  have hstable : (prefixWord ++ tailWord_731375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731375).length < 2 ^ (prefixWord ++ tailWord_731375).sum := by decide
  have hdescent : baseEnd_731375 < baseStart_731375 := by decide
  rcases family_descends (prefixWord ++ tailWord_731375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731390 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_731390 : Nat := 118140960795 + 731390 * 2 ^ 59
def prefixEnd_731390 : Nat := 4983230072969 + 3 ^ 40 * 731390 * 2
def baseEnd_731390 : Nat := 250369743927999111307603

theorem tailTrace_731390 : CollatzResearch.WordTrace tailWord_731390 prefixEnd_731390 250369743927999111307603 := by
  unfold tailWord_731390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334498102538302039049953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17783989880204277541599749 3334498102538302039049953)
  ·
    refine ⟨2500873576903726529287465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3334498102538302039049953 2500873576903726529287465)
    ·
      refine ⟨1875655182677794896965599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2500873576903726529287465 1875655182677794896965599)
      ·
        refine ⟨2813482774016692345448399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875655182677794896965599 2813482774016692345448399)
        ·
          refine ⟨4220224161025038518172599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813482774016692345448399 4220224161025038518172599)
          ·
            refine ⟨6330336241537557777258899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220224161025038518172599 6330336241537557777258899)
            ·
              refine ⟨9495504362306336665888349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330336241537557777258899 9495504362306336665888349)
              ·
                refine ⟨3560814135864876249708131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9495504362306336665888349 3560814135864876249708131)
                ·
                  refine ⟨5341221203797314374562197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560814135864876249708131 5341221203797314374562197)
                  ·
                    refine ⟨250369743927999111307603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5341221203797314374562197 250369743927999111307603)
                    ·
                      rfl

theorem cell22_731390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_731390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731390 prefixEnd_731390 := by exact prefixLift 731390
  have htrace : WordTrace (prefixWord ++ tailWord_731390) baseStart_731390 baseEnd_731390 := by
    simpa [prefixWord, tailWord_731390, baseEnd_731390] using wordTrace_append hprefix tailTrace_731390
  have hstable : (prefixWord ++ tailWord_731390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731390).length < 2 ^ (prefixWord ++ tailWord_731390).sum := by decide
  have hdescent : baseEnd_731390 < baseStart_731390 := by decide
  rcases family_descends (prefixWord ++ tailWord_731390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731394 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_731394 : Nat := 118140960795 + 731394 * 2 ^ 59
def prefixEnd_731394 : Nat := 4983230072969 + 3 ^ 40 * 731394 * 2
def baseEnd_731394 : Nat := 83457037736581478069197

theorem tailTrace_731394 : CollatzResearch.WordTrace tailWord_731394 prefixEnd_731394 83457037736581478069197 := by
  unfold tailWord_731394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669032678072981248886309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17784087141527949997030157 6669032678072981248886309)
  ·
    refine ⟨1250443627138683984166183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6669032678072981248886309 1250443627138683984166183)
    ·
      refine ⟨1875665440708025976249275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250443627138683984166183 1875665440708025976249275)
      ·
        refine ⟨2813498161062038964373913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875665440708025976249275 2813498161062038964373913)
        ·
          refine ⟨2110123620796529223280435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2813498161062038964373913 2110123620796529223280435)
          ·
            refine ⟨3165185431194793834920653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110123620796529223280435 3165185431194793834920653)
            ·
              refine ⟨1186944536698047688095245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3165185431194793834920653 1186944536698047688095245)
              ·
                refine ⟨445104201261767883035717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1186944536698047688095245 445104201261767883035717)
                ·
                  refine ⟨83457037736581478069197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445104201261767883035717 83457037736581478069197)
                  ·
                    rfl

theorem cell22_731394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_731394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731394 prefixEnd_731394 := by exact prefixLift 731394
  have htrace : WordTrace (prefixWord ++ tailWord_731394) baseStart_731394 baseEnd_731394 := by
    simpa [prefixWord, tailWord_731394, baseEnd_731394] using wordTrace_append hprefix tailTrace_731394
  have hstable : (prefixWord ++ tailWord_731394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731394).length < 2 ^ (prefixWord ++ tailWord_731394).sum := by decide
  have hdescent : baseEnd_731394 < baseStart_731394 := by decide
  rcases family_descends (prefixWord ++ tailWord_731394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731422 : List Nat := [4, 3, 2, 1, 1, 1, 1, 9]
def baseStart_731422 : Nat := 118140960795 + 731422 * 2 ^ 59
def prefixEnd_731422 : Nat := 4983230072969 + 3 ^ 40 * 731422 * 2
def baseEnd_731422 : Nat := 27820077575773521611945

theorem tailTrace_731422 : CollatzResearch.WordTrace tailWord_731422 prefixEnd_731422 27820077575773521611945 := by
  unfold tailWord_731422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334643994523810722195565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17784767970793657185043013 3334643994523810722195565)
  ·
    refine ⟨1250491497946429020823337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3334643994523810722195565 1250491497946429020823337)
    ·
      refine ⟨937868623459821765617503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250491497946429020823337 937868623459821765617503)
      ·
        refine ⟨1406802935189732648426255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937868623459821765617503 1406802935189732648426255)
        ·
          refine ⟨2110204402784598972639383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406802935189732648426255 2110204402784598972639383)
          ·
            refine ⟨3165306604176898458959075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110204402784598972639383 3165306604176898458959075)
            ·
              refine ⟨4747959906265347688438613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165306604176898458959075 4747959906265347688438613)
              ·
                refine ⟨27820077575773521611945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4747959906265347688438613 27820077575773521611945)
                ·
                  rfl

theorem cell22_731422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_731422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731422 prefixEnd_731422 := by exact prefixLift 731422
  have htrace : WordTrace (prefixWord ++ tailWord_731422) baseStart_731422 baseEnd_731422 := by
    simpa [prefixWord, tailWord_731422, baseEnd_731422] using wordTrace_append hprefix tailTrace_731422
  have hstable : (prefixWord ++ tailWord_731422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731422).length < 2 ^ (prefixWord ++ tailWord_731422).sum := by decide
  have hdescent : baseEnd_731422 < baseStart_731422 := by decide
  rcases family_descends (prefixWord ++ tailWord_731422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731426 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_731426 : Nat := 118140960795 + 731426 * 2 ^ 59
def prefixEnd_731426 : Nat := 4983230072969 + 3 ^ 40 * 731426 * 2
def baseEnd_731426 : Nat := 250382067463707017407493

theorem tailTrace_731426 : CollatzResearch.WordTrace tailWord_731426 prefixEnd_731426 250382067463707017407493 := by
  unfold tailWord_731426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669324462043998615177533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17784865232117329640473421 6669324462043998615177533)
  ·
    refine ⟨2500996673266499480691575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6669324462043998615177533 2500996673266499480691575)
    ·
      refine ⟨3751495009899749221037363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500996673266499480691575 3751495009899749221037363)
      ·
        refine ⟨5627242514849623831556045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751495009899749221037363 5627242514849623831556045)
        ·
          refine ⟨2110215943068608936833517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5627242514849623831556045 2110215943068608936833517)
          ·
            refine ⟨791330978650728351312569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2110215943068608936833517 791330978650728351312569)
            ·
              refine ⟨593498233988046263484427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791330978650728351312569 593498233988046263484427)
              ·
                refine ⟨890247350982069395226641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593498233988046263484427 890247350982069395226641)
                ·
                  refine ⟨667685513236552046419981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890247350982069395226641 667685513236552046419981)
                  ·
                    refine ⟨250382067463707017407493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667685513236552046419981 250382067463707017407493)
                    ·
                      rfl

theorem cell22_731426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_731426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731426 prefixEnd_731426 := by exact prefixLift 731426
  have htrace : WordTrace (prefixWord ++ tailWord_731426) baseStart_731426 baseEnd_731426 := by
    simpa [prefixWord, tailWord_731426, baseEnd_731426] using wordTrace_append hprefix tailTrace_731426
  have hstable : (prefixWord ++ tailWord_731426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731426).length < 2 ^ (prefixWord ++ tailWord_731426).sum := by decide
  have hdescent : baseEnd_731426 < baseStart_731426 := by decide
  rcases family_descends (prefixWord ++ tailWord_731426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731495 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 8]
def baseStart_731495 : Nat := 118140960795 + 731495 * 2 ^ 59
def prefixEnd_731495 : Nat := 4983230072969 + 3 ^ 40 * 731495 * 2
def baseEnd_731495 : Nat := 83468562524604612477427

theorem tailTrace_731495 : CollatzResearch.WordTrace tailWord_731495 prefixEnd_731495 83468562524604612477427 := by
  unfold tailWord_731495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26679814484926019244971939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17786542989950679496647959 26679814484926019244971939)
  ·
    refine ⟨40019721727389028867457909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26679814484926019244971939 40019721727389028867457909)
    ·
      refine ⟨3751848911942721456324179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40019721727389028867457909 3751848911942721456324179)
      ·
        refine ⟨5627773367914082184486269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751848911942721456324179 5627773367914082184486269)
        ·
          refine ⟨2110415012967780819182351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5627773367914082184486269 2110415012967780819182351)
          ·
            refine ⟨3165622519451671228773527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110415012967780819182351 3165622519451671228773527)
            ·
              refine ⟨4748433779177506843160291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165622519451671228773527 4748433779177506843160291)
              ·
                refine ⟨7122650668766260264740437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748433779177506843160291 7122650668766260264740437)
                ·
                  refine ⟨83468562524604612477427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7122650668766260264740437 83468562524604612477427)
                  ·
                    rfl

theorem cell22_731495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_731495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731495 prefixEnd_731495 := by exact prefixLift 731495
  have htrace : WordTrace (prefixWord ++ tailWord_731495) baseStart_731495 baseEnd_731495 := by
    simpa [prefixWord, tailWord_731495, baseEnd_731495] using wordTrace_append hprefix tailTrace_731495
  have hstable : (prefixWord ++ tailWord_731495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731495).length < 2 ^ (prefixWord ++ tailWord_731495).sum := by decide
  have hdescent : baseEnd_731495 < baseStart_731495 := by decide
  rcases family_descends (prefixWord ++ tailWord_731495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731525 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_731525 : Nat := 118140960795 + 731525 * 2 ^ 59
def prefixEnd_731525 : Nat := 4983230072969 + 3 ^ 40 * 731525 * 2
def baseEnd_731525 : Nat := 250415957186903759182189

theorem tailTrace_731525 : CollatzResearch.WordTrace tailWord_731525 prefixEnd_731525 250415957186903759182189 := by
  unfold tailWord_731525
  simp only [CollatzResearch.WordTrace]
  refine ⟨26680908674817334368564029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17787272449878222912376019 26680908674817334368564029)
  ·
    refine ⟨10005340753056500388211511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26680908674817334368564029 10005340753056500388211511)
    ·
      refine ⟨15008011129584750582317267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10005340753056500388211511 15008011129584750582317267)
      ·
        refine ⟨22512016694377125873475901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15008011129584750582317267 22512016694377125873475901)
        ·
          refine ⟨8442006260391422202553463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22512016694377125873475901 8442006260391422202553463)
          ·
            refine ⟨12663009390587133303830195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442006260391422202553463 12663009390587133303830195)
            ·
              refine ⟨18994514085880699955745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663009390587133303830195 18994514085880699955745293)
              ·
                refine ⟨7122942782205262483404485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18994514085880699955745293 7122942782205262483404485)
                ·
                  refine ⟨1335551771663486715638341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7122942782205262483404485 1335551771663486715638341)
                  ·
                    refine ⟨250415957186903759182189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335551771663486715638341 250415957186903759182189)
                    ·
                      rfl

theorem cell22_731525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_731525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731525 prefixEnd_731525 := by exact prefixLift 731525
  have htrace : WordTrace (prefixWord ++ tailWord_731525) baseStart_731525 baseEnd_731525 := by
    simpa [prefixWord, tailWord_731525, baseEnd_731525] using wordTrace_append hprefix tailTrace_731525
  have hstable : (prefixWord ++ tailWord_731525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731525).length < 2 ^ (prefixWord ++ tailWord_731525).sum := by decide
  have hdescent : baseEnd_731525 < baseStart_731525 := by decide
  rcases family_descends (prefixWord ++ tailWord_731525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731527 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 4, 3]
def baseStart_731527 : Nat := 118140960795 + 731527 * 2 ^ 59
def prefixEnd_731527 : Nat := 4983230072969 + 3 ^ 40 * 731527 * 2
def baseEnd_731527 : Nat := 250416641827776420632183

theorem tailTrace_731527 : CollatzResearch.WordTrace tailWord_731527 prefixEnd_731527 250416641827776420632183 := by
  unfold tailWord_731527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26680981620810088710136835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17787321080540059140091223 26680981620810088710136835)
  ·
    refine ⟨40021472431215133065205253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26680981620810088710136835 40021472431215133065205253)
    ·
      refine ⟨7504026080852837449725985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40021472431215133065205253 7504026080852837449725985)
      ·
        refine ⟨5628019560639628087294489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7504026080852837449725985 5628019560639628087294489)
        ·
          refine ⟨4221014670479721065470867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5628019560639628087294489 4221014670479721065470867)
          ·
            refine ⟨6331522005719581598206301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221014670479721065470867 6331522005719581598206301)
            ·
              refine ⟨2374320752144843099327363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6331522005719581598206301 2374320752144843099327363)
              ·
                refine ⟨3561481128217264648991045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374320752144843099327363 3561481128217264648991045)
                ·
                  refine ⟨667777711540737121685821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3561481128217264648991045 667777711540737121685821)
                  ·
                    refine ⟨250416641827776420632183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667777711540737121685821 250416641827776420632183)
                    ·
                      rfl

theorem cell22_731527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_731527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731527 prefixEnd_731527 := by exact prefixLift 731527
  have htrace : WordTrace (prefixWord ++ tailWord_731527) baseStart_731527 baseEnd_731527 := by
    simpa [prefixWord, tailWord_731527, baseEnd_731527] using wordTrace_append hprefix tailTrace_731527
  have hstable : (prefixWord ++ tailWord_731527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731527).length < 2 ^ (prefixWord ++ tailWord_731527).sum := by decide
  have hdescent : baseEnd_731527 < baseStart_731527 := by decide
  rcases family_descends (prefixWord ++ tailWord_731527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731544 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_731544 : Nat := 118140960795 + 731544 * 2 ^ 59
def prefixEnd_731544 : Nat := 4983230072969 + 3 ^ 40 * 731544 * 2
def baseEnd_731544 : Nat := 250422461275194042957131

theorem tailTrace_731544 : CollatzResearch.WordTrace tailWord_731544 prefixEnd_731544 250422461275194042957131 := by
  unfold tailWord_731544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13340800830874250306752843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17787734441165667075670457 13340800830874250306752843)
  ·
    refine ⟨20011201246311375460129265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13340800830874250306752843 20011201246311375460129265)
    ·
      refine ⟨15008400934733531595096949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20011201246311375460129265 15008400934733531595096949)
      ·
        refine ⟨1407037587631268587040339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15008400934733531595096949 1407037587631268587040339)
        ·
          refine ⟨2110556381446902880560509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407037587631268587040339 2110556381446902880560509)
          ·
            refine ⟨791458643042588580210191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2110556381446902880560509 791458643042588580210191)
            ·
              refine ⟨1187187964563882870315287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791458643042588580210191 1187187964563882870315287)
              ·
                refine ⟨1780781946845824305472931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187187964563882870315287 1780781946845824305472931)
                ·
                  refine ⟨2671172920268736458209397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780781946845824305472931 2671172920268736458209397)
                  ·
                    refine ⟨250422461275194042957131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2671172920268736458209397 250422461275194042957131)
                    ·
                      rfl

theorem cell22_731544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_731544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731544 prefixEnd_731544 := by exact prefixLift 731544
  have htrace : WordTrace (prefixWord ++ tailWord_731544) baseStart_731544 baseEnd_731544 := by
    simpa [prefixWord, tailWord_731544, baseEnd_731544] using wordTrace_append hprefix tailTrace_731544
  have hstable : (prefixWord ++ tailWord_731544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731544).length < 2 ^ (prefixWord ++ tailWord_731544).sum := by decide
  have hdescent : baseEnd_731544 < baseStart_731544 := by decide
  rcases family_descends (prefixWord ++ tailWord_731544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731713 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_731713 : Nat := 118140960795 + 731713 * 2 ^ 59
def prefixEnd_731713 : Nat := 4983230072969 + 3 ^ 40 * 731713 * 2
def baseEnd_731713 : Nat := 250480313428933935481613

theorem tailTrace_731713 : CollatzResearch.WordTrace tailWord_731713 prefixEnd_731713 250480313428933935481613 := by
  unfold tailWord_731713
  simp only [CollatzResearch.WordTrace]
  refine ⟨26687765598136242476407793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17791843732090828317605195 26687765598136242476407793)
  ·
    refine ⟨20015824198602181857305845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26687765598136242476407793 20015824198602181857305845)
    ·
      refine ⟨1876483518618954549122423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20015824198602181857305845 1876483518618954549122423)
      ·
        refine ⟨2814725277928431823683635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876483518618954549122423 2814725277928431823683635)
        ·
          refine ⟨4222087916892647735525453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814725277928431823683635 4222087916892647735525453)
          ·
            refine ⟨1583282968834742900822045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4222087916892647735525453 1583282968834742900822045)
            ·
              refine ⟨593731113313028587808267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1583282968834742900822045 593731113313028587808267)
              ·
                refine ⟨890596669969542881712401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593731113313028587808267 890596669969542881712401)
                ·
                  refine ⟨667947502477157161284301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890596669969542881712401 667947502477157161284301)
                  ·
                    refine ⟨250480313428933935481613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667947502477157161284301 250480313428933935481613)
                    ·
                      rfl

theorem cell22_731713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_731713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731713 prefixEnd_731713 := by exact prefixLift 731713
  have htrace : WordTrace (prefixWord ++ tailWord_731713) baseStart_731713 baseEnd_731713 := by
    simpa [prefixWord, tailWord_731713, baseEnd_731713] using wordTrace_append hprefix tailTrace_731713
  have hstable : (prefixWord ++ tailWord_731713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731713).length < 2 ^ (prefixWord ++ tailWord_731713).sum := by decide
  have hdescent : baseEnd_731713 < baseStart_731713 := by decide
  rcases family_descends (prefixWord ++ tailWord_731713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731724 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_731724 : Nat := 118140960795 + 731724 * 2 ^ 59
def prefixEnd_731724 : Nat := 4983230072969 + 3 ^ 40 * 731724 * 2
def baseEnd_731724 : Nat := 250484078953733573456579

theorem tailTrace_731724 : CollatzResearch.WordTrace tailWord_731724 prefixEnd_731724 250484078953733573456579 := by
  unfold tailWord_731724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344083400548195677529113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17792111200730927570038817 13344083400548195677529113)
  ·
    refine ⟨10008062550411146758146835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13344083400548195677529113 10008062550411146758146835)
    ·
      refine ⟨15012093825616720137220253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10008062550411146758146835 15012093825616720137220253)
      ·
        refine ⟨5629535184606270051457595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15012093825616720137220253 5629535184606270051457595)
        ·
          refine ⟨8444302776909405077186393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629535184606270051457595 8444302776909405077186393)
          ·
            refine ⟨6333227082682053807889795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8444302776909405077186393 6333227082682053807889795)
            ·
              refine ⟨9499840624023080711834693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333227082682053807889795 9499840624023080711834693)
              ·
                refine ⟨1781220117004327633469005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9499840624023080711834693 1781220117004327633469005)
                ·
                  refine ⟨667957543876622862550877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1781220117004327633469005 667957543876622862550877)
                  ·
                    refine ⟨250484078953733573456579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667957543876622862550877 250484078953733573456579)
                    ·
                      rfl

theorem cell22_731724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_731724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731724 prefixEnd_731724 := by exact prefixLift 731724
  have htrace : WordTrace (prefixWord ++ tailWord_731724) baseStart_731724 baseEnd_731724 := by
    simpa [prefixWord, tailWord_731724, baseEnd_731724] using wordTrace_append hprefix tailTrace_731724
  have hstable : (prefixWord ++ tailWord_731724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731724).length < 2 ^ (prefixWord ++ tailWord_731724).sum := by decide
  have hdescent : baseEnd_731724 < baseStart_731724 := by decide
  rcases family_descends (prefixWord ++ tailWord_731724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731754 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_731754 : Nat := 118140960795 + 731754 * 2 ^ 59
def prefixEnd_731754 : Nat := 4983230072969 + 3 ^ 40 * 731754 * 2
def baseEnd_731754 : Nat := 83498116188941165068829

theorem tailTrace_731754 : CollatzResearch.WordTrace tailWord_731754 prefixEnd_731754 83498116188941165068829 := by
  unfold tailWord_731754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6672315247746926619662579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17792840660658470985766877 6672315247746926619662579)
  ·
    refine ⟨10008472871620389929493869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6672315247746926619662579 10008472871620389929493869)
    ·
      refine ⟨3753177326857646223560201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10008472871620389929493869 3753177326857646223560201)
      ·
        refine ⟨2814882995143234667670151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753177326857646223560201 2814882995143234667670151)
        ·
          refine ⟨4222324492714852001505227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814882995143234667670151 4222324492714852001505227)
          ·
            refine ⟨6333486739072278002257841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222324492714852001505227 6333486739072278002257841)
            ·
              refine ⟨4750115054304208501693381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6333486739072278002257841 4750115054304208501693381)
              ·
                refine ⟨890646572682039094067509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4750115054304208501693381 890646572682039094067509)
                ·
                  refine ⟨83498116188941165068829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890646572682039094067509 83498116188941165068829)
                  ·
                    rfl

theorem cell22_731754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_731754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731754 prefixEnd_731754 := by exact prefixLift 731754
  have htrace : WordTrace (prefixWord ++ tailWord_731754) baseStart_731754 baseEnd_731754 := by
    simpa [prefixWord, tailWord_731754, baseEnd_731754] using wordTrace_append hprefix tailTrace_731754
  have hstable : (prefixWord ++ tailWord_731754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731754).length < 2 ^ (prefixWord ++ tailWord_731754).sum := by decide
  have hdescent : baseEnd_731754 < baseStart_731754 := by decide
  rcases family_descends (prefixWord ++ tailWord_731754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731758 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_731758 : Nat := 118140960795 + 731758 * 2 ^ 59
def prefixEnd_731758 : Nat := 4983230072969 + 3 ^ 40 * 731758 * 2
def baseEnd_731758 : Nat := 250495717848568818106475

theorem tailTrace_731758 : CollatzResearch.WordTrace tailWord_731758 prefixEnd_731758 250495717848568818106475 := by
  unfold tailWord_731758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336175860371651895224491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17792937921982143441197285 3336175860371651895224491)
  ·
    refine ⟨5004263790557477842836737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3336175860371651895224491 5004263790557477842836737)
    ·
      refine ⟨3753197842918108382127553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5004263790557477842836737 3753197842918108382127553)
      ·
        refine ⟨2814898382188581286595665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753197842918108382127553 2814898382188581286595665)
        ·
          refine ⟨2111173786641435964946749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2814898382188581286595665 2111173786641435964946749)
          ·
            refine ⟨791690169990538486855031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2111173786641435964946749 791690169990538486855031)
            ·
              refine ⟨1187535254985807730282547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791690169990538486855031 1187535254985807730282547)
              ·
                refine ⟨1781302882478711595423821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187535254985807730282547 1781302882478711595423821)
                ·
                  refine ⟨667988580929516848283933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1781302882478711595423821 667988580929516848283933)
                  ·
                    refine ⟨250495717848568818106475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 667988580929516848283933 250495717848568818106475)
                    ·
                      rfl

theorem cell22_731758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_731758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731758 prefixEnd_731758 := by exact prefixLift 731758
  have htrace : WordTrace (prefixWord ++ tailWord_731758) baseStart_731758 baseEnd_731758 := by
    simpa [prefixWord, tailWord_731758, baseEnd_731758] using wordTrace_append hprefix tailTrace_731758
  have hstable : (prefixWord ++ tailWord_731758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731758).length < 2 ^ (prefixWord ++ tailWord_731758).sum := by decide
  have hdescent : baseEnd_731758 < baseStart_731758 := by decide
  rcases family_descends (prefixWord ++ tailWord_731758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731801 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_731801 : Nat := 118140960795 + 731801 * 2 ^ 59
def prefixEnd_731801 : Nat := 4983230072969 + 3 ^ 40 * 731801 * 2
def baseEnd_731801 : Nat := 250510437627331039281343

theorem tailTrace_731801 : CollatzResearch.WordTrace tailWord_731801 prefixEnd_731801 250510437627331039281343 := by
  unfold tailWord_731801
  simp only [CollatzResearch.WordTrace]
  refine ⟨26690975221817433505611257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17793983481211622337074171 26690975221817433505611257)
  ·
    refine ⟨20018231416363075129208443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26690975221817433505611257 20018231416363075129208443)
    ·
      refine ⟨30027347124544612693812665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20018231416363075129208443 30027347124544612693812665)
      ·
        refine ⟨22520510343408459520359499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30027347124544612693812665 22520510343408459520359499)
        ·
          refine ⟨33780765515112689280539249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22520510343408459520359499 33780765515112689280539249)
          ·
            refine ⟨25335574136334516960404437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33780765515112689280539249 25335574136334516960404437)
            ·
              refine ⟨593802518820340241259479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25335574136334516960404437 593802518820340241259479)
              ·
                refine ⟨890703778230510361889219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593802518820340241259479 890703778230510361889219)
                ·
                  refine ⟨1336055667345765542833829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890703778230510361889219 1336055667345765542833829)
                  ·
                    refine ⟨250510437627331039281343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336055667345765542833829 250510437627331039281343)
                    ·
                      rfl

theorem cell22_731801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_731801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731801 prefixEnd_731801 := by exact prefixLift 731801
  have htrace : WordTrace (prefixWord ++ tailWord_731801) baseStart_731801 baseEnd_731801 := by
    simpa [prefixWord, tailWord_731801, baseEnd_731801] using wordTrace_append hprefix tailTrace_731801
  have hstable : (prefixWord ++ tailWord_731801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731801).length < 2 ^ (prefixWord ++ tailWord_731801).sum := by decide
  have hdescent : baseEnd_731801 < baseStart_731801 := by decide
  rcases family_descends (prefixWord ++ tailWord_731801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731831 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 1, 5]
def baseStart_731831 : Nat := 118140960795 + 731831 * 2 ^ 59
def prefixEnd_731831 : Nat := 4983230072969 + 3 ^ 40 * 731831 * 2
def baseEnd_731831 : Nat := 250520707240420961031251

theorem tailTrace_731831 : CollatzResearch.WordTrace tailWord_731831 prefixEnd_731831 250520707240420961031251 := by
  unfold tailWord_731831
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692069411708748629203347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17794712941139165752802231 26692069411708748629203347)
  ·
    refine ⟨40038104117563122943805021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26692069411708748629203347 40038104117563122943805021)
    ·
      refine ⟨15014289044086171103926883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40038104117563122943805021 15014289044086171103926883)
      ·
        refine ⟨22521433566129256655890325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15014289044086171103926883 22521433566129256655890325)
        ·
          refine ⟨1055692198412308905744859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22521433566129256655890325 1055692198412308905744859)
          ·
            refine ⟨1583538297618463358617289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055692198412308905744859 1583538297618463358617289)
            ·
              refine ⟨1187653723213847518962967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583538297618463358617289 1187653723213847518962967)
              ·
                refine ⟨1781480584820771278444451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187653723213847518962967 1781480584820771278444451)
                ·
                  refine ⟨2672220877231156917666677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781480584820771278444451 2672220877231156917666677)
                  ·
                    refine ⟨250520707240420961031251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2672220877231156917666677 250520707240420961031251)
                    ·
                      rfl

theorem cell22_731831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_731831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731831 prefixEnd_731831 := by exact prefixLift 731831
  have htrace : WordTrace (prefixWord ++ tailWord_731831) baseStart_731831 baseEnd_731831 := by
    simpa [prefixWord, tailWord_731831, baseEnd_731831] using wordTrace_append hprefix tailTrace_731831
  have hstable : (prefixWord ++ tailWord_731831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731831).length < 2 ^ (prefixWord ++ tailWord_731831).sum := by decide
  have hdescent : baseEnd_731831 < baseStart_731831 := by decide
  rcases family_descends (prefixWord ++ tailWord_731831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731861 : List Nat := [1, 3, 2, 5, 1, 1, 9]
def baseStart_731861 : Nat := 118140960795 + 731861 * 2 ^ 59
def prefixEnd_731861 : Nat := 4983230072969 + 3 ^ 40 * 731861 * 2
def baseEnd_731861 : Nat := 9278925068648551214117

theorem tailTrace_731861 : CollatzResearch.WordTrace tailWord_731861 prefixEnd_731861 9278925068648551214117 := by
  unfold tailWord_731861
  simp only [CollatzResearch.WordTrace]
  refine ⟨26693163601600063752795437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17795442401066709168530291 26693163601600063752795437)
  ·
    refine ⟨10009936350600023907298289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26693163601600063752795437 10009936350600023907298289)
    ·
      refine ⟨7507452262950017930473717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10009936350600023907298289 7507452262950017930473717)
      ·
        refine ⟨703823649651564180981911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7507452262950017930473717 703823649651564180981911)
        ·
          refine ⟨1055735474477346271472867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703823649651564180981911 1055735474477346271472867)
          ·
            refine ⟨1583603211716019407209301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055735474477346271472867 1583603211716019407209301)
            ·
              refine ⟨9278925068648551214117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1583603211716019407209301 9278925068648551214117)
              ·
                rfl

theorem cell22_731861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 9].length) (baseStart_731861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731861 prefixEnd_731861 := by exact prefixLift 731861
  have htrace : WordTrace (prefixWord ++ tailWord_731861) baseStart_731861 baseEnd_731861 := by
    simpa [prefixWord, tailWord_731861, baseEnd_731861] using wordTrace_append hprefix tailTrace_731861
  have hstable : (prefixWord ++ tailWord_731861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731861).length < 2 ^ (prefixWord ++ tailWord_731861).sum := by decide
  have hdescent : baseEnd_731861 < baseStart_731861 := by decide
  rcases family_descends (prefixWord ++ tailWord_731861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731876 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_731876 : Nat := 118140960795 + 731876 * 2 ^ 59
def prefixEnd_731876 : Nat := 4983230072969 + 3 ^ 40 * 731876 * 2
def baseEnd_731876 : Nat := 250536111660055843656113

theorem tailTrace_731876 : CollatzResearch.WordTrace tailWord_731876 prefixEnd_731876 250536111660055843656113 := by
  unfold tailWord_731876
  simp only [CollatzResearch.WordTrace]
  refine ⟨13346855348272860657295741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17795807131030480876394321 13346855348272860657295741)
  ·
    refine ⟨5005070755602322746485903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13346855348272860657295741 5005070755602322746485903)
    ·
      refine ⟨7507606133403484119728855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5005070755602322746485903 7507606133403484119728855)
      ·
        refine ⟨11261409200105226179593283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7507606133403484119728855 11261409200105226179593283)
        ·
          refine ⟨16892113800157839269389925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11261409200105226179593283 16892113800157839269389925)
          ·
            refine ⟨3167271337529594863010611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16892113800157839269389925 3167271337529594863010611)
            ·
              refine ⟨4750907006294392294515917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167271337529594863010611 4750907006294392294515917)
              ·
                refine ⟨1781590127360397110443469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4750907006294392294515917 1781590127360397110443469)
                ·
                  refine ⟨668096297760148916416301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1781590127360397110443469 668096297760148916416301)
                  ·
                    refine ⟨250536111660055843656113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668096297760148916416301 250536111660055843656113)
                    ·
                      rfl

theorem cell22_731876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_731876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731876 prefixEnd_731876 := by exact prefixLift 731876
  have htrace : WordTrace (prefixWord ++ tailWord_731876) baseStart_731876 baseEnd_731876 := by
    simpa [prefixWord, tailWord_731876, baseEnd_731876] using wordTrace_append hprefix tailTrace_731876
  have hstable : (prefixWord ++ tailWord_731876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731876).length < 2 ^ (prefixWord ++ tailWord_731876).sum := by decide
  have hdescent : baseEnd_731876 < baseStart_731876 := by decide
  rcases family_descends (prefixWord ++ tailWord_731876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731906 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_731906 : Nat := 118140960795 + 731906 * 2 ^ 59
def prefixEnd_731906 : Nat := 4983230072969 + 3 ^ 40 * 731906 * 2
def baseEnd_731906 : Nat := 83515460424381921802007

theorem tailTrace_731906 : CollatzResearch.WordTrace tailWord_731906 prefixEnd_731906 83515460424381921802007 := by
  unfold tailWord_731906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6673701221609259109545893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17796536590958024292122381 6673701221609259109545893)
  ·
    refine ⟨1251318979051736083039855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6673701221609259109545893 1251318979051736083039855)
    ·
      refine ⟨1876978468577604124559783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251318979051736083039855 1876978468577604124559783)
      ·
        refine ⟨2815467702866406186839675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876978468577604124559783 2815467702866406186839675)
        ·
          refine ⟨4223201554299609280259513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815467702866406186839675 4223201554299609280259513)
          ·
            refine ⟨3167401165724706960194635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4223201554299609280259513 3167401165724706960194635)
            ·
              refine ⟨4751101748587060440291953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167401165724706960194635 4751101748587060440291953)
              ·
                refine ⟨3563326311440295330218965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751101748587060440291953 3563326311440295330218965)
                ·
                  refine ⟨83515460424381921802007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3563326311440295330218965 83515460424381921802007)
                  ·
                    rfl

theorem cell22_731906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_731906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731906 prefixEnd_731906 := by exact prefixLift 731906
  have htrace : WordTrace (prefixWord ++ tailWord_731906) baseStart_731906 baseEnd_731906 := by
    simpa [prefixWord, tailWord_731906, baseEnd_731906] using wordTrace_append hprefix tailTrace_731906
  have hstable : (prefixWord ++ tailWord_731906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731906).length < 2 ^ (prefixWord ++ tailWord_731906).sum := by decide
  have hdescent : baseEnd_731906 < baseStart_731906 := by decide
  rcases family_descends (prefixWord ++ tailWord_731906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731927 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 1, 3]
def baseStart_731927 : Nat := 118140960795 + 731927 * 2 ^ 59
def prefixEnd_731927 : Nat := 4983230072969 + 3 ^ 40 * 731927 * 2
def baseEnd_731927 : Nat := 250553570002308710630957

theorem tailTrace_731927 : CollatzResearch.WordTrace tailWord_731927 prefixEnd_731927 250553570002308710630957 := by
  unfold tailWord_731927
  simp only [CollatzResearch.WordTrace]
  refine ⟨26695570819360957024698035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17797047212907304683132023 26695570819360957024698035)
  ·
    refine ⟨40043356229041435537047053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26695570819360957024698035 40043356229041435537047053)
    ·
      refine ⟨15016258585890538326392645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40043356229041435537047053 15016258585890538326392645)
      ·
        refine ⟨2815548484854475936198621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15016258585890538326392645 2815548484854475936198621)
        ·
          refine ⟨1055830681820428476074483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2815548484854475936198621 1055830681820428476074483)
          ·
            refine ⟨1583746022730642714111725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055830681820428476074483 1583746022730642714111725)
            ·
              refine ⟨593904758523991017791897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1583746022730642714111725 593904758523991017791897)
              ·
                refine ⟨445428568892993263343923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593904758523991017791897 445428568892993263343923)
                ·
                  refine ⟨668142853339489895015885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445428568892993263343923 668142853339489895015885)
                  ·
                    refine ⟨250553570002308710630957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668142853339489895015885 250553570002308710630957)
                    ·
                      rfl

theorem cell22_731927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_731927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731927 prefixEnd_731927 := by exact prefixLift 731927
  have htrace : WordTrace (prefixWord ++ tailWord_731927) baseStart_731927 baseEnd_731927 := by
    simpa [prefixWord, tailWord_731927, baseEnd_731927] using wordTrace_append hprefix tailTrace_731927
  have hstable : (prefixWord ++ tailWord_731927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731927).length < 2 ^ (prefixWord ++ tailWord_731927).sum := by decide
  have hdescent : baseEnd_731927 < baseStart_731927 := by decide
  rcases family_descends (prefixWord ++ tailWord_731927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731940 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_731940 : Nat := 118140960795 + 731940 * 2 ^ 59
def prefixEnd_731940 : Nat := 4983230072969 + 3 ^ 40 * 731940 * 2
def baseEnd_731940 : Nat := 83519340055993670018639

theorem tailTrace_731940 : CollatzResearch.WordTrace tailWord_731940 prefixEnd_731940 83519340055993670018639 := by
  unfold tailWord_731940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348022484156930122460637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17797363312209240163280849 13348022484156930122460637)
  ·
    refine ⟨5005508431558848795922739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13348022484156930122460637 5005508431558848795922739)
    ·
      refine ⟨7508262647338273193884109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5005508431558848795922739 7508262647338273193884109)
      ·
        refine ⟨2815598492751852447706541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7508262647338273193884109 2815598492751852447706541)
        ·
          refine ⟨1055849434781944667889953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2815598492751852447706541 1055849434781944667889953)
          ·
            refine ⟨791887076086458500917465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055849434781944667889953 791887076086458500917465)
            ·
              refine ⟨593915307064843875688099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791887076086458500917465 593915307064843875688099)
              ·
                refine ⟨890872960597265813532149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593915307064843875688099 890872960597265813532149)
                ·
                  refine ⟨83519340055993670018639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890872960597265813532149 83519340055993670018639)
                  ·
                    rfl

theorem cell22_731940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_731940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_731940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_731940 prefixEnd_731940 := by exact prefixLift 731940
  have htrace : WordTrace (prefixWord ++ tailWord_731940) baseStart_731940 baseEnd_731940 := by
    simpa [prefixWord, tailWord_731940, baseEnd_731940] using wordTrace_append hprefix tailTrace_731940
  have hstable : (prefixWord ++ tailWord_731940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731940).length < 2 ^ (prefixWord ++ tailWord_731940).sum := by decide
  have hdescent : baseEnd_731940 < baseStart_731940 := by decide
  rcases family_descends (prefixWord ++ tailWord_731940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732011 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 5, 3]
def baseStart_732011 : Nat := 118140960795 + 732011 * 2 ^ 59
def prefixEnd_732011 : Nat := 4983230072969 + 3 ^ 40 * 732011 * 2
def baseEnd_732011 : Nat := 250582324918960491530699

theorem tailTrace_732011 : CollatzResearch.WordTrace tailWord_732011 prefixEnd_732011 250582324918960491530699 := by
  unfold tailWord_732011
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698634551056639370755887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17799089700704426247170591 26698634551056639370755887)
  ·
    refine ⟨40047951826584959056133831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26698634551056639370755887 40047951826584959056133831)
    ·
      refine ⟨60071927739877438584200747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40047951826584959056133831 60071927739877438584200747)
      ·
        refine ⟨90107891609816157876301121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60071927739877438584200747 90107891609816157876301121)
        ·
          refine ⟨67580918707362118407225841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90107891609816157876301121 67580918707362118407225841)
          ·
            refine ⟨50685689030521588805419381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67580918707362118407225841 50685689030521588805419381)
            ·
              refine ⟨4751783346611398950508067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50685689030521588805419381 4751783346611398950508067)
              ·
                refine ⟨7127675019917098425762101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751783346611398950508067 7127675019917098425762101)
                ·
                  refine ⟨668219533117227977415197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7127675019917098425762101 668219533117227977415197)
                  ·
                    refine ⟨250582324918960491530699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668219533117227977415197 250582324918960491530699)
                    ·
                      rfl

theorem cell22_732011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3].length) (baseStart_732011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732011 prefixEnd_732011 := by exact prefixLift 732011
  have htrace : WordTrace (prefixWord ++ tailWord_732011) baseStart_732011 baseEnd_732011 := by
    simpa [prefixWord, tailWord_732011, baseEnd_732011] using wordTrace_append hprefix tailTrace_732011
  have hstable : (prefixWord ++ tailWord_732011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732011).length < 2 ^ (prefixWord ++ tailWord_732011).sum := by decide
  have hdescent : baseEnd_732011 < baseStart_732011 := by decide
  rcases family_descends (prefixWord ++ tailWord_732011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732041 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 7]
def baseStart_732041 : Nat := 118140960795 + 732041 * 2 ^ 59
def prefixEnd_732041 : Nat := 4983230072969 + 3 ^ 40 * 732041 * 2
def baseEnd_732041 : Nat := 83530864844016804426869

theorem tailTrace_732041 : CollatzResearch.WordTrace tailWord_732041 prefixEnd_732041 83530864844016804426869 := by
  unfold tailWord_732041
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699728740947954494347977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17799819160631969662898651 26699728740947954494347977)
  ·
    refine ⟨20024796555710965870760983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26699728740947954494347977 20024796555710965870760983)
    ·
      refine ⟨30037194833566448806141475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024796555710965870760983 30037194833566448806141475)
      ·
        refine ⟨45055792250349673209212213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30037194833566448806141475 45055792250349673209212213)
        ·
          refine ⟨4223980523470281863363645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45055792250349673209212213 4223980523470281863363645)
          ·
            refine ⟨1583992696301355698761367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4223980523470281863363645 1583992696301355698761367)
            ·
              refine ⟨2375989044452033548142051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583992696301355698761367 2375989044452033548142051)
              ·
                refine ⟨3563983566678050322213077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375989044452033548142051 3563983566678050322213077)
                ·
                  refine ⟨83530864844016804426869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3563983566678050322213077 83530864844016804426869)
                  ·
                    rfl

theorem cell22_732041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_732041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732041 prefixEnd_732041 := by exact prefixLift 732041
  have htrace : WordTrace (prefixWord ++ tailWord_732041) baseStart_732041 baseEnd_732041 := by
    simpa [prefixWord, tailWord_732041, baseEnd_732041] using wordTrace_append hprefix tailTrace_732041
  have hstable : (prefixWord ++ tailWord_732041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732041).length < 2 ^ (prefixWord ++ tailWord_732041).sum := by decide
  have hdescent : baseEnd_732041 < baseStart_732041 := by decide
  rcases family_descends (prefixWord ++ tailWord_732041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732088 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_732088 : Nat := 118140960795 + 732088 * 2 ^ 59
def prefixEnd_732088 : Nat := 4983230072969 + 3 ^ 40 * 732088 * 2
def baseEnd_732088 : Nat := 250608683592557957355463

theorem tailTrace_732088 : CollatzResearch.WordTrace tailWord_732088 prefixEnd_732088 250608683592557957355463 := by
  unfold tailWord_732088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13350721485888840760654459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17800961981185121014205945 13350721485888840760654459)
  ·
    refine ⟨20026082228833261140981689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13350721485888840760654459 20026082228833261140981689)
    ·
      refine ⟨15019561671624945855736267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20026082228833261140981689 15019561671624945855736267)
      ·
        refine ⟨22529342507437418783604401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15019561671624945855736267 22529342507437418783604401)
        ·
          refine ⟨16897006880578064087703301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22529342507437418783604401 16897006880578064087703301)
          ·
            refine ⟨3168188790108387016444369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16897006880578064087703301 3168188790108387016444369)
            ·
              refine ⟨2376141592581290262333277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168188790108387016444369 2376141592581290262333277)
              ·
                refine ⟨891053097217983848374979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2376141592581290262333277 891053097217983848374979)
                ·
                  refine ⟨1336579645826975772562469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891053097217983848374979 1336579645826975772562469)
                  ·
                    refine ⟨250608683592557957355463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336579645826975772562469 250608683592557957355463)
                    ·
                      rfl

theorem cell22_732088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_732088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732088 prefixEnd_732088 := by exact prefixLift 732088
  have htrace : WordTrace (prefixWord ++ tailWord_732088) baseStart_732088 baseEnd_732088 := by
    simpa [prefixWord, tailWord_732088, baseEnd_732088] using wordTrace_append hprefix tailTrace_732088
  have hstable : (prefixWord ++ tailWord_732088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732088).length < 2 ^ (prefixWord ++ tailWord_732088).sum := by decide
  have hdescent : baseEnd_732088 < baseStart_732088 := by decide
  rcases family_descends (prefixWord ++ tailWord_732088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732103 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 4]
def baseStart_732103 : Nat := 118140960795 + 732103 * 2 ^ 59
def prefixEnd_732103 : Nat := 4983230072969 + 3 ^ 40 * 732103 * 2
def baseEnd_732103 : Nat := 83537939466367639410139

theorem tailTrace_732103 : CollatzResearch.WordTrace tailWord_732103 prefixEnd_732103 83537939466367639410139 := by
  unfold tailWord_732103
  simp only [CollatzResearch.WordTrace]
  refine ⟨26701990066723339083104963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17801326711148892722069975 26701990066723339083104963)
  ·
    refine ⟨40052985100085008624657445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26701990066723339083104963 40052985100085008624657445)
    ·
      refine ⟨7509934706265939117123271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40052985100085008624657445 7509934706265939117123271)
      ·
        refine ⟨11264902059398908675684907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7509934706265939117123271 11264902059398908675684907)
        ·
          refine ⟨16897353089098363013527361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11264902059398908675684907 16897353089098363013527361)
          ·
            refine ⟨12673014816823772260145521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16897353089098363013527361 12673014816823772260145521)
            ·
              refine ⟨9504761112617829195109141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12673014816823772260145521 9504761112617829195109141)
              ·
                refine ⟨445535677153960743520741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9504761112617829195109141 445535677153960743520741)
                ·
                  refine ⟨83537939466367639410139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445535677153960743520741 83537939466367639410139)
                  ·
                    rfl

theorem cell22_732103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 4].length) (baseStart_732103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732103 prefixEnd_732103 := by exact prefixLift 732103
  have htrace : WordTrace (prefixWord ++ tailWord_732103) baseStart_732103 baseEnd_732103 := by
    simpa [prefixWord, tailWord_732103, baseEnd_732103] using wordTrace_append hprefix tailTrace_732103
  have hstable : (prefixWord ++ tailWord_732103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732103).length < 2 ^ (prefixWord ++ tailWord_732103).sum := by decide
  have hdescent : baseEnd_732103 < baseStart_732103 := by decide
  rcases family_descends (prefixWord ++ tailWord_732103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732109 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 5]
def baseStart_732109 : Nat := 118140960795 + 732109 * 2 ^ 59
def prefixEnd_732109 : Nat := 4983230072969 + 3 ^ 40 * 732109 * 2
def baseEnd_732109 : Nat := 83538624107240300860133

theorem tailTrace_732109 : CollatzResearch.WordTrace tailWord_732109 prefixEnd_732109 83538624107240300860133 := by
  unfold tailWord_732109
  simp only [CollatzResearch.WordTrace]
  refine ⟨26702208904701602107823381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17801472603134401405215587 26702208904701602107823381)
  ·
    refine ⟨1251666042407887598804221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26702208904701602107823381 1251666042407887598804221)
    ·
      refine ⟨469374765902957849551583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1251666042407887598804221 469374765902957849551583)
      ·
        refine ⟨704062148854436774327375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469374765902957849551583 704062148854436774327375)
        ·
          refine ⟨1056093223281655161491063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704062148854436774327375 1056093223281655161491063)
          ·
            refine ⟨1584139834922482742236595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056093223281655161491063 1584139834922482742236595)
            ·
              refine ⟨2376209752383724113354893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584139834922482742236595 2376209752383724113354893)
              ·
                refine ⟨891078657143896542508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2376209752383724113354893 891078657143896542508085)
                ·
                  refine ⟨83538624107240300860133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 891078657143896542508085 83538624107240300860133)
                  ·
                    rfl

theorem cell22_732109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_732109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732109 prefixEnd_732109 := by exact prefixLift 732109
  have htrace : WordTrace (prefixWord ++ tailWord_732109) baseStart_732109 baseEnd_732109 := by
    simpa [prefixWord, tailWord_732109, baseEnd_732109] using wordTrace_append hprefix tailTrace_732109
  have hstable : (prefixWord ++ tailWord_732109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732109).length < 2 ^ (prefixWord ++ tailWord_732109).sum := by decide
  have hdescent : baseEnd_732109 < baseStart_732109 := by decide
  rcases family_descends (prefixWord ++ tailWord_732109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732131 : List Nat := [1, 1, 1, 6, 1, 1, 1, 10]
def baseStart_732131 : Nat := 118140960795 + 732131 * 2 ^ 59
def prefixEnd_732131 : Nat := 4983230072969 + 3 ^ 40 * 732131 * 2
def baseEnd_732131 : Nat := 27847044819035575392259

theorem tailTrace_732131 : CollatzResearch.WordTrace tailWord_732131 prefixEnd_732131 27847044819035575392259 := by
  unfold tailWord_732131
  simp only [CollatzResearch.WordTrace]
  refine ⟨26703011310621899865124247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17802007540414599910082831 26703011310621899865124247)
  ·
    refine ⟨40054516965932849797686371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26703011310621899865124247 40054516965932849797686371)
    ·
      refine ⟨60081775448899274696529557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40054516965932849797686371 60081775448899274696529557)
      ·
        refine ⟨2816333224167153501399823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60081775448899274696529557 2816333224167153501399823)
        ·
          refine ⟨4224499836250730252099735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816333224167153501399823 4224499836250730252099735)
          ·
            refine ⟨6336749754376095378149603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224499836250730252099735 6336749754376095378149603)
            ·
              refine ⟨9505124631564143067224405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336749754376095378149603 9505124631564143067224405)
              ·
                refine ⟨27847044819035575392259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9505124631564143067224405 27847044819035575392259)
                ·
                  rfl

theorem cell22_732131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 10].length) (baseStart_732131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732131 prefixEnd_732131 := by exact prefixLift 732131
  have htrace : WordTrace (prefixWord ++ tailWord_732131) baseStart_732131 baseEnd_732131 := by
    simpa [prefixWord, tailWord_732131, baseEnd_732131] using wordTrace_append hprefix tailTrace_732131
  have hstable : (prefixWord ++ tailWord_732131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732131).length < 2 ^ (prefixWord ++ tailWord_732131).sum := by decide
  have hdescent : baseEnd_732131 < baseStart_732131 := by decide
  rcases family_descends (prefixWord ++ tailWord_732131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732150 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_732150 : Nat := 118140960795 + 732150 * 2 ^ 59
def prefixEnd_732150 : Nat := 4983230072969 + 3 ^ 40 * 732150 * 2
def baseEnd_732150 : Nat := 250629907459610462305273

theorem tailTrace_732150 : CollatzResearch.WordTrace tailWord_732150 prefixEnd_732150 250629907459610462305273 := by
  unfold tailWord_732150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668981518597066631879119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17802469531702044073377269 1668981518597066631879119)
  ·
    refine ⟨2503472277895599947818679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668981518597066631879119 2503472277895599947818679)
    ·
      refine ⟨3755208416843399921728019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503472277895599947818679 3755208416843399921728019)
      ·
        refine ⟨5632812625265099882592029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3755208416843399921728019 5632812625265099882592029)
        ·
          refine ⟨2112304734474412455972011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5632812625265099882592029 2112304734474412455972011)
          ·
            refine ⟨3168457101711618683958017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112304734474412455972011 3168457101711618683958017)
            ·
              refine ⟨2376342826283714012968513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168457101711618683958017 2376342826283714012968513)
              ·
                refine ⟨1782257119712785509726385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376342826283714012968513 1782257119712785509726385)
                ·
                  refine ⟨1336692839784589132294789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1782257119712785509726385 1336692839784589132294789)
                  ·
                    refine ⟨250629907459610462305273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336692839784589132294789 250629907459610462305273)
                    ·
                      rfl

theorem cell22_732150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_732150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732150 prefixEnd_732150 := by exact prefixLift 732150
  have htrace : WordTrace (prefixWord ++ tailWord_732150) baseStart_732150 baseEnd_732150 := by
    simpa [prefixWord, tailWord_732150, baseEnd_732150] using wordTrace_append hprefix tailTrace_732150
  have hstable : (prefixWord ++ tailWord_732150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732150).length < 2 ^ (prefixWord ++ tailWord_732150).sum := by decide
  have hdescent : baseEnd_732150 < baseStart_732150 := by decide
  rcases family_descends (prefixWord ++ tailWord_732150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732197 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_732197 : Nat := 118140960795 + 732197 * 2 ^ 59
def prefixEnd_732197 : Nat := 4983230072969 + 3 ^ 40 * 732197 * 2
def baseEnd_732197 : Nat := 250645996520118006380129

theorem tailTrace_732197 : CollatzResearch.WordTrace tailWord_732197 prefixEnd_732197 250645996520118006380129 := by
  unfold tailWord_732197
  simp only [CollatzResearch.WordTrace]
  refine ⟨26705418528382793137026845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17803612352255195424684563 26705418528382793137026845)
  ·
    refine ⟨10014531948143547426385067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26705418528382793137026845 10014531948143547426385067)
    ·
      refine ⟨15021797922215321139577601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10014531948143547426385067 15021797922215321139577601)
      ·
        refine ⟨11266348441661490854683201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15021797922215321139577601 11266348441661490854683201)
        ·
          refine ⟨8449761331246118141012401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11266348441661490854683201 8449761331246118141012401)
          ·
            refine ⟨6337320998434588605759301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8449761331246118141012401 6337320998434588605759301)
            ·
              refine ⟨1188247687206485363579869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6337320998434588605759301 1188247687206485363579869)
              ·
                refine ⟨445592882702432011342451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1188247687206485363579869 445592882702432011342451)
                ·
                  refine ⟨668389324053648017013677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445592882702432011342451 668389324053648017013677)
                  ·
                    refine ⟨250645996520118006380129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668389324053648017013677 250645996520118006380129)
                    ·
                      rfl

theorem cell22_732197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_732197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732197 prefixEnd_732197 := by exact prefixLift 732197
  have htrace : WordTrace (prefixWord ++ tailWord_732197) baseStart_732197 baseEnd_732197 := by
    simpa [prefixWord, tailWord_732197, baseEnd_732197] using wordTrace_append hprefix tailTrace_732197
  have hstable : (prefixWord ++ tailWord_732197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732197).length < 2 ^ (prefixWord ++ tailWord_732197).sum := by decide
  have hdescent : baseEnd_732197 < baseStart_732197 := by decide
  rcases family_descends (prefixWord ++ tailWord_732197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732214 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_732214 : Nat := 118140960795 + 732214 * 2 ^ 59
def prefixEnd_732214 : Nat := 4983230072969 + 3 ^ 40 * 732214 * 2
def baseEnd_732214 : Nat := 250651815967535628705077

theorem tailTrace_732214 : CollatzResearch.WordTrace tailWord_732214 prefixEnd_732214 250651815967535628705077 := by
  unfold tailWord_732214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669127410582575315024731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17804025712880803360263797 1669127410582575315024731)
  ·
    refine ⟨2503691115873862972537097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1669127410582575315024731 2503691115873862972537097)
    ·
      refine ⟨1877768336905397229402823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2503691115873862972537097 1877768336905397229402823)
      ·
        refine ⟨2816652505358095844104235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877768336905397229402823 2816652505358095844104235)
        ·
          refine ⟨4224978758037143766156353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816652505358095844104235 4224978758037143766156353)
          ·
            refine ⟨3168734068527857824617265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224978758037143766156353 3168734068527857824617265)
            ·
              refine ⟨2376550551395893368462949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168734068527857824617265 2376550551395893368462949)
              ·
                refine ⟨445603228386730006586803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2376550551395893368462949 445603228386730006586803)
                ·
                  refine ⟨668404842580095009880205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445603228386730006586803 668404842580095009880205)
                  ·
                    refine ⟨250651815967535628705077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668404842580095009880205 250651815967535628705077)
                    ·
                      rfl

theorem cell22_732214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_732214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732214 prefixEnd_732214 := by exact prefixLift 732214
  have htrace : WordTrace (prefixWord ++ tailWord_732214) baseStart_732214 baseEnd_732214 := by
    simpa [prefixWord, tailWord_732214, baseEnd_732214] using wordTrace_append hprefix tailTrace_732214
  have hstable : (prefixWord ++ tailWord_732214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732214).length < 2 ^ (prefixWord ++ tailWord_732214).sum := by decide
  have hdescent : baseEnd_732214 < baseStart_732214 := by decide
  rcases family_descends (prefixWord ++ tailWord_732214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732238 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_732238 : Nat := 118140960795 + 732238 * 2 ^ 59
def prefixEnd_732238 : Nat := 4983230072969 + 3 ^ 40 * 732238 * 2
def baseEnd_732238 : Nat := 83553343886002522035001

theorem tailTrace_732238 : CollatzResearch.WordTrace tailWord_732238 prefixEnd_732238 83553343886002522035001 := by
  unfold tailWord_732238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338364240154282142408671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17804609280822838092846245 3338364240154282142408671)
  ·
    refine ⟨5007546360231423213613007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338364240154282142408671 5007546360231423213613007)
    ·
      refine ⟨7511319540347134820419511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007546360231423213613007 7511319540347134820419511)
      ·
        refine ⟨11266979310520702230629267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7511319540347134820419511 11266979310520702230629267)
        ·
          refine ⟨16900468965781053345943901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11266979310520702230629267 16900468965781053345943901)
          ·
            refine ⟨6337675862167895004728963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16900468965781053345943901 6337675862167895004728963)
            ·
              refine ⟨9506513793251842507093445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337675862167895004728963 9506513793251842507093445)
              ·
                refine ⟨1782471336234720470080021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9506513793251842507093445 1782471336234720470080021)
                ·
                  refine ⟨83553343886002522035001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1782471336234720470080021 83553343886002522035001)
                  ·
                    rfl

theorem cell22_732238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_732238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732238 prefixEnd_732238 := by exact prefixLift 732238
  have htrace : WordTrace (prefixWord ++ tailWord_732238) baseStart_732238 baseEnd_732238 := by
    simpa [prefixWord, tailWord_732238, baseEnd_732238] using wordTrace_append hprefix tailTrace_732238
  have hstable : (prefixWord ++ tailWord_732238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732238).length < 2 ^ (prefixWord ++ tailWord_732238).sum := by decide
  have hdescent : baseEnd_732238 < baseStart_732238 := by decide
  rcases family_descends (prefixWord ++ tailWord_732238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732272 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_732272 : Nat := 118140960795 + 732272 * 2 ^ 59
def prefixEnd_732272 : Nat := 4983230072969 + 3 ^ 40 * 732272 * 2
def baseEnd_732272 : Nat := 83557223517614270251633

theorem tailTrace_732272 : CollatzResearch.WordTrace tailWord_732272 prefixEnd_732272 83557223517614270251633 := by
  unfold tailWord_732272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13354077001555540473003535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17805436002074053964004713 13354077001555540473003535)
  ·
    refine ⟨20031115502333310709505303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13354077001555540473003535 20031115502333310709505303)
    ·
      refine ⟨30046673253499966064257955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20031115502333310709505303 30046673253499966064257955)
      ·
        refine ⟨45070009880249949096386933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30046673253499966064257955 45070009880249949096386933)
        ·
          refine ⟨4225313426273432727786275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45070009880249949096386933 4225313426273432727786275)
          ·
            refine ⟨6337970139410149091679413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225313426273432727786275 6337970139410149091679413)
            ·
              refine ⟨594184700569701477344945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6337970139410149091679413 594184700569701477344945)
              ·
                refine ⟨445638525427276108008709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594184700569701477344945 445638525427276108008709)
                ·
                  refine ⟨83557223517614270251633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445638525427276108008709 83557223517614270251633)
                  ·
                    rfl

theorem cell22_732272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_732272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732272 prefixEnd_732272 := by exact prefixLift 732272
  have htrace : WordTrace (prefixWord ++ tailWord_732272) baseStart_732272 baseEnd_732272 := by
    simpa [prefixWord, tailWord_732272, baseEnd_732272] using wordTrace_append hprefix tailTrace_732272
  have hstable : (prefixWord ++ tailWord_732272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732272).length < 2 ^ (prefixWord ++ tailWord_732272).sum := by decide
  have hdescent : baseEnd_732272 < baseStart_732272 := by decide
  rcases family_descends (prefixWord ++ tailWord_732272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732302 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_732302 : Nat := 118140960795 + 732302 * 2 ^ 59
def prefixEnd_732302 : Nat := 4983230072969 + 3 ^ 40 * 732302 * 2
def baseEnd_732302 : Nat := 250681940165932732504807

theorem tailTrace_732302 : CollatzResearch.WordTrace tailWord_732302 prefixEnd_732302 250681940165932732504807 := by
  unfold tailWord_732302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338656024125299508699895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17806165462001597379732773 3338656024125299508699895)
  ·
    refine ⟨5007984036187949263049843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338656024125299508699895 5007984036187949263049843)
    ·
      refine ⟨7511976054281923894574765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007984036187949263049843 7511976054281923894574765)
      ·
        refine ⟨2816991020355721460465537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7511976054281923894574765 2816991020355721460465537)
        ·
          refine ⟨2112743265266791095349153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816991020355721460465537 2112743265266791095349153)
          ·
            refine ⟨1584557448950093321511865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112743265266791095349153 1584557448950093321511865)
            ·
              refine ⟨1188418086712569991133899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584557448950093321511865 1188418086712569991133899)
              ·
                refine ⟨1782627130068854986700849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188418086712569991133899 1782627130068854986700849)
                ·
                  refine ⟨1336970347551641240025637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1782627130068854986700849 1336970347551641240025637)
                  ·
                    refine ⟨250681940165932732504807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336970347551641240025637 250681940165932732504807)
                    ·
                      rfl

theorem cell22_732302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_732302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732302 prefixEnd_732302 := by exact prefixLift 732302
  have htrace : WordTrace (prefixWord ++ tailWord_732302) baseStart_732302 baseEnd_732302 := by
    simpa [prefixWord, tailWord_732302, baseEnd_732302] using wordTrace_append hprefix tailTrace_732302
  have hstable : (prefixWord ++ tailWord_732302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732302).length < 2 ^ (prefixWord ++ tailWord_732302).sum := by decide
  have hdescent : baseEnd_732302 < baseStart_732302 := by decide
  rcases family_descends (prefixWord ++ tailWord_732302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732345 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 5]
def baseStart_732345 : Nat := 118140960795 + 732345 * 2 ^ 59
def prefixEnd_732345 : Nat := 4983230072969 + 3 ^ 40 * 732345 * 2
def baseEnd_732345 : Nat := 83565553314898317893225

theorem tailTrace_732345 : CollatzResearch.WordTrace tailWord_732345 prefixEnd_732345 83565553314898317893225 := by
  unfold tailWord_732345
  simp only [CollatzResearch.WordTrace]
  refine ⟨26710816531846614413414489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17807211021231076275609659 26710816531846614413414489)
  ·
    refine ⟨20033112398884960810060867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26710816531846614413414489 20033112398884960810060867)
    ·
      refine ⟨30049668598327441215091301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20033112398884960810060867 30049668598327441215091301)
      ·
        refine ⟨5634312862186395227829619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30049668598327441215091301 5634312862186395227829619)
        ·
          refine ⟨8451469293279592841744429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634312862186395227829619 8451469293279592841744429)
          ·
            refine ⟨3169300984979847315654161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8451469293279592841744429 3169300984979847315654161)
            ·
              refine ⟨2376975738734885486740621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169300984979847315654161 2376975738734885486740621)
              ·
                refine ⟨891365902025582057527733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2376975738734885486740621 891365902025582057527733)
                ·
                  refine ⟨83565553314898317893225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 891365902025582057527733 83565553314898317893225)
                  ·
                    rfl

theorem cell22_732345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_732345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732345 prefixEnd_732345 := by exact prefixLift 732345
  have htrace : WordTrace (prefixWord ++ tailWord_732345) baseStart_732345 baseEnd_732345 := by
    simpa [prefixWord, tailWord_732345, baseEnd_732345] using wordTrace_append hprefix tailTrace_732345
  have hstable : (prefixWord ++ tailWord_732345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732345).length < 2 ^ (prefixWord ++ tailWord_732345).sum := by decide
  have hdescent : baseEnd_732345 < baseStart_732345 := by decide
  rcases family_descends (prefixWord ++ tailWord_732345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732366 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_732366 : Nat := 118140960795 + 732366 * 2 ^ 59
def prefixEnd_732366 : Nat := 4983230072969 + 3 ^ 40 * 732366 * 2
def baseEnd_732366 : Nat := 250703848673857898904611

theorem tailTrace_732366 : CollatzResearch.WordTrace tailWord_732366 prefixEnd_732366 250703848673857898904611 := by
  unfold tailWord_732366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338947808096316874991119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17807721643180356666619301 3338947808096316874991119)
  ·
    refine ⟨5008421712144475312486679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338947808096316874991119 5008421712144475312486679)
    ·
      refine ⟨7512632568216712968730019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008421712144475312486679 7512632568216712968730019)
      ·
        refine ⟨11268948852325069453095029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7512632568216712968730019 11268948852325069453095029)
        ·
          refine ⟨1056463954905475261227659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11268948852325069453095029 1056463954905475261227659)
          ·
            refine ⟨1584695932358212891841489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056463954905475261227659 1584695932358212891841489)
            ·
              refine ⟨1188521949268659668881117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584695932358212891841489 1188521949268659668881117)
              ·
                refine ⟨445695730975747375830419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1188521949268659668881117 445695730975747375830419)
                ·
                  refine ⟨668543596463621063745629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445695730975747375830419 668543596463621063745629)
                  ·
                    refine ⟨250703848673857898904611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668543596463621063745629 250703848673857898904611)
                    ·
                      rfl

theorem cell22_732366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_732366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732366 prefixEnd_732366 := by exact prefixLift 732366
  have htrace : WordTrace (prefixWord ++ tailWord_732366) baseStart_732366 baseEnd_732366 := by
    simpa [prefixWord, tailWord_732366, baseEnd_732366] using wordTrace_append hprefix tailTrace_732366
  have hstable : (prefixWord ++ tailWord_732366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732366).length < 2 ^ (prefixWord ++ tailWord_732366).sum := by decide
  have hdescent : baseEnd_732366 < baseStart_732366 := by decide
  rcases family_descends (prefixWord ++ tailWord_732366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732456 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_732456 : Nat := 118140960795 + 732456 * 2 ^ 59
def prefixEnd_732456 : Nat := 4983230072969 + 3 ^ 40 * 732456 * 2
def baseEnd_732456 : Nat := 250734657513127664154335

theorem tailTrace_732456 : CollatzResearch.WordTrace tailWord_732456 prefixEnd_732456 250734657513127664154335 := by
  unfold tailWord_732456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357432517222240185352611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17809910022962986913803481 13357432517222240185352611)
  ·
    refine ⟨20036148775833360278028917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13357432517222240185352611 20036148775833360278028917)
    ·
      refine ⟨1878388947734377526065211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20036148775833360278028917 1878388947734377526065211)
      ·
        refine ⟨2817583421601566289097817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878388947734377526065211 2817583421601566289097817)
        ·
          refine ⟨2113187566201174716823363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2817583421601566289097817 2113187566201174716823363)
          ·
            refine ⟨3169781349301762075235045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113187566201174716823363 3169781349301762075235045)
            ·
              refine ⟨594334002994080389106571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3169781349301762075235045 594334002994080389106571)
              ·
                refine ⟨891501004491120583659857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594334002994080389106571 891501004491120583659857)
                ·
                  refine ⟨668625753368340437744893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 891501004491120583659857 668625753368340437744893)
                  ·
                    refine ⟨250734657513127664154335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668625753368340437744893 250734657513127664154335)
                    ·
                      rfl

theorem cell22_732456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_732456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732456 prefixEnd_732456 := by exact prefixLift 732456
  have htrace : WordTrace (prefixWord ++ tailWord_732456) baseStart_732456 baseEnd_732456 := by
    simpa [prefixWord, tailWord_732456, baseEnd_732456] using wordTrace_append hprefix tailTrace_732456
  have hstable : (prefixWord ++ tailWord_732456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732456).length < 2 ^ (prefixWord ++ tailWord_732456).sum := by decide
  have hdescent : baseEnd_732456 < baseStart_732456 := by decide
  rcases family_descends (prefixWord ++ tailWord_732456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732486 : List Nat := [6, 1, 1, 3, 2, 9]
def baseStart_732486 : Nat := 118140960795 + 732486 * 2 ^ 59
def prefixEnd_732486 : Nat := 4983230072969 + 3 ^ 40 * 732486 * 2
def baseEnd_732486 : Nat := 3095616384274291184003

theorem tailTrace_732486 : CollatzResearch.WordTrace tailWord_732486 prefixEnd_732486 3095616384274291184003 := by
  unfold tailWord_732486
  simp only [CollatzResearch.WordTrace]
  refine ⟨834873725760493609196791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17810639482890530329531541 834873725760493609196791)
  ·
    refine ⟨1252310588640740413795187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834873725760493609196791 1252310588640740413795187)
    ·
      refine ⟨1878465882961110620692781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252310588640740413795187 1878465882961110620692781)
      ·
        refine ⟨704424706110416482759793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1878465882961110620692781 704424706110416482759793)
        ·
          refine ⟨528318529582812362069845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704424706110416482759793 528318529582812362069845)
          ·
            refine ⟨3095616384274291184003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 528318529582812362069845 3095616384274291184003)
            ·
              rfl

theorem cell22_732486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 9].length) (baseStart_732486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732486 prefixEnd_732486 := by exact prefixLift 732486
  have htrace : WordTrace (prefixWord ++ tailWord_732486) baseStart_732486 baseEnd_732486 := by
    simpa [prefixWord, tailWord_732486, baseEnd_732486] using wordTrace_append hprefix tailTrace_732486
  have hstable : (prefixWord ++ tailWord_732486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732486).length < 2 ^ (prefixWord ++ tailWord_732486).sum := by decide
  have hdescent : baseEnd_732486 < baseStart_732486 := by decide
  rcases family_descends (prefixWord ++ tailWord_732486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732497 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 5]
def baseStart_732497 : Nat := 118140960795 + 732497 * 2 ^ 59
def prefixEnd_732497 : Nat := 4983230072969 + 3 ^ 40 * 732497 * 2
def baseEnd_732497 : Nat := 83582897550339074626403

theorem tailTrace_732497 : CollatzResearch.WordTrace tailWord_732497 prefixEnd_732497 83582897550339074626403 := by
  unfold tailWord_732497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26716360427295944372947745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17810906951530629581965163 26716360427295944372947745)
  ·
    refine ⟨20037270320471958279710809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26716360427295944372947745 20037270320471958279710809)
    ·
      refine ⟨15027952740353968709783107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20037270320471958279710809 15027952740353968709783107)
      ·
        refine ⟨22541929110530953064674661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15027952740353968709783107 22541929110530953064674661)
        ·
          refine ⟨4226611708224553699626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22541929110530953064674661 4226611708224553699626499)
          ·
            refine ⟨6339917562336830549439749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226611708224553699626499 6339917562336830549439749)
            ·
              refine ⟨1188734542938155728019953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6339917562336830549439749 1188734542938155728019953)
              ·
                refine ⟨891550907203616796014965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188734542938155728019953 891550907203616796014965)
                ·
                  refine ⟨83582897550339074626403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 891550907203616796014965 83582897550339074626403)
                  ·
                    rfl

theorem cell22_732497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_732497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732497 prefixEnd_732497 := by exact prefixLift 732497
  have htrace : WordTrace (prefixWord ++ tailWord_732497) baseStart_732497 baseEnd_732497 := by
    simpa [prefixWord, tailWord_732497, baseEnd_732497] using wordTrace_append hprefix tailTrace_732497
  have hstable : (prefixWord ++ tailWord_732497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732497).length < 2 ^ (prefixWord ++ tailWord_732497).sum := by decide
  have hdescent : baseEnd_732497 < baseStart_732497 := by decide
  rcases family_descends (prefixWord ++ tailWord_732497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732501 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_732501 : Nat := 118140960795 + 732501 * 2 ^ 59
def prefixEnd_732501 : Nat := 4983230072969 + 3 ^ 40 * 732501 * 2
def baseEnd_732501 : Nat := 250750061932762546779197

theorem tailTrace_732501 : CollatzResearch.WordTrace tailWord_732501 prefixEnd_732501 250750061932762546779197 := by
  unfold tailWord_732501
  simp only [CollatzResearch.WordTrace]
  refine ⟨26716506319281453056093357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17811004212854302037395571 26716506319281453056093357)
  ·
    refine ⟨10018689869730544896035009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26716506319281453056093357 10018689869730544896035009)
    ·
      refine ⟨7514017402297908672026257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10018689869730544896035009 7514017402297908672026257)
      ·
        refine ⟨5635513051723431504019693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7514017402297908672026257 5635513051723431504019693)
        ·
          refine ⟨2113317394396286814007385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5635513051723431504019693 2113317394396286814007385)
          ·
            refine ⟨1584988045797215110505539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113317394396286814007385 1584988045797215110505539)
            ·
              refine ⟨2377482068695822665758309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584988045797215110505539 2377482068695822665758309)
              ·
                refine ⟨445777887880466749829683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2377482068695822665758309 445777887880466749829683)
                ·
                  refine ⟨668666831820700124744525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445777887880466749829683 668666831820700124744525)
                  ·
                    refine ⟨250750061932762546779197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668666831820700124744525 250750061932762546779197)
                    ·
                      rfl

theorem cell22_732501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_732501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732501 prefixEnd_732501 := by exact prefixLift 732501
  have htrace : WordTrace (prefixWord ++ tailWord_732501) baseStart_732501 baseEnd_732501 := by
    simpa [prefixWord, tailWord_732501, baseEnd_732501] using wordTrace_append hprefix tailTrace_732501
  have hstable : (prefixWord ++ tailWord_732501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732501).length < 2 ^ (prefixWord ++ tailWord_732501).sum := by decide
  have hdescent : baseEnd_732501 < baseStart_732501 := by decide
  rcases family_descends (prefixWord ++ tailWord_732501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732512 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_732512 : Nat := 118140960795 + 732512 * 2 ^ 59
def prefixEnd_732512 : Nat := 4983230072969 + 3 ^ 40 * 732512 * 2
def baseEnd_732512 : Nat := 250753827457562184754163

theorem tailTrace_732512 : CollatzResearch.WordTrace tailWord_732512 prefixEnd_732512 250753827457562184754163 := by
  unfold tailWord_732512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358453761120800967371895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17811271681494401289829193 13358453761120800967371895)
  ·
    refine ⟨20037680641681201451057843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13358453761120800967371895 20037680641681201451057843)
    ·
      refine ⟨30056520962521802176586765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20037680641681201451057843 30056520962521802176586765)
      ·
        refine ⟨11271195360945675816220037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30056520962521802176586765 11271195360945675816220037)
        ·
          refine ⟨2113349130177314215541257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11271195360945675816220037 2113349130177314215541257)
          ·
            refine ⟨1585011847632985661655943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113349130177314215541257 1585011847632985661655943)
            ·
              refine ⟨2377517771449478492483915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585011847632985661655943 2377517771449478492483915)
              ·
                refine ⟨3566276657174217738725873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377517771449478492483915 3566276657174217738725873)
                ·
                  refine ⟨2674707492880663304044405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3566276657174217738725873 2674707492880663304044405)
                  ·
                    refine ⟨250753827457562184754163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2674707492880663304044405 250753827457562184754163)
                    ·
                      rfl

theorem cell22_732512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_732512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732512 prefixEnd_732512 := by exact prefixLift 732512
  have htrace : WordTrace (prefixWord ++ tailWord_732512) baseStart_732512 baseEnd_732512 := by
    simpa [prefixWord, tailWord_732512, baseEnd_732512] using wordTrace_append hprefix tailTrace_732512
  have hstable : (prefixWord ++ tailWord_732512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732512).length < 2 ^ (prefixWord ++ tailWord_732512).sum := by decide
  have hdescent : baseEnd_732512 < baseStart_732512 := by decide
  rcases family_descends (prefixWord ++ tailWord_732512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732527 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 1, 4]
def baseStart_732527 : Nat := 118140960795 + 732527 * 2 ^ 59
def prefixEnd_732527 : Nat := 4983230072969 + 3 ^ 40 * 732527 * 2
def baseEnd_732527 : Nat := 250758962264107145629117

theorem tailTrace_732527 : CollatzResearch.WordTrace tailWord_732527 prefixEnd_732527 250758962264107145629117 := by
  unfold tailWord_732527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26717454617187259496539835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17811636411458172997693223 26717454617187259496539835)
  ·
    refine ⟨40076181925780889244809753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26717454617187259496539835 40076181925780889244809753)
    ·
      refine ⟨30057136444335666933607315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40076181925780889244809753 30057136444335666933607315)
      ·
        refine ⟨45085704666503500400410973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30057136444335666933607315 45085704666503500400410973)
        ·
          refine ⟨16907139249938812650154115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45085704666503500400410973 16907139249938812650154115)
          ·
            refine ⟨25360708874908218975231173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16907139249938812650154115 25360708874908218975231173)
            ·
              refine ⟨4755132914045291057855845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25360708874908218975231173 4755132914045291057855845)
              ·
                refine ⟨891587421383492073347971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4755132914045291057855845 891587421383492073347971)
                ·
                  refine ⟨1337381132075238110021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891587421383492073347971 1337381132075238110021957)
                  ·
                    refine ⟨250758962264107145629117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1337381132075238110021957 250758962264107145629117)
                    ·
                      rfl

theorem cell22_732527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_732527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732527 prefixEnd_732527 := by exact prefixLift 732527
  have htrace : WordTrace (prefixWord ++ tailWord_732527) baseStart_732527 baseEnd_732527 := by
    simpa [prefixWord, tailWord_732527, baseEnd_732527] using wordTrace_append hprefix tailTrace_732527
  have hstable : (prefixWord ++ tailWord_732527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732527).length < 2 ^ (prefixWord ++ tailWord_732527).sum := by decide
  have hdescent : baseEnd_732527 < baseStart_732527 := by decide
  rcases family_descends (prefixWord ++ tailWord_732527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732589 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_732589 : Nat := 118140960795 + 732589 * 2 ^ 59
def prefixEnd_732589 : Nat := 4983230072969 + 3 ^ 40 * 732589 * 2
def baseEnd_732589 : Nat := 250780186131159650578927

theorem tailTrace_732589 : CollatzResearch.WordTrace tailWord_732589 prefixEnd_732589 250780186131159650578927 := by
  unfold tailWord_732589
  simp only [CollatzResearch.WordTrace]
  refine ⟨26719715942962644085296821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17813143961975096056864547 26719715942962644085296821)
  ·
    refine ⟨2504973369652747882996577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26719715942962644085296821 2504973369652747882996577)
    ·
      refine ⟨1878730027239560912247433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2504973369652747882996577 1878730027239560912247433)
      ·
        refine ⟨1409047520429670684185575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878730027239560912247433 1409047520429670684185575)
        ·
          refine ⟨2113571280644506026278363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409047520429670684185575 2113571280644506026278363)
          ·
            refine ⟨3170356920966759039417545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113571280644506026278363 3170356920966759039417545)
            ·
              refine ⟨2377767690725069279563159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170356920966759039417545 2377767690725069279563159)
              ·
                refine ⟨3566651536087603919344739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377767690725069279563159 3566651536087603919344739)
                ·
                  refine ⟨5349977304131405879017109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566651536087603919344739 5349977304131405879017109)
                  ·
                    refine ⟨250780186131159650578927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5349977304131405879017109 250780186131159650578927)
                    ·
                      rfl

theorem cell22_732589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_732589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732589 prefixEnd_732589 := by exact prefixLift 732589
  have htrace : WordTrace (prefixWord ++ tailWord_732589) baseStart_732589 baseEnd_732589 := by
    simpa [prefixWord, tailWord_732589, baseEnd_732589] using wordTrace_append hprefix tailTrace_732589
  have hstable : (prefixWord ++ tailWord_732589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732589).length < 2 ^ (prefixWord ++ tailWord_732589).sum := by decide
  have hdescent : baseEnd_732589 < baseStart_732589 := by decide
  rcases family_descends (prefixWord ++ tailWord_732589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732604 : List Nat := [2, 2, 2, 4, 2, 2, 8]
def baseStart_732604 : Nat := 118140960795 + 732604 * 2 ^ 59
def prefixEnd_732604 : Nat := 4983230072969 + 3 ^ 40 * 732604 * 2
def baseEnd_732604 : Nat := 9288345219914985609403

theorem tailTrace_732604 : CollatzResearch.WordTrace tailWord_732604 prefixEnd_732604 9288345219914985609403 := by
  unfold tailWord_732604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360131518954150823546433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17813508691938867764728577 13360131518954150823546433)
  ·
    refine ⟨10020098639215613117659825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13360131518954150823546433 10020098639215613117659825)
    ·
      refine ⟨7515073979411709838244869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10020098639215613117659825 7515073979411709838244869)
      ·
        refine ⟨1409076371139695594670913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7515073979411709838244869 1409076371139695594670913)
        ·
          refine ⟨1056807278354771696003185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409076371139695594670913 1056807278354771696003185)
          ·
            refine ⟨792605458766078772002389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056807278354771696003185 792605458766078772002389)
            ·
              refine ⟨9288345219914985609403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 792605458766078772002389 9288345219914985609403)
              ·
                rfl

theorem cell22_732604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 8].length) (baseStart_732604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732604 prefixEnd_732604 := by exact prefixLift 732604
  have htrace : WordTrace (prefixWord ++ tailWord_732604) baseStart_732604 baseEnd_732604 := by
    simpa [prefixWord, tailWord_732604, baseEnd_732604] using wordTrace_append hprefix tailTrace_732604
  have hstable : (prefixWord ++ tailWord_732604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732604).length < 2 ^ (prefixWord ++ tailWord_732604).sum := by decide
  have hdescent : baseEnd_732604 < baseStart_732604 := by decide
  rcases family_descends (prefixWord ++ tailWord_732604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732619 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 3, 3]
def baseStart_732619 : Nat := 118140960795 + 732619 * 2 ^ 59
def prefixEnd_732619 : Nat := 4983230072969 + 3 ^ 40 * 732619 * 2
def baseEnd_732619 : Nat := 250790455744249572328835

theorem tailTrace_732619 : CollatzResearch.WordTrace tailWord_732619 prefixEnd_732619 250790455744249572328835 := by
  unfold tailWord_732619
  simp only [CollatzResearch.WordTrace]
  refine ⟨26720810132853959208888911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17813873421902639472592607 26720810132853959208888911)
  ·
    refine ⟨40081215199280938813333367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26720810132853959208888911 40081215199280938813333367)
    ·
      refine ⟨60121822798921408220000051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40081215199280938813333367 60121822798921408220000051)
      ·
        refine ⟨90182734198382112330000077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60121822798921408220000051 90182734198382112330000077)
        ·
          refine ⟨33818525324393292123750029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90182734198382112330000077 33818525324393292123750029)
          ·
            refine ⟨12681946996647484546406261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33818525324393292123750029 12681946996647484546406261)
            ·
              refine ⟨1188932530935701676225587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12681946996647484546406261 1188932530935701676225587)
              ·
                refine ⟨1783398796403552514338381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188932530935701676225587 1783398796403552514338381)
                ·
                  refine ⟨668774548651332192876893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1783398796403552514338381 668774548651332192876893)
                  ·
                    refine ⟨250790455744249572328835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668774548651332192876893 250790455744249572328835)
                    ·
                      rfl

theorem cell22_732619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3].length) (baseStart_732619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732619 prefixEnd_732619 := by exact prefixLift 732619
  have htrace : WordTrace (prefixWord ++ tailWord_732619) baseStart_732619 baseEnd_732619 := by
    simpa [prefixWord, tailWord_732619, baseEnd_732619] using wordTrace_append hprefix tailTrace_732619
  have hstable : (prefixWord ++ tailWord_732619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732619).length < 2 ^ (prefixWord ++ tailWord_732619).sum := by decide
  have hdescent : baseEnd_732619 < baseStart_732619 := by decide
  rcases family_descends (prefixWord ++ tailWord_732619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732677 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 6]
def baseStart_732677 : Nat := 118140960795 + 732677 * 2 ^ 59
def prefixEnd_732677 : Nat := 4983230072969 + 3 ^ 40 * 732677 * 2
def baseEnd_732677 : Nat := 83603436776518918126219

theorem tailTrace_732677 : CollatzResearch.WordTrace tailWord_732677 prefixEnd_732677 83603436776518918126219 := by
  unfold tailWord_732677
  simp only [CollatzResearch.WordTrace]
  refine ⟨26722925566643835114500285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17815283711095890076333523 26722925566643835114500285)
  ·
    refine ⟨10021097087491438167937607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26722925566643835114500285 10021097087491438167937607)
    ·
      refine ⟨15031645631237157251906411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10021097087491438167937607 15031645631237157251906411)
      ·
        refine ⟨22547468446855735877859617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15031645631237157251906411 22547468446855735877859617)
        ·
          refine ⟨16910601335141801908394713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22547468446855735877859617 16910601335141801908394713)
          ·
            refine ⟨12682951001356351431296035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16910601335141801908394713 12682951001356351431296035)
            ·
              refine ⟨19024426502034527146944053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12682951001356351431296035 19024426502034527146944053)
              ·
                refine ⟨1783539984565736920026005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19024426502034527146944053 1783539984565736920026005)
                ·
                  refine ⟨83603436776518918126219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1783539984565736920026005 83603436776518918126219)
                  ·
                    rfl

theorem cell22_732677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_732677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732677 prefixEnd_732677 := by exact prefixLift 732677
  have htrace : WordTrace (prefixWord ++ tailWord_732677) baseStart_732677 baseEnd_732677 := by
    simpa [prefixWord, tailWord_732677, baseEnd_732677] using wordTrace_append hprefix tailTrace_732677
  have hstable : (prefixWord ++ tailWord_732677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732677).length < 2 ^ (prefixWord ++ tailWord_732677).sum := by decide
  have hdescent : baseEnd_732677 < baseStart_732677 := by decide
  rcases family_descends (prefixWord ++ tailWord_732677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732679 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_732679 : Nat := 118140960795 + 732679 * 2 ^ 59
def prefixEnd_732679 : Nat := 4983230072969 + 3 ^ 40 * 732679 * 2
def baseEnd_732679 : Nat := 250810994970429415828651

theorem tailTrace_732679 : CollatzResearch.WordTrace tailWord_732679 prefixEnd_732679 250810994970429415828651 := by
  unfold tailWord_732679
  simp only [CollatzResearch.WordTrace]
  refine ⟨26722998512636589456073091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17815332341757726304048727 26722998512636589456073091)
  ·
    refine ⟨40084497768954884184109637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26722998512636589456073091 40084497768954884184109637)
    ·
      refine ⟨7515843331679040784520557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40084497768954884184109637 7515843331679040784520557)
      ·
        refine ⟨2818441249379640294195209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7515843331679040784520557 2818441249379640294195209)
        ·
          refine ⟨2113830937034730220646407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2818441249379640294195209 2113830937034730220646407)
          ·
            refine ⟨3170746405552095330969611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113830937034730220646407 3170746405552095330969611)
            ·
              refine ⟨4756119608328142996454417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170746405552095330969611 4756119608328142996454417)
              ·
                refine ⟨3567089706246107247340813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756119608328142996454417 3567089706246107247340813)
                ·
                  refine ⟨1337658639842290217752805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3567089706246107247340813 1337658639842290217752805)
                  ·
                    refine ⟨250810994970429415828651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1337658639842290217752805 250810994970429415828651)
                    ·
                      rfl

theorem cell22_732679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_732679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732679 prefixEnd_732679 := by exact prefixLift 732679
  have htrace : WordTrace (prefixWord ++ tailWord_732679) baseStart_732679 baseEnd_732679 := by
    simpa [prefixWord, tailWord_732679, baseEnd_732679] using wordTrace_append hprefix tailTrace_732679
  have hstable : (prefixWord ++ tailWord_732679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732679).length < 2 ^ (prefixWord ++ tailWord_732679).sum := by decide
  have hdescent : baseEnd_732679 < baseStart_732679 := by decide
  rcases family_descends (prefixWord ++ tailWord_732679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732709 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_732709 : Nat := 118140960795 + 732709 * 2 ^ 59
def prefixEnd_732709 : Nat := 4983230072969 + 3 ^ 40 * 732709 * 2
def baseEnd_732709 : Nat := 250821264583519337578559

theorem tailTrace_732709 : CollatzResearch.WordTrace tailWord_732709 prefixEnd_732709 250821264583519337578559 := by
  unfold tailWord_732709
  simp only [CollatzResearch.WordTrace]
  refine ⟨26724092702527904579665181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17816061801685269719776787 26724092702527904579665181)
  ·
    refine ⟨10021534763447964217374443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26724092702527904579665181 10021534763447964217374443)
    ·
      refine ⟨15032302145171946326061665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10021534763447964217374443 15032302145171946326061665)
      ·
        refine ⟨11274226608878959744546249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15032302145171946326061665 11274226608878959744546249)
        ·
          refine ⟨8455669956659219808409687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11274226608878959744546249 8455669956659219808409687)
          ·
            refine ⟨12683504934988829712614531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455669956659219808409687 12683504934988829712614531)
            ·
              refine ⟨19025257402483244568921797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12683504934988829712614531 19025257402483244568921797)
              ·
                refine ⟨3567235762965608356672837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19025257402483244568921797 3567235762965608356672837)
                ·
                  refine ⟨668856705556051566876157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3567235762965608356672837 668856705556051566876157)
                  ·
                    refine ⟨250821264583519337578559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668856705556051566876157 250821264583519337578559)
                    ·
                      rfl

theorem cell22_732709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_732709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732709 prefixEnd_732709 := by exact prefixLift 732709
  have htrace : WordTrace (prefixWord ++ tailWord_732709) baseStart_732709 baseEnd_732709 := by
    simpa [prefixWord, tailWord_732709, baseEnd_732709] using wordTrace_append hprefix tailTrace_732709
  have hstable : (prefixWord ++ tailWord_732709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732709).length < 2 ^ (prefixWord ++ tailWord_732709).sum := by decide
  have hdescent : baseEnd_732709 < baseStart_732709 := by decide
  rcases family_descends (prefixWord ++ tailWord_732709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732743 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 1, 5]
def baseStart_732743 : Nat := 118140960795 + 732743 * 2 ^ 59
def prefixEnd_732743 : Nat := 4983230072969 + 3 ^ 40 * 732743 * 2
def baseEnd_732743 : Nat := 250832903478354582228455

theorem tailTrace_732743 : CollatzResearch.WordTrace tailWord_732743 prefixEnd_732743 250832903478354582228455 := by
  unfold tailWord_732743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26725332784404728386402883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17816888522936485590935255 26725332784404728386402883)
  ·
    refine ⟨40087999176607092579604325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26725332784404728386402883 40087999176607092579604325)
    ·
      refine ⟨7516499845613829858675811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40087999176607092579604325 7516499845613829858675811)
      ·
        refine ⟨11274749768420744788013717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7516499845613829858675811 11274749768420744788013717)
        ·
          refine ⟨528503895394722411938143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11274749768420744788013717 528503895394722411938143)
          ·
            refine ⟨792755843092083617907215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528503895394722411938143 792755843092083617907215)
            ·
              refine ⟨1189133764638125426860823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792755843092083617907215 1189133764638125426860823)
              ·
                refine ⟨1783700646957188140291235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189133764638125426860823 1783700646957188140291235)
                ·
                  refine ⟨2675550970435782210436853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783700646957188140291235 2675550970435782210436853)
                  ·
                    refine ⟨250832903478354582228455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2675550970435782210436853 250832903478354582228455)
                    ·
                      rfl

theorem cell22_732743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_732743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732743 prefixEnd_732743 := by exact prefixLift 732743
  have htrace : WordTrace (prefixWord ++ tailWord_732743) baseStart_732743 baseEnd_732743 := by
    simpa [prefixWord, tailWord_732743, baseEnd_732743] using wordTrace_append hprefix tailTrace_732743
  have hstable : (prefixWord ++ tailWord_732743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732743).length < 2 ^ (prefixWord ++ tailWord_732743).sum := by decide
  have hdescent : baseEnd_732743 < baseStart_732743 := by decide
  rcases family_descends (prefixWord ++ tailWord_732743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732784 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_732784 : Nat := 118140960795 + 732784 * 2 ^ 59
def prefixEnd_732784 : Nat := 4983230072969 + 3 ^ 40 * 732784 * 2
def baseEnd_732784 : Nat := 83615646205414713984443

theorem tailTrace_732784 : CollatzResearch.WordTrace tailWord_732784 prefixEnd_732784 83615646205414713984443 := by
  unfold tailWord_732784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13363414088628096194322703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17817885451504128259096937 13363414088628096194322703)
  ·
    refine ⟨20045121132942144291484055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13363414088628096194322703 20045121132942144291484055)
    ·
      refine ⟨30067681699413216437226083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20045121132942144291484055 30067681699413216437226083)
      ·
        refine ⟨45101522549119824655839125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30067681699413216437226083 45101522549119824655839125)
        ·
          refine ⟨2114133869489991780742459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45101522549119824655839125 2114133869489991780742459)
          ·
            refine ⟨3171200804234987671113689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114133869489991780742459 3171200804234987671113689)
            ·
              refine ⟨2378400603176240753335267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171200804234987671113689 2378400603176240753335267)
              ·
                refine ⟨3567600904764361130002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378400603176240753335267 3567600904764361130002901)
                ·
                  refine ⟨83615646205414713984443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3567600904764361130002901 83615646205414713984443)
                  ·
                    rfl

theorem cell22_732784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_732784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732784 prefixEnd_732784 := by exact prefixLift 732784
  have htrace : WordTrace (prefixWord ++ tailWord_732784) baseStart_732784 baseEnd_732784 := by
    simpa [prefixWord, tailWord_732784, baseEnd_732784] using wordTrace_append hprefix tailTrace_732784
  have hstable : (prefixWord ++ tailWord_732784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732784).length < 2 ^ (prefixWord ++ tailWord_732784).sum := by decide
  have hdescent : baseEnd_732784 < baseStart_732784 := by decide
  rcases family_descends (prefixWord ++ tailWord_732784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732801 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 5]
def baseStart_732801 : Nat := 118140960795 + 732801 * 2 ^ 59
def prefixEnd_732801 : Nat := 4983230072969 + 3 ^ 40 * 732801 * 2
def baseEnd_732801 : Nat := 83617586021220588092759

theorem tailTrace_732801 : CollatzResearch.WordTrace tailWord_732801 prefixEnd_732801 83617586021220588092759 := by
  unfold tailWord_732801
  simp only [CollatzResearch.WordTrace]
  refine ⟨26727448218194604292014257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17818298812129736194676171 26727448218194604292014257)
  ·
    refine ⟨20045586163645953219010693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26727448218194604292014257 20045586163645953219010693)
    ·
      refine ⟨3758547405683616228564505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20045586163645953219010693 3758547405683616228564505)
      ·
        refine ⟨2818910554262712171423379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3758547405683616228564505 2818910554262712171423379)
        ·
          refine ⟨4228365831394068257135069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818910554262712171423379 4228365831394068257135069)
          ·
            refine ⟨1585637186772775596425651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4228365831394068257135069 1585637186772775596425651)
            ·
              refine ⟨2378455780159163394638477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585637186772775596425651 2378455780159163394638477)
              ·
                refine ⟨891920917559686272989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2378455780159163394638477 891920917559686272989429)
                ·
                  refine ⟨83617586021220588092759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 891920917559686272989429 83617586021220588092759)
                  ·
                    rfl

theorem cell22_732801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_732801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732801 prefixEnd_732801 := by exact prefixLift 732801
  have htrace : WordTrace (prefixWord ++ tailWord_732801) baseStart_732801 baseEnd_732801 := by
    simpa [prefixWord, tailWord_732801, baseEnd_732801] using wordTrace_append hprefix tailTrace_732801
  have hstable : (prefixWord ++ tailWord_732801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732801).length < 2 ^ (prefixWord ++ tailWord_732801).sum := by decide
  have hdescent : baseEnd_732801 < baseStart_732801 := by decide
  rcases family_descends (prefixWord ++ tailWord_732801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732859 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_732859 : Nat := 118140960795 + 732859 * 2 ^ 59
def prefixEnd_732859 : Nat := 4983230072969 + 3 ^ 40 * 732859 * 2
def baseEnd_732859 : Nat := 250872612648968946328099

theorem tailTrace_732859 : CollatzResearch.WordTrace tailWord_732859 prefixEnd_732859 250872612648968946328099 := by
  unfold tailWord_732859
  simp only [CollatzResearch.WordTrace]
  refine ⟨26729563651984480197625631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17819709101322986798417087 26729563651984480197625631)
  ·
    refine ⟨40094345477976720296438447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26729563651984480197625631 40094345477976720296438447)
    ·
      refine ⟨60141518216965080444657671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40094345477976720296438447 60141518216965080444657671)
      ·
        refine ⟨90212277325447620666986507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60141518216965080444657671 90212277325447620666986507)
        ·
          refine ⟨135318415988171431000479761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90212277325447620666986507 135318415988171431000479761)
          ·
            refine ⟨101488811991128573250359821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135318415988171431000479761 101488811991128573250359821)
            ·
              refine ⟨38058304496673214968884933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101488811991128573250359821 38058304496673214968884933)
              ·
                refine ⟨7135932093126227806665925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38058304496673214968884933 7135932093126227806665925)
                ·
                  refine ⟨1337987267461167713749861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7135932093126227806665925 1337987267461167713749861)
                  ·
                    refine ⟨250872612648968946328099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1337987267461167713749861 250872612648968946328099)
                    ·
                      rfl

theorem cell22_732859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_732859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732859 prefixEnd_732859 := by exact prefixLift 732859
  have htrace : WordTrace (prefixWord ++ tailWord_732859) baseStart_732859 baseEnd_732859 := by
    simpa [prefixWord, tailWord_732859, baseEnd_732859] using wordTrace_append hprefix tailTrace_732859
  have hstable : (prefixWord ++ tailWord_732859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732859).length < 2 ^ (prefixWord ++ tailWord_732859).sum := by decide
  have hdescent : baseEnd_732859 < baseStart_732859 := by decide
  rcases family_descends (prefixWord ++ tailWord_732859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732861 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_732861 : Nat := 118140960795 + 732861 * 2 ^ 59
def prefixEnd_732861 : Nat := 4983230072969 + 3 ^ 40 * 732861 * 2
def baseEnd_732861 : Nat := 250873297289841607778093

theorem tailTrace_732861 : CollatzResearch.WordTrace tailWord_732861 prefixEnd_732861 250873297289841607778093 := by
  unfold tailWord_732861
  simp only [CollatzResearch.WordTrace]
  refine ⟨26729636597977234539198437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17819757731984823026132291 26729636597977234539198437)
  ·
    refine ⟨5011806862120731476099707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26729636597977234539198437 5011806862120731476099707)
    ·
      refine ⟨7517710293181097214149561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011806862120731476099707 7517710293181097214149561)
      ·
        refine ⟨5638282719885822910612171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7517710293181097214149561 5638282719885822910612171)
        ·
          refine ⟨8457424079828734365918257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638282719885822910612171 8457424079828734365918257)
          ·
            refine ⟨6343068059871550774438693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8457424079828734365918257 6343068059871550774438693)
            ·
              refine ⟨1189325261225915770207255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6343068059871550774438693 1189325261225915770207255)
              ·
                refine ⟨1783987891838873655310883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189325261225915770207255 1783987891838873655310883)
                ·
                  refine ⟨2675981837758310482966325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783987891838873655310883 2675981837758310482966325)
                  ·
                    refine ⟨250873297289841607778093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2675981837758310482966325 250873297289841607778093)
                    ·
                      rfl

theorem cell22_732861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_732861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732861 prefixEnd_732861 := by exact prefixLift 732861
  have htrace : WordTrace (prefixWord ++ tailWord_732861) baseStart_732861 baseEnd_732861 := by
    simpa [prefixWord, tailWord_732861, baseEnd_732861] using wordTrace_append hprefix tailTrace_732861
  have hstable : (prefixWord ++ tailWord_732861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732861).length < 2 ^ (prefixWord ++ tailWord_732861).sum := by decide
  have hdescent : baseEnd_732861 < baseStart_732861 := by decide
  rcases family_descends (prefixWord ++ tailWord_732861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732940 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_732940 : Nat := 118140960795 + 732940 * 2 ^ 59
def prefixEnd_732940 : Nat := 4983230072969 + 3 ^ 40 * 732940 * 2
def baseEnd_732940 : Nat := 250900340604311735052851

theorem tailTrace_732940 : CollatzResearch.WordTrace tailWord_732940 prefixEnd_732940 250900340604311735052851 := by
  unfold tailWord_732940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13366258982345515515662137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17821678643127354020882849 13366258982345515515662137)
  ·
    refine ⟨10024694236759136636746603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13366258982345515515662137 10024694236759136636746603)
    ·
      refine ⟨15037041355138704955119905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10024694236759136636746603 15037041355138704955119905)
      ·
        refine ⟨11277781016354028716339929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15037041355138704955119905 11277781016354028716339929)
        ·
          refine ⟨8458335762265521537254947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277781016354028716339929 8458335762265521537254947)
          ·
            refine ⟨12687503643398282305882421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458335762265521537254947 12687503643398282305882421)
            ·
              refine ⟨1189453466568588966176477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12687503643398282305882421 1189453466568588966176477)
              ·
                refine ⟨446045049963220862316179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189453466568588966176477 446045049963220862316179)
                ·
                  refine ⟨669067574944831293474269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446045049963220862316179 669067574944831293474269)
                  ·
                    refine ⟨250900340604311735052851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669067574944831293474269 250900340604311735052851)
                    ·
                      rfl

theorem cell22_732940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_732940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_732940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_732940 prefixEnd_732940 := by exact prefixLift 732940
  have htrace : WordTrace (prefixWord ++ tailWord_732940) baseStart_732940 baseEnd_732940 := by
    simpa [prefixWord, tailWord_732940, baseEnd_732940] using wordTrace_append hprefix tailTrace_732940
  have hstable : (prefixWord ++ tailWord_732940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732940).length < 2 ^ (prefixWord ++ tailWord_732940).sum := by decide
  have hdescent : baseEnd_732940 < baseStart_732940 := by decide
  rcases family_descends (prefixWord ++ tailWord_732940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733000 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_733000 : Nat := 118140960795 + 733000 * 2 ^ 59
def prefixEnd_733000 : Nat := 4983230072969 + 3 ^ 40 * 733000 * 2
def baseEnd_733000 : Nat := 250920879830491578552667

theorem tailTrace_733000 : CollatzResearch.WordTrace tailWord_733000 prefixEnd_733000 250920879830491578552667 := by
  unfold tailWord_733000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367353172236830639254227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17823137562982440852338969 13367353172236830639254227)
  ·
    refine ⟨20051029758355245958881341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13367353172236830639254227 20051029758355245958881341)
    ·
      refine ⟨7519136159383217234580503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20051029758355245958881341 7519136159383217234580503)
      ·
        refine ⟨11278704239074825851870755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7519136159383217234580503 11278704239074825851870755)
        ·
          refine ⟨16918056358612238777806133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11278704239074825851870755 16918056358612238777806133)
          ·
            refine ⟨1586067783619897385419325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16918056358612238777806133 1586067783619897385419325)
            ·
              refine ⟨594775418857461519532247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1586067783619897385419325 594775418857461519532247)
              ·
                refine ⟨892163128286192279298371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594775418857461519532247 892163128286192279298371)
                ·
                  refine ⟨1338244692429288418947557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892163128286192279298371 1338244692429288418947557)
                  ·
                    refine ⟨250920879830491578552667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338244692429288418947557 250920879830491578552667)
                    ·
                      rfl

theorem cell22_733000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_733000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733000 prefixEnd_733000 := by exact prefixLift 733000
  have htrace : WordTrace (prefixWord ++ tailWord_733000) baseStart_733000 baseEnd_733000 := by
    simpa [prefixWord, tailWord_733000, baseEnd_733000] using wordTrace_append hprefix tailTrace_733000
  have hstable : (prefixWord ++ tailWord_733000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733000).length < 2 ^ (prefixWord ++ tailWord_733000).sum := by decide
  have hdescent : baseEnd_733000 < baseStart_733000 := by decide
  rcases family_descends (prefixWord ++ tailWord_733000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733015 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 4]
def baseStart_733015 : Nat := 118140960795 + 733015 * 2 ^ 59
def prefixEnd_733015 : Nat := 4983230072969 + 3 ^ 40 * 733015 * 2
def baseEnd_733015 : Nat := 83642004879012179809207

theorem tailTrace_733015 : CollatzResearch.WordTrace tailWord_733015 prefixEnd_733015 83642004879012179809207 := by
  unfold tailWord_733015
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735253439419318840304499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823502292946212560202999 26735253439419318840304499)
  ·
    refine ⟨40102880159128978260456749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26735253439419318840304499 40102880159128978260456749)
    ·
      refine ⟨15038580059673366847671281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40102880159128978260456749 15038580059673366847671281)
      ·
        refine ⟨11278935044755025135753461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15038580059673366847671281 11278935044755025135753461)
        ·
          refine ⟨1057400160445783606476887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11278935044755025135753461 1057400160445783606476887)
          ·
            refine ⟨1586100240668675409715331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057400160445783606476887 1586100240668675409715331)
            ·
              refine ⟨2379150361003013114572997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586100240668675409715331 2379150361003013114572997)
              ·
                refine ⟨446090692688064958982437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2379150361003013114572997 446090692688064958982437)
                ·
                  refine ⟨83642004879012179809207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446090692688064958982437 83642004879012179809207)
                  ·
                    rfl

theorem cell22_733015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 4].length) (baseStart_733015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733015 prefixEnd_733015 := by exact prefixLift 733015
  have htrace : WordTrace (prefixWord ++ tailWord_733015) baseStart_733015 baseEnd_733015 := by
    simpa [prefixWord, tailWord_733015, baseEnd_733015] using wordTrace_append hprefix tailTrace_733015
  have hstable : (prefixWord ++ tailWord_733015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733015).length < 2 ^ (prefixWord ++ tailWord_733015).sum := by decide
  have hdescent : baseEnd_733015 < baseStart_733015 := by decide
  rcases family_descends (prefixWord ++ tailWord_733015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733064 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_733064 : Nat := 118140960795 + 733064 * 2 ^ 59
def prefixEnd_733064 : Nat := 4983230072969 + 3 ^ 40 * 733064 * 2
def baseEnd_733064 : Nat := 250942788338416744952471

theorem tailTrace_733064 : CollatzResearch.WordTrace tailWord_733064 prefixEnd_733064 250942788338416744952471 := by
  unfold tailWord_733064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13368520308120900104419123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17824693744161200139225497 13368520308120900104419123)
  ·
    refine ⟨20052780462181350156628685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13368520308120900104419123 20052780462181350156628685)
    ·
      refine ⟨7519792673318006308735757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20052780462181350156628685 7519792673318006308735757)
      ·
        refine ⟨2819922252494252365775909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7519792673318006308735757 2819922252494252365775909)
        ·
          refine ⟨528735422342672318582983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2819922252494252365775909 528735422342672318582983)
          ·
            refine ⟨793103133514008477874475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528735422342672318582983 793103133514008477874475)
            ·
              refine ⟨1189654700271012716811713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793103133514008477874475 1189654700271012716811713)
              ·
                refine ⟨892241025203259537608785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189654700271012716811713 892241025203259537608785)
                ·
                  refine ⟨669180768902444653206589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892241025203259537608785 669180768902444653206589)
                  ·
                    refine ⟨250942788338416744952471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669180768902444653206589 250942788338416744952471)
                    ·
                      rfl

theorem cell22_733064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_733064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733064 prefixEnd_733064 := by exact prefixLift 733064
  have htrace : WordTrace (prefixWord ++ tailWord_733064) baseStart_733064 baseEnd_733064 := by
    simpa [prefixWord, tailWord_733064, baseEnd_733064] using wordTrace_append hprefix tailTrace_733064
  have hstable : (prefixWord ++ tailWord_733064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733064).length < 2 ^ (prefixWord ++ tailWord_733064).sum := by decide
  have hdescent : baseEnd_733064 < baseStart_733064 := by decide
  rcases family_descends (prefixWord ++ tailWord_733064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733109 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_733109 : Nat := 118140960795 + 733109 * 2 ^ 59
def prefixEnd_733109 : Nat := 4983230072969 + 3 ^ 40 * 733109 * 2
def baseEnd_733109 : Nat := 250958192758051627577333

theorem tailTrace_733109 : CollatzResearch.WordTrace tailWord_733109 prefixEnd_733109 250958192758051627577333 := by
  unfold tailWord_733109
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738681901078772894226381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17825787934052515262817587 26738681901078772894226381)
  ·
    refine ⟨10027005712904539835334893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26738681901078772894226381 10027005712904539835334893)
    ·
      refine ⟨3760127142339202438250585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10027005712904539835334893 3760127142339202438250585)
      ·
        refine ⟨2820095356754401828687939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3760127142339202438250585 2820095356754401828687939)
        ·
          refine ⟨4230143035131602743031909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820095356754401828687939 4230143035131602743031909)
          ·
            refine ⟨793151819087175514318483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4230143035131602743031909 793151819087175514318483)
            ·
              refine ⟨1189727728630763271477725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793151819087175514318483 1189727728630763271477725)
              ·
                refine ⟨446147898236536226804147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189727728630763271477725 446147898236536226804147)
                ·
                  refine ⟨669221847354804340206221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446147898236536226804147 669221847354804340206221)
                  ·
                    refine ⟨250958192758051627577333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669221847354804340206221 250958192758051627577333)
                    ·
                      rfl

theorem cell22_733109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_733109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733109 prefixEnd_733109 := by exact prefixLift 733109
  have htrace : WordTrace (prefixWord ++ tailWord_733109) baseStart_733109 baseEnd_733109 := by
    simpa [prefixWord, tailWord_733109, baseEnd_733109] using wordTrace_append hprefix tailTrace_733109
  have hstable : (prefixWord ++ tailWord_733109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733109).length < 2 ^ (prefixWord ++ tailWord_733109).sum := by decide
  have hdescent : baseEnd_733109 < baseStart_733109 := by decide
  rcases family_descends (prefixWord ++ tailWord_733109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733208 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_733208 : Nat := 118140960795 + 733208 * 2 ^ 59
def prefixEnd_733208 : Nat := 4983230072969 + 3 ^ 40 * 733208 * 2
def baseEnd_733208 : Nat := 250992082481248369352029

theorem tailTrace_733208 : CollatzResearch.WordTrace tailWord_733208 prefixEnd_733208 250992082481248369352029 := by
  unfold tailWord_733208
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371146363860056401040139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17828195151813408534720185 13371146363860056401040139)
  ·
    refine ⟨20056719545790084601560209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371146363860056401040139 20056719545790084601560209)
    ·
      refine ⟨15042539659342563451170157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20056719545790084601560209 15042539659342563451170157)
      ·
        refine ⟨5640952372253461294188809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15042539659342563451170157 5640952372253461294188809)
        ·
          refine ⟨4230714279190095970641607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5640952372253461294188809 4230714279190095970641607)
          ·
            refine ⟨6346071418785143955962411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230714279190095970641607 6346071418785143955962411)
            ·
              refine ⟨9519107128177715933943617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346071418785143955962411 9519107128177715933943617)
              ·
                refine ⟨7139330346133286950457713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9519107128177715933943617 7139330346133286950457713)
                ·
                  refine ⟨5354497759599965212843285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139330346133286950457713 5354497759599965212843285)
                  ·
                    refine ⟨250992082481248369352029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5354497759599965212843285 250992082481248369352029)
                    ·
                      rfl

theorem cell22_733208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_733208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733208 prefixEnd_733208 := by exact prefixLift 733208
  have htrace : WordTrace (prefixWord ++ tailWord_733208) baseStart_733208 baseEnd_733208 := by
    simpa [prefixWord, tailWord_733208, baseEnd_733208] using wordTrace_append hprefix tailTrace_733208
  have hstable : (prefixWord ++ tailWord_733208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733208).length < 2 ^ (prefixWord ++ tailWord_733208).sum := by decide
  have hdescent : baseEnd_733208 < baseStart_733208 := by decide
  rcases family_descends (prefixWord ++ tailWord_733208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733210 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_733210 : Nat := 118140960795 + 733210 * 2 ^ 59
def prefixEnd_733210 : Nat := 4983230072969 + 3 ^ 40 * 733210 * 2
def baseEnd_733210 : Nat := 250992767122121030802023

theorem tailTrace_733210 : CollatzResearch.WordTrace tailWord_733210 prefixEnd_733210 250992767122121030802023 := by
  unfold tailWord_733210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685591418428216785913271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17828243782475244762435389 6685591418428216785913271)
  ·
    refine ⟨10028387127642325178869907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6685591418428216785913271 10028387127642325178869907)
    ·
      refine ⟨15042580691463487768304861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028387127642325178869907 15042580691463487768304861)
      ·
        refine ⟨5640967759298807913114323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15042580691463487768304861 5640967759298807913114323)
        ·
          refine ⟨8461451638948211869671485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640967759298807913114323 8461451638948211869671485)
          ·
            refine ⟨3173044364605579451126807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8461451638948211869671485 3173044364605579451126807)
            ·
              refine ⟨4759566546908369176690211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173044364605579451126807 4759566546908369176690211)
              ·
                refine ⟨7139349820362553765035317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759566546908369176690211 7139349820362553765035317)
                ·
                  refine ⟨669314045658989415472061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7139349820362553765035317 669314045658989415472061)
                  ·
                    refine ⟨250992767122121030802023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669314045658989415472061 250992767122121030802023)
                    ·
                      rfl

theorem cell22_733210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_733210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733210 prefixEnd_733210 := by exact prefixLift 733210
  have htrace : WordTrace (prefixWord ++ tailWord_733210) baseStart_733210 baseEnd_733210 := by
    simpa [prefixWord, tailWord_733210, baseEnd_733210] using wordTrace_append hprefix tailTrace_733210
  have hstable : (prefixWord ++ tailWord_733210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733210).length < 2 ^ (prefixWord ++ tailWord_733210).sum := by decide
  have hdescent : baseEnd_733210 < baseStart_733210 := by decide
  rcases family_descends (prefixWord ++ tailWord_733210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733240 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_733240 : Nat := 118140960795 + 733240 * 2 ^ 59
def prefixEnd_733240 : Nat := 4983230072969 + 3 ^ 40 * 733240 * 2
def baseEnd_733240 : Nat := 83667678911736984183977

theorem tailTrace_733240 : CollatzResearch.WordTrace tailWord_733240 prefixEnd_733240 83667678911736984183977 := by
  unfold tailWord_733240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371729931802091133622587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17828973242402788178163449 13371729931802091133622587)
  ·
    refine ⟨20057594897703136700433881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371729931802091133622587 20057594897703136700433881)
    ·
      refine ⟨15043196173277352525325411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20057594897703136700433881 15043196173277352525325411)
      ·
        refine ⟨22564794259916028787988117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15043196173277352525325411 22564794259916028787988117)
        ·
          refine ⟨1057724730933563849436943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22564794259916028787988117 1057724730933563849436943)
          ·
            refine ⟨1586587096400345774155415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057724730933563849436943 1586587096400345774155415)
            ·
              refine ⟨2379880644600518661233123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586587096400345774155415 2379880644600518661233123)
              ·
                refine ⟨3569820966900777991849685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379880644600518661233123 3569820966900777991849685)
                ·
                  refine ⟨83667678911736984183977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3569820966900777991849685 83667678911736984183977)
                  ·
                    rfl

theorem cell22_733240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_733240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733240 prefixEnd_733240 := by exact prefixLift 733240
  have htrace : WordTrace (prefixWord ++ tailWord_733240) baseStart_733240 baseEnd_733240 := by
    simpa [prefixWord, tailWord_733240, baseEnd_733240] using wordTrace_append hprefix tailTrace_733240
  have hstable : (prefixWord ++ tailWord_733240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733240).length < 2 ^ (prefixWord ++ tailWord_733240).sum := by decide
  have hdescent : baseEnd_733240 < baseStart_733240 := by decide
  rcases family_descends (prefixWord ++ tailWord_733240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733302 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_733302 : Nat := 118140960795 + 733302 * 2 ^ 59
def prefixEnd_733302 : Nat := 4983230072969 + 3 ^ 40 * 733302 * 2
def baseEnd_733302 : Nat := 83674753534087819167247

theorem tailTrace_733302 : CollatzResearch.WordTrace tailWord_733302 prefixEnd_733302 83674753534087819167247 := by
  unfold tailWord_733302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671607574336222928500135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17830480792919711237334773 1671607574336222928500135)
  ·
    refine ⟨2507411361504334392750203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671607574336222928500135 2507411361504334392750203)
    ·
      refine ⟨3761117042256501589125305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507411361504334392750203 3761117042256501589125305)
      ·
        refine ⟨2820837781692376191843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3761117042256501589125305 2820837781692376191843979)
        ·
          refine ⟨4231256672538564287765969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820837781692376191843979 4231256672538564287765969)
          ·
            refine ⟨3173442504403923215824477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231256672538564287765969 3173442504403923215824477)
            ·
              refine ⟨1190040939151471205934179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3173442504403923215824477 1190040939151471205934179)
              ·
                refine ⟨1785061408727206808901269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190040939151471205934179 1785061408727206808901269)
                ·
                  refine ⟨83674753534087819167247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1785061408727206808901269 83674753534087819167247)
                  ·
                    rfl

theorem cell22_733302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_733302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733302 prefixEnd_733302 := by exact prefixLift 733302
  have htrace : WordTrace (prefixWord ++ tailWord_733302) baseStart_733302 baseEnd_733302 := by
    simpa [prefixWord, tailWord_733302, baseEnd_733302] using wordTrace_append hprefix tailTrace_733302
  have hstable : (prefixWord ++ tailWord_733302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733302).length < 2 ^ (prefixWord ++ tailWord_733302).sum := by decide
  have hdescent : baseEnd_733302 < baseStart_733302 := by decide
  rcases family_descends (prefixWord ++ tailWord_733302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733330 : List Nat := [3, 2, 3, 1, 1, 1, 1, 10]
def baseStart_733330 : Nat := 118140960795 + 733330 * 2 ^ 59
def prefixEnd_733330 : Nat := 4983230072969 + 3 ^ 40 * 733330 * 2
def baseEnd_733330 : Nat := 27892649508275635311295

theorem tailTrace_733330 : CollatzResearch.WordTrace tailWord_733330 prefixEnd_733330 27892649508275635311295 := by
  unfold tailWord_733330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686685608319531909505361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17831161622185418425347629 6686685608319531909505361)
  ·
    refine ⟨5015014206239648932129021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6686685608319531909505361 5015014206239648932129021)
    ·
      refine ⟨1880630327339868349548383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5015014206239648932129021 1880630327339868349548383)
      ·
        refine ⟨2820945491009802524322575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880630327339868349548383 2820945491009802524322575)
        ·
          refine ⟨4231418236514703786483863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820945491009802524322575 4231418236514703786483863)
          ·
            refine ⟨6347127354772055679725795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231418236514703786483863 6347127354772055679725795)
            ·
              refine ⟨9520691032158083519588693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347127354772055679725795 9520691032158083519588693)
              ·
                refine ⟨27892649508275635311295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9520691032158083519588693 27892649508275635311295)
                ·
                  rfl

theorem cell22_733330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_733330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733330 prefixEnd_733330 := by exact prefixLift 733330
  have htrace : WordTrace (prefixWord ++ tailWord_733330) baseStart_733330 baseEnd_733330 := by
    simpa [prefixWord, tailWord_733330, baseEnd_733330] using wordTrace_append hprefix tailTrace_733330
  have hstable : (prefixWord ++ tailWord_733330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733330).length < 2 ^ (prefixWord ++ tailWord_733330).sum := by decide
  have hdescent : baseEnd_733330 < baseStart_733330 := by decide
  rcases family_descends (prefixWord ++ tailWord_733330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733351 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 2, 3]
def baseStart_733351 : Nat := 118140960795 + 733351 * 2 ^ 59
def prefixEnd_733351 : Nat := 4983230072969 + 3 ^ 40 * 733351 * 2
def baseEnd_733351 : Nat := 251041034303643663026591

theorem tailTrace_733351 : CollatzResearch.WordTrace tailWord_733351 prefixEnd_733351 251041034303643663026591 := by
  unfold tailWord_733351
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747508366202048224535907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17831672244134698816357271 26747508366202048224535907)
  ·
    refine ⟨40121262549303072336803861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26747508366202048224535907 40121262549303072336803861)
    ·
      refine ⟨1880684181998581515787681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40121262549303072336803861 1880684181998581515787681)
      ·
        refine ⟨1410513136498936136840761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1880684181998581515787681 1410513136498936136840761)
        ·
          refine ⟨1057884852374202102630571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410513136498936136840761 1057884852374202102630571)
          ·
            refine ⟨1586827278561303153945857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057884852374202102630571 1586827278561303153945857)
            ·
              refine ⟨1190120458920977365459393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586827278561303153945857 1190120458920977365459393)
              ·
                refine ⟨892590344190733024094545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190120458920977365459393 892590344190733024094545)
                ·
                  refine ⟨669442758143049768070909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892590344190733024094545 669442758143049768070909)
                  ·
                    refine ⟨251041034303643663026591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669442758143049768070909 251041034303643663026591)
                    ·
                      rfl

theorem cell22_733351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_733351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733351 prefixEnd_733351 := by exact prefixLift 733351
  have htrace : WordTrace (prefixWord ++ tailWord_733351) baseStart_733351 baseEnd_733351 := by
    simpa [prefixWord, tailWord_733351, baseEnd_733351] using wordTrace_append hprefix tailTrace_733351
  have hstable : (prefixWord ++ tailWord_733351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733351).length < 2 ^ (prefixWord ++ tailWord_733351).sum := by decide
  have hdescent : baseEnd_733351 < baseStart_733351 := by decide
  rcases family_descends (prefixWord ++ tailWord_733351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733362 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_733362 : Nat := 118140960795 + 733362 * 2 ^ 59
def prefixEnd_733362 : Nat := 4983230072969 + 3 ^ 40 * 733362 * 2
def baseEnd_733362 : Nat := 251044799828443301001557

theorem tailTrace_733362 : CollatzResearch.WordTrace tailWord_733362 prefixEnd_733362 251044799828443301001557 := by
  unfold tailWord_733362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686977392290549275796585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17831939712774798068790893 6686977392290549275796585)
  ·
    refine ⟨5015233044217911956847439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6686977392290549275796585 5015233044217911956847439)
    ·
      refine ⟨7522849566326867935271159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015233044217911956847439 7522849566326867935271159)
      ·
        refine ⟨11284274349490301902906739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7522849566326867935271159 11284274349490301902906739)
        ·
          refine ⟨16926411524235452854360109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11284274349490301902906739 16926411524235452854360109)
          ·
            refine ⟨6347404321588294820385041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16926411524235452854360109 6347404321588294820385041)
            ·
              refine ⟨4760553241191221115288781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347404321588294820385041 4760553241191221115288781)
              ·
                refine ⟨1785207465446707918233293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4760553241191221115288781 1785207465446707918233293)
                ·
                  refine ⟨669452799542515469337485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1785207465446707918233293 669452799542515469337485)
                  ·
                    refine ⟨251044799828443301001557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669452799542515469337485 251044799828443301001557)
                    ·
                      rfl

theorem cell22_733362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_733362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733362 prefixEnd_733362 := by exact prefixLift 733362
  have htrace : WordTrace (prefixWord ++ tailWord_733362) baseStart_733362 baseEnd_733362 := by
    simpa [prefixWord, tailWord_733362, baseEnd_733362] using wordTrace_append hprefix tailTrace_733362
  have hstable : (prefixWord ++ tailWord_733362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733362).length < 2 ^ (prefixWord ++ tailWord_733362).sum := by decide
  have hdescent : baseEnd_733362 < baseStart_733362 := by decide
  rcases family_descends (prefixWord ++ tailWord_733362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733452 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_733452 : Nat := 118140960795 + 733452 * 2 ^ 59
def prefixEnd_733452 : Nat := 4983230072969 + 3 ^ 40 * 733452 * 2
def baseEnd_733452 : Nat := 251075608667713066251281

theorem tailTrace_733452 : CollatzResearch.WordTrace tailWord_733452 prefixEnd_733452 251075608667713066251281 := by
  unfold tailWord_733452
  simp only [CollatzResearch.WordTrace]
  refine ⟨13375596069418071236981305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17834128092557428315975073 13375596069418071236981305)
  ·
    refine ⟨10031697052063553427735979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13375596069418071236981305 10031697052063553427735979)
    ·
      refine ⟨15047545578095330141603969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10031697052063553427735979 15047545578095330141603969)
      ·
        refine ⟨11285659183571497606202977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15047545578095330141603969 11285659183571497606202977)
        ·
          refine ⟨8464244387678623204652233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11285659183571497606202977 8464244387678623204652233)
          ·
            refine ⟨6348183290758967403489175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8464244387678623204652233 6348183290758967403489175)
            ·
              refine ⟨9522274936138451105233763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348183290758967403489175 9522274936138451105233763)
              ·
                refine ⟨14283412404207676657850645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9522274936138451105233763 14283412404207676657850645)
                ·
                  refine ⟨669534956447234843336749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14283412404207676657850645 669534956447234843336749)
                  ·
                    refine ⟨251075608667713066251281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669534956447234843336749 251075608667713066251281)
                    ·
                      rfl

theorem cell22_733452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_733452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733452 prefixEnd_733452 := by exact prefixLift 733452
  have htrace : WordTrace (prefixWord ++ tailWord_733452) baseStart_733452 baseEnd_733452 := by
    simpa [prefixWord, tailWord_733452, baseEnd_733452] using wordTrace_append hprefix tailTrace_733452
  have hstable : (prefixWord ++ tailWord_733452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733452).length < 2 ^ (prefixWord ++ tailWord_733452).sum := by decide
  have hdescent : baseEnd_733452 < baseStart_733452 := by decide
  rcases family_descends (prefixWord ++ tailWord_733452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733471 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 4]
def baseStart_733471 : Nat := 118140960795 + 733471 * 2 ^ 59
def prefixEnd_733471 : Nat := 4983230072969 + 3 ^ 40 * 733471 * 2
def baseEnd_733471 : Nat := 83694037585334450008741

theorem tailTrace_733471 : CollatzResearch.WordTrace tailWord_733471 prefixEnd_733471 83694037585334450008741 := by
  unfold tailWord_733471
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751885125767308718904267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17834590083844872479269511 26751885125767308718904267)
  ·
    refine ⟨40127827688650963078356401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26751885125767308718904267 40127827688650963078356401)
    ·
      refine ⟨30095870766488222308767301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40127827688650963078356401 30095870766488222308767301)
      ·
        refine ⟨5642975768716541682893869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30095870766488222308767301 5642975768716541682893869)
        ·
          refine ⟨2116115913268703131085201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5642975768716541682893869 2116115913268703131085201)
          ·
            refine ⟨1587086934951527348313901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116115913268703131085201 1587086934951527348313901)
            ·
              refine ⟨595157600606822755617713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1587086934951527348313901 595157600606822755617713)
              ·
                refine ⟨446368200455117066713285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595157600606822755617713 446368200455117066713285)
                ·
                  refine ⟨83694037585334450008741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446368200455117066713285 83694037585334450008741)
                  ·
                    rfl

theorem cell22_733471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 4].length) (baseStart_733471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733471 prefixEnd_733471 := by exact prefixLift 733471
  have htrace : WordTrace (prefixWord ++ tailWord_733471) baseStart_733471 baseEnd_733471 := by
    simpa [prefixWord, tailWord_733471, baseEnd_733471] using wordTrace_append hprefix tailTrace_733471
  have hstable : (prefixWord ++ tailWord_733471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733471).length < 2 ^ (prefixWord ++ tailWord_733471).sum := by decide
  have hdescent : baseEnd_733471 < baseStart_733471 := by decide
  rcases family_descends (prefixWord ++ tailWord_733471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733544 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_733544 : Nat := 118140960795 + 733544 * 2 ^ 59
def prefixEnd_733544 : Nat := 4983230072969 + 3 ^ 40 * 733544 * 2
def baseEnd_733544 : Nat := 83702367382618497650333

theorem tailTrace_733544 : CollatzResearch.WordTrace tailWord_733544 prefixEnd_733544 83702367382618497650333 := by
  unfold tailWord_733544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377273827251421093155843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17836365103001894790874457 13377273827251421093155843)
  ·
    refine ⟨20065910740877131639733765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13377273827251421093155843 20065910740877131639733765)
    ·
      refine ⟨3762358263914462182450081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20065910740877131639733765 3762358263914462182450081)
      ·
        refine ⟨2821768697935846636837561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3762358263914462182450081 2821768697935846636837561)
        ·
          refine ⟨2116326523451884977628171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821768697935846636837561 2116326523451884977628171)
          ·
            refine ⟨3174489785177827466442257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116326523451884977628171 3174489785177827466442257)
            ·
              refine ⟨2380867338883370599831693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3174489785177827466442257 2380867338883370599831693)
              ·
                refine ⟨892825252081263974936885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2380867338883370599831693 892825252081263974936885)
                ·
                  refine ⟨83702367382618497650333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 892825252081263974936885 83702367382618497650333)
                  ·
                    rfl

theorem cell22_733544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_733544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733544 prefixEnd_733544 := by exact prefixLift 733544
  have htrace : WordTrace (prefixWord ++ tailWord_733544) baseStart_733544 baseEnd_733544 := by
    simpa [prefixWord, tailWord_733544, baseEnd_733544] using wordTrace_append hprefix tailTrace_733544
  have hstable : (prefixWord ++ tailWord_733544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733544).length < 2 ^ (prefixWord ++ tailWord_733544).sum := by decide
  have hdescent : baseEnd_733544 < baseStart_733544 := by decide
  rcases family_descends (prefixWord ++ tailWord_733544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733572 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_733572 : Nat := 118140960795 + 733572 * 2 ^ 59
def prefixEnd_733572 : Nat := 4983230072969 + 3 ^ 40 * 733572 * 2
def baseEnd_733572 : Nat := 83705562373357584416971

theorem tailTrace_733572 : CollatzResearch.WordTrace tailWord_733572 prefixEnd_733572 83705562373357584416971 := by
  unfold tailWord_733572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377784449200701484165485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17837045932267601978887313 13377784449200701484165485)
  ·
    refine ⟨5016669168450263056562057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13377784449200701484165485 5016669168450263056562057)
    ·
      refine ⟨3762501876337697292421543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5016669168450263056562057 3762501876337697292421543)
      ·
        refine ⟨5643752814506545938632315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762501876337697292421543 5643752814506545938632315)
        ·
          refine ⟨8465629221759818907948473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643752814506545938632315 8465629221759818907948473)
          ·
            refine ⟨6349221916319864180961355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8465629221759818907948473 6349221916319864180961355)
            ·
              refine ⟨9523832874479796271442033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349221916319864180961355 9523832874479796271442033)
              ·
                refine ⟨7142874655859847203581525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9523832874479796271442033 7142874655859847203581525)
                ·
                  refine ⟨83705562373357584416971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7142874655859847203581525 83705562373357584416971)
                  ·
                    rfl

theorem cell22_733572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_733572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733572 prefixEnd_733572 := by exact prefixLift 733572
  have htrace : WordTrace (prefixWord ++ tailWord_733572) baseStart_733572 baseEnd_733572 := by
    simpa [prefixWord, tailWord_733572, baseEnd_733572] using wordTrace_append hprefix tailTrace_733572
  have hstable : (prefixWord ++ tailWord_733572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733572).length < 2 ^ (prefixWord ++ tailWord_733572).sum := by decide
  have hdescent : baseEnd_733572 < baseStart_733572 := by decide
  rcases family_descends (prefixWord ++ tailWord_733572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733578 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_733578 : Nat := 118140960795 + 733578 * 2 ^ 59
def prefixEnd_733578 : Nat := 4983230072969 + 3 ^ 40 * 733578 * 2
def baseEnd_733578 : Nat := 83706247014230245866965

theorem tailTrace_733578 : CollatzResearch.WordTrace tailWord_733578 prefixEnd_733578 83706247014230245866965 := by
  unfold tailWord_733578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688946934094916498262347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17837191824253110662032925 6688946934094916498262347)
  ·
    refine ⟨10033420401142374747393521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6688946934094916498262347 10033420401142374747393521)
    ·
      refine ⟨7525065300856781060545141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10033420401142374747393521 7525065300856781060545141)
      ·
        refine ⟨705474871955323224426107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7525065300856781060545141 705474871955323224426107)
        ·
          refine ⟨1058212307932984836639161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705474871955323224426107 1058212307932984836639161)
          ·
            refine ⟨793659230949738627479371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058212307932984836639161 793659230949738627479371)
            ·
              refine ⟨1190488846424607941219057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793659230949738627479371 1190488846424607941219057)
              ·
                refine ⟨892866634818455955914293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190488846424607941219057 892866634818455955914293)
                ·
                  refine ⟨83706247014230245866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 892866634818455955914293 83706247014230245866965)
                  ·
                    rfl

theorem cell22_733578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_733578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733578 prefixEnd_733578 := by exact prefixLift 733578
  have htrace : WordTrace (prefixWord ++ tailWord_733578) baseStart_733578 baseEnd_733578 := by
    simpa [prefixWord, tailWord_733578, baseEnd_733578] using wordTrace_append hprefix tailTrace_733578
  have hstable : (prefixWord ++ tailWord_733578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733578).length < 2 ^ (prefixWord ++ tailWord_733578).sum := by decide
  have hdescent : baseEnd_733578 < baseStart_733578 := by decide
  rcases family_descends (prefixWord ++ tailWord_733578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733604 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_733604 : Nat := 118140960795 + 733604 * 2 ^ 59
def prefixEnd_733604 : Nat := 4983230072969 + 3 ^ 40 * 733604 * 2
def baseEnd_733604 : Nat := 251127641374035336450815

theorem tailTrace_733604 : CollatzResearch.WordTrace tailWord_733604 prefixEnd_733604 251127641374035336450815 := by
  unfold tailWord_733604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13378368017142736216747933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17837824022856981622330577 13378368017142736216747933)
  ·
    refine ⟨5016888006428526081280475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13378368017142736216747933 5016888006428526081280475)
    ·
      refine ⟨7525332009642789121920713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5016888006428526081280475 7525332009642789121920713)
      ·
        refine ⟨5643999007232091841440535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7525332009642789121920713 5643999007232091841440535)
        ·
          refine ⟨8465998510848137762160803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643999007232091841440535 8465998510848137762160803)
          ·
            refine ⟨12698997766272206643241205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465998510848137762160803 12698997766272206643241205)
            ·
              refine ⟨1190531040588019372803863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12698997766272206643241205 1190531040588019372803863)
              ·
                refine ⟨1785796560882029059205795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190531040588019372803863 1785796560882029059205795)
                ·
                  refine ⟨2678694841323043588808693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785796560882029059205795 2678694841323043588808693)
                  ·
                    refine ⟨251127641374035336450815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2678694841323043588808693 251127641374035336450815)
                    ·
                      rfl

theorem cell22_733604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_733604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733604 prefixEnd_733604 := by exact prefixLift 733604
  have htrace : WordTrace (prefixWord ++ tailWord_733604) baseStart_733604 baseEnd_733604 := by
    simpa [prefixWord, tailWord_733604, baseEnd_733604] using wordTrace_append hprefix tailTrace_733604
  have hstable : (prefixWord ++ tailWord_733604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733604).length < 2 ^ (prefixWord ++ tailWord_733604).sum := by decide
  have hdescent : baseEnd_733604 < baseStart_733604 := by decide
  rcases family_descends (prefixWord ++ tailWord_733604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733608 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_733608 : Nat := 118140960795 + 733608 * 2 ^ 59
def prefixEnd_733608 : Nat := 4983230072969 + 3 ^ 40 * 733608 * 2
def baseEnd_733608 : Nat := 251129010655780659350803

theorem tailTrace_733608 : CollatzResearch.WordTrace tailWord_733608 prefixEnd_733608 251129010655780659350803 := by
  unfold tailWord_733608
  simp only [CollatzResearch.WordTrace]
  refine ⟨13378440963135490558320739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17837921284180654077760985 13378440963135490558320739)
  ·
    refine ⟨20067661444703235837481109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13378440963135490558320739 20067661444703235837481109)
    ·
      refine ⟨940671630220464179881927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20067661444703235837481109 940671630220464179881927)
      ·
        refine ⟨1411007445330696269822891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940671630220464179881927 1411007445330696269822891)
        ·
          refine ⟨2116511167996044404734337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411007445330696269822891 2116511167996044404734337)
          ·
            refine ⟨1587383375997033303550753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116511167996044404734337 1587383375997033303550753)
            ·
              refine ⟨1190537531997774977663065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587383375997033303550753 1190537531997774977663065)
              ·
                refine ⟨892903148998331233247299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190537531997774977663065 892903148998331233247299)
                ·
                  refine ⟨1339354723497496849870949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892903148998331233247299 1339354723497496849870949)
                  ·
                    refine ⟨251129010655780659350803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1339354723497496849870949 251129010655780659350803)
                    ·
                      rfl

theorem cell22_733608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_733608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733608 prefixEnd_733608 := by exact prefixLift 733608
  have htrace : WordTrace (prefixWord ++ tailWord_733608) baseStart_733608 baseEnd_733608 := by
    simpa [prefixWord, tailWord_733608, baseEnd_733608] using wordTrace_append hprefix tailTrace_733608
  have hstable : (prefixWord ++ tailWord_733608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733608).length < 2 ^ (prefixWord ++ tailWord_733608).sum := by decide
  have hdescent : baseEnd_733608 < baseStart_733608 := by decide
  rcases family_descends (prefixWord ++ tailWord_733608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733647 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_733647 : Nat := 118140960795 + 733647 * 2 ^ 59
def prefixEnd_733647 : Nat := 4983230072969 + 3 ^ 40 * 733647 * 2
def baseEnd_733647 : Nat := 251142361152797557625683

theorem tailTrace_733647 : CollatzResearch.WordTrace tailWord_733647 prefixEnd_733647 251142361152797557625683 := by
  unfold tailWord_733647
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758304373129690777311195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17838869582086460518207463 26758304373129690777311195)
  ·
    refine ⟨40137456559694536165966793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26758304373129690777311195 40137456559694536165966793)
    ·
      refine ⟨30103092419770902124475095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40137456559694536165966793 30103092419770902124475095)
      ·
        refine ⟨45154638629656353186712643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30103092419770902124475095 45154638629656353186712643)
        ·
          refine ⟨67731957944484529780068965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45154638629656353186712643 67731957944484529780068965)
          ·
            refine ⟨12699742114590849333762931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67731957944484529780068965 12699742114590849333762931)
            ·
              refine ⟨19049613171886274000644397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12699742114590849333762931 19049613171886274000644397)
              ·
                refine ⟨7143604939457352750241649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19049613171886274000644397 7143604939457352750241649)
                ·
                  refine ⟨5357703704593014562681237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7143604939457352750241649 5357703704593014562681237)
                  ·
                    refine ⟨251142361152797557625683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5357703704593014562681237 251142361152797557625683)
                    ·
                      rfl

theorem cell22_733647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_733647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733647 prefixEnd_733647 := by exact prefixLift 733647
  have htrace : WordTrace (prefixWord ++ tailWord_733647) baseStart_733647 baseEnd_733647 := by
    simpa [prefixWord, tailWord_733647, baseEnd_733647] using wordTrace_append hprefix tailTrace_733647
  have hstable : (prefixWord ++ tailWord_733647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733647).length < 2 ^ (prefixWord ++ tailWord_733647).sum := by decide
  have hdescent : baseEnd_733647 < baseStart_733647 := by decide
  rcases family_descends (prefixWord ++ tailWord_733647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733700 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_733700 : Nat := 118140960795 + 733700 * 2 ^ 59
def prefixEnd_733700 : Nat := 4983230072969 + 3 ^ 40 * 733700 * 2
def baseEnd_733700 : Nat := 251160504135923086050521

theorem tailTrace_733700 : CollatzResearch.WordTrace tailWord_733700 prefixEnd_733700 251160504135923086050521 := by
  unfold tailWord_733700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13380118720968840414495277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17840158294625120552660369 13380118720968840414495277)
  ·
    refine ⟨5017544520363315155435729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13380118720968840414495277 5017544520363315155435729)
    ·
      refine ⟨3763158390272486366576797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5017544520363315155435729 3763158390272486366576797)
      ·
        refine ⟨1411184396352182387466299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3763158390272486366576797 1411184396352182387466299)
        ·
          refine ⟨2116776594528273581199449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411184396352182387466299 2116776594528273581199449)
          ·
            refine ⟨1587582445896205185899587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116776594528273581199449 1587582445896205185899587)
            ·
              refine ⟨2381373668844307778849381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587582445896205185899587 2381373668844307778849381)
              ·
                refine ⟨446507562908307708534259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2381373668844307778849381 446507562908307708534259)
                ·
                  refine ⟨669761344362461562801389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446507562908307708534259 669761344362461562801389)
                  ·
                    refine ⟨251160504135923086050521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669761344362461562801389 251160504135923086050521)
                    ·
                      rfl

theorem cell22_733700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_733700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733700 prefixEnd_733700 := by exact prefixLift 733700
  have htrace : WordTrace (prefixWord ++ tailWord_733700) baseStart_733700 baseEnd_733700 := by
    simpa [prefixWord, tailWord_733700, baseEnd_733700] using wordTrace_append hprefix tailTrace_733700
  have hstable : (prefixWord ++ tailWord_733700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733700).length < 2 ^ (prefixWord ++ tailWord_733700).sum := by decide
  have hdescent : baseEnd_733700 < baseStart_733700 := by decide
  rcases family_descends (prefixWord ++ tailWord_733700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733724 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_733724 : Nat := 118140960795 + 733724 * 2 ^ 59
def prefixEnd_733724 : Nat := 4983230072969 + 3 ^ 40 * 733724 * 2
def baseEnd_733724 : Nat := 83722906608798341150149

theorem tailTrace_733724 : CollatzResearch.WordTrace tailWord_733724 prefixEnd_733724 83722906608798341150149 := by
  unfold tailWord_733724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13380556396925366463932113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17840741862567155285242817 13380556396925366463932113)
  ·
    refine ⟨10035417297694024847949085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13380556396925366463932113 10035417297694024847949085)
    ·
      refine ⟨3763281486635259317980907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10035417297694024847949085 3763281486635259317980907)
      ·
        refine ⟨5644922229952888976971361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763281486635259317980907 5644922229952888976971361)
        ·
          refine ⟨4233691672464666732728521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5644922229952888976971361 4233691672464666732728521)
          ·
            refine ⟨3175268754348500049546391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233691672464666732728521 3175268754348500049546391)
            ·
              refine ⟨4762903131522750074319587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175268754348500049546391 4762903131522750074319587)
              ·
                refine ⟨7144354697284125111479381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762903131522750074319587 7144354697284125111479381)
                ·
                  refine ⟨83722906608798341150149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7144354697284125111479381 83722906608798341150149)
                  ·
                    rfl

theorem cell22_733724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_733724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733724 prefixEnd_733724 := by exact prefixLift 733724
  have htrace : WordTrace (prefixWord ++ tailWord_733724) baseStart_733724 baseEnd_733724 := by
    simpa [prefixWord, tailWord_733724, baseEnd_733724] using wordTrace_append hprefix tailTrace_733724
  have hstable : (prefixWord ++ tailWord_733724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733724).length < 2 ^ (prefixWord ++ tailWord_733724).sum := by decide
  have hdescent : baseEnd_733724 < baseStart_733724 := by decide
  rcases family_descends (prefixWord ++ tailWord_733724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733773 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_733773 : Nat := 118140960795 + 733773 * 2 ^ 59
def prefixEnd_733773 : Nat := 4983230072969 + 3 ^ 40 * 733773 * 2
def baseEnd_733773 : Nat := 251185493527775228975297

theorem tailTrace_733773 : CollatzResearch.WordTrace tailWord_733773 prefixEnd_733773 251185493527775228975297 := by
  unfold tailWord_733773
  simp only [CollatzResearch.WordTrace]
  refine ⟨26762899970673214296397973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17841933313782142864265315 26762899970673214296397973)
  ·
    refine ⟨1254510936125306920143655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26762899970673214296397973 1254510936125306920143655)
    ·
      refine ⟨1881766404187960380215483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254510936125306920143655 1881766404187960380215483)
      ·
        refine ⟨2822649606281940570323225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881766404187960380215483 2822649606281940570323225)
        ·
          refine ⟨2116987204711455427742419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822649606281940570323225 2116987204711455427742419)
          ·
            refine ⟨3175480807067183141613629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116987204711455427742419 3175480807067183141613629)
            ·
              refine ⟨1190805302650193678105111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3175480807067183141613629 1190805302650193678105111)
              ·
                refine ⟨1786207953975290517157667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190805302650193678105111 1786207953975290517157667)
                ·
                  refine ⟨2679311930962935775736501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786207953975290517157667 2679311930962935775736501)
                  ·
                    refine ⟨251185493527775228975297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2679311930962935775736501 251185493527775228975297)
                    ·
                      rfl

theorem cell22_733773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_733773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733773 prefixEnd_733773 := by exact prefixLift 733773
  have htrace : WordTrace (prefixWord ++ tailWord_733773) baseStart_733773 baseEnd_733773 := by
    simpa [prefixWord, tailWord_733773, baseEnd_733773] using wordTrace_append hprefix tailTrace_733773
  have hstable : (prefixWord ++ tailWord_733773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733773).length < 2 ^ (prefixWord ++ tailWord_733773).sum := by decide
  have hdescent : baseEnd_733773 < baseStart_733773 := by decide
  rcases family_descends (prefixWord ++ tailWord_733773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733799 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_733799 : Nat := 118140960795 + 733799 * 2 ^ 59
def prefixEnd_733799 : Nat := 4983230072969 + 3 ^ 40 * 733799 * 2
def baseEnd_733799 : Nat := 251194393859119827825217

theorem tailTrace_733799 : CollatzResearch.WordTrace tailWord_733799 prefixEnd_733799 251194393859119827825217 := by
  unfold tailWord_733799
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763848268579020736844451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17842565512386013824562967 26763848268579020736844451)
  ·
    refine ⟨40145772402868531105266677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26763848268579020736844451 40145772402868531105266677)
    ·
      refine ⟨3763666162768924791118751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40145772402868531105266677 3763666162768924791118751)
      ·
        refine ⟨5645499244153387186678127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763666162768924791118751 5645499244153387186678127)
        ·
          refine ⟨8468248866230080780017191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645499244153387186678127 8468248866230080780017191)
          ·
            refine ⟨12702373299345121170025787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468248866230080780017191 12702373299345121170025787)
            ·
              refine ⟨19053559949017681755038681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702373299345121170025787 19053559949017681755038681)
              ·
                refine ⟨14290169961763261316279011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19053559949017681755038681 14290169961763261316279011)
                ·
                  refine ⟨21435254942644891974418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14290169961763261316279011 21435254942644891974418517)
                  ·
                    refine ⟨251194393859119827825217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21435254942644891974418517 251194393859119827825217)
                    ·
                      rfl

theorem cell22_733799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_733799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733799 prefixEnd_733799 := by exact prefixLift 733799
  have htrace : WordTrace (prefixWord ++ tailWord_733799) baseStart_733799 baseEnd_733799 := by
    simpa [prefixWord, tailWord_733799, baseEnd_733799] using wordTrace_append hprefix tailTrace_733799
  have hstable : (prefixWord ++ tailWord_733799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733799).length < 2 ^ (prefixWord ++ tailWord_733799).sum := by decide
  have hdescent : baseEnd_733799 < baseStart_733799 := by decide
  rcases family_descends (prefixWord ++ tailWord_733799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733831 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 5]
def baseStart_733831 : Nat := 118140960795 + 733831 * 2 ^ 59
def prefixEnd_733831 : Nat := 4983230072969 + 3 ^ 40 * 733831 * 2
def baseEnd_733831 : Nat := 83735116037694137008373

theorem tailTrace_733831 : CollatzResearch.WordTrace tailWord_733831 prefixEnd_733831 83735116037694137008373 := by
  unfold tailWord_733831
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765015404463090202009347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17843343602975393468006231 26765015404463090202009347)
  ·
    refine ⟨40147523106694635303014021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26765015404463090202009347 40147523106694635303014021)
    ·
      refine ⟨7527660582505244119315129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40147523106694635303014021 7527660582505244119315129)
      ·
        refine ⟨5645745436878933089486347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7527660582505244119315129 5645745436878933089486347)
        ·
          refine ⟨8468618155318399634229521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645745436878933089486347 8468618155318399634229521)
          ·
            refine ⟨6351463616488799725672141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8468618155318399634229521 6351463616488799725672141)
            ·
              refine ⟨2381798856183299897127053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6351463616488799725672141 2381798856183299897127053)
              ·
                refine ⟨893174571068737461422645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2381798856183299897127053 893174571068737461422645)
                ·
                  refine ⟨83735116037694137008373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 893174571068737461422645 83735116037694137008373)
                  ·
                    rfl

theorem cell22_733831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 5].length) (baseStart_733831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733831 prefixEnd_733831 := by exact prefixLift 733831
  have htrace : WordTrace (prefixWord ++ tailWord_733831) baseStart_733831 baseEnd_733831 := by
    simpa [prefixWord, tailWord_733831, baseEnd_733831] using wordTrace_append hprefix tailTrace_733831
  have hstable : (prefixWord ++ tailWord_733831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733831).length < 2 ^ (prefixWord ++ tailWord_733831).sum := by decide
  have hdescent : baseEnd_733831 < baseStart_733831 := by decide
  rcases family_descends (prefixWord ++ tailWord_733831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733859 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 10]
def baseStart_733859 : Nat := 118140960795 + 733859 * 2 ^ 59
def prefixEnd_733859 : Nat := 4983230072969 + 3 ^ 40 * 733859 * 2
def baseEnd_733859 : Nat := 83738311028433223775011

theorem tailTrace_733859 : CollatzResearch.WordTrace tailWord_733859 prefixEnd_733859 83738311028433223775011 := by
  unfold tailWord_733859
  simp only [CollatzResearch.WordTrace]
  refine ⟨26766036648361650984028631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17844024432241100656019087 26766036648361650984028631)
  ·
    refine ⟨40149054972542476476042947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26766036648361650984028631 40149054972542476476042947)
    ·
      refine ⟨60223582458813714714064421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40149054972542476476042947 60223582458813714714064421)
      ·
        refine ⟨11291921711027571508887079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60223582458813714714064421 11291921711027571508887079)
        ·
          refine ⟨16937882566541357263330619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11291921711027571508887079 16937882566541357263330619)
          ·
            refine ⟨25406823849812035894995929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16937882566541357263330619 25406823849812035894995929)
            ·
              refine ⟨19055117887359026921246947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25406823849812035894995929 19055117887359026921246947)
              ·
                refine ⟨28582676831038540381870421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19055117887359026921246947 28582676831038540381870421)
                ·
                  refine ⟨83738311028433223775011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 28582676831038540381870421 83738311028433223775011)
                  ·
                    rfl

theorem cell22_733859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_733859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733859 prefixEnd_733859 := by exact prefixLift 733859
  have htrace : WordTrace (prefixWord ++ tailWord_733859) baseStart_733859 baseEnd_733859 := by
    simpa [prefixWord, tailWord_733859, baseEnd_733859] using wordTrace_append hprefix tailTrace_733859
  have hstable : (prefixWord ++ tailWord_733859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733859).length < 2 ^ (prefixWord ++ tailWord_733859).sum := by decide
  have hdescent : baseEnd_733859 < baseStart_733859 := by decide
  rcases family_descends (prefixWord ++ tailWord_733859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733869 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_733869 : Nat := 118140960795 + 733869 * 2 ^ 59
def prefixEnd_733869 : Nat := 4983230072969 + 3 ^ 40 * 733869 * 2
def baseEnd_733869 : Nat := 251218356289662978575003

theorem tailTrace_733869 : CollatzResearch.WordTrace tailWord_733869 prefixEnd_733869 251218356289662978575003 := by
  unfold tailWord_733869
  simp only [CollatzResearch.WordTrace]
  refine ⟨26766401378325422691892661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17844267585550281794595107 26766401378325422691892661)
  ·
    refine ⟨2509350129218008377364937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26766401378325422691892661 2509350129218008377364937)
    ·
      refine ⟨1882012596913506283023703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2509350129218008377364937 1882012596913506283023703)
      ·
        refine ⟨2823018895370259424535555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882012596913506283023703 2823018895370259424535555)
        ·
          refine ⟨4234528343055389136803333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823018895370259424535555 4234528343055389136803333)
          ·
            refine ⟨793974064322885463150625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4234528343055389136803333 793974064322885463150625)
            ·
              refine ⟨595480548242164097362969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793974064322885463150625 595480548242164097362969)
              ·
                refine ⟨446610411181623073022227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595480548242164097362969 446610411181623073022227)
                ·
                  refine ⟨669915616772434609533341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446610411181623073022227 669915616772434609533341)
                  ·
                    refine ⟨251218356289662978575003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669915616772434609533341 251218356289662978575003)
                    ·
                      rfl

theorem cell22_733869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_733869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733869 prefixEnd_733869 := by exact prefixLift 733869
  have htrace : WordTrace (prefixWord ++ tailWord_733869) baseStart_733869 baseEnd_733869 := by
    simpa [prefixWord, tailWord_733869, baseEnd_733869] using wordTrace_append hprefix tailTrace_733869
  have hstable : (prefixWord ++ tailWord_733869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733869).length < 2 ^ (prefixWord ++ tailWord_733869).sum := by decide
  have hdescent : baseEnd_733869 < baseStart_733869 := by decide
  rcases family_descends (prefixWord ++ tailWord_733869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733921 : List Nat := [1, 2, 3, 1, 4, 2, 9]
def baseStart_733921 : Nat := 118140960795 + 733921 * 2 ^ 59
def prefixEnd_733921 : Nat := 4983230072969 + 3 ^ 40 * 733921 * 2
def baseEnd_733921 : Nat := 9305042850087117639809

theorem tailTrace_733921 : CollatzResearch.WordTrace tailWord_733921 prefixEnd_733921 9305042850087117639809 := by
  unfold tailWord_733921
  simp only [CollatzResearch.WordTrace]
  refine ⟨26768297974137035572785617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17845531982758023715190411 26768297974137035572785617)
  ·
    refine ⟨20076223480602776679589213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26768297974137035572785617 20076223480602776679589213)
    ·
      refine ⟨7528583805226041254845955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20076223480602776679589213 7528583805226041254845955)
      ·
        refine ⟨11292875707839061882268933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7528583805226041254845955 11292875707839061882268933)
        ·
          refine ⟨2117414195219824102925425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11292875707839061882268933 2117414195219824102925425)
          ·
            refine ⟨1588060646414868077194069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117414195219824102925425 1588060646414868077194069)
            ·
              refine ⟨9305042850087117639809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1588060646414868077194069 9305042850087117639809)
              ·
                rfl

theorem cell22_733921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 9].length) (baseStart_733921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733921 prefixEnd_733921 := by exact prefixLift 733921
  have htrace : WordTrace (prefixWord ++ tailWord_733921) baseStart_733921 baseEnd_733921 := by
    simpa [prefixWord, tailWord_733921, baseEnd_733921] using wordTrace_append hprefix tailTrace_733921
  have hstable : (prefixWord ++ tailWord_733921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733921).length < 2 ^ (prefixWord ++ tailWord_733921).sum := by decide
  have hdescent : baseEnd_733921 < baseStart_733921 := by decide
  rcases family_descends (prefixWord ++ tailWord_733921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733925 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_733925 : Nat := 118140960795 + 733925 * 2 ^ 59
def prefixEnd_733925 : Nat := 4983230072969 + 3 ^ 40 * 733925 * 2
def baseEnd_733925 : Nat := 251237526234097499174831

theorem tailTrace_733925 : CollatzResearch.WordTrace tailWord_733925 prefixEnd_733925 251237526234097499174831 := by
  unfold tailWord_733925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26768443866122544255931229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17845629244081696170620819 26768443866122544255931229)
  ·
    refine ⟨10038166449795954095974211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26768443866122544255931229 10038166449795954095974211)
    ·
      refine ⟨15057249674693931143961317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038166449795954095974211 15057249674693931143961317)
      ·
        refine ⟨2823234314005112089492747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15057249674693931143961317 2823234314005112089492747)
        ·
          refine ⟨4234851471007668134239121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823234314005112089492747 4234851471007668134239121)
          ·
            refine ⟨3176138603255751100679341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234851471007668134239121 3176138603255751100679341)
            ·
              refine ⟨1191051976220906662754753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3176138603255751100679341 1191051976220906662754753)
              ·
                refine ⟨893288982165679997066065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191051976220906662754753 893288982165679997066065)
                ·
                  refine ⟨669966736624259997799549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893288982165679997066065 669966736624259997799549)
                  ·
                    refine ⟨251237526234097499174831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669966736624259997799549 251237526234097499174831)
                    ·
                      rfl

theorem cell22_733925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_733925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733925 prefixEnd_733925 := by exact prefixLift 733925
  have htrace : WordTrace (prefixWord ++ tailWord_733925) baseStart_733925 baseEnd_733925 := by
    simpa [prefixWord, tailWord_733925, baseEnd_733925] using wordTrace_append hprefix tailTrace_733925
  have hstable : (prefixWord ++ tailWord_733925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733925).length < 2 ^ (prefixWord ++ tailWord_733925).sum := by decide
  have hdescent : baseEnd_733925 < baseStart_733925 := by decide
  rcases family_descends (prefixWord ++ tailWord_733925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733942 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_733942 : Nat := 118140960795 + 733942 * 2 ^ 59
def prefixEnd_733942 : Nat := 4983230072969 + 3 ^ 40 * 733942 * 2
def baseEnd_733942 : Nat := 251243345681515121499779

theorem tailTrace_733942 : CollatzResearch.WordTrace tailWord_733942 prefixEnd_733942 251243345681515121499779 := by
  unfold tailWord_733942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673066494191309759956255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17846042604707304106200053 1673066494191309759956255)
  ·
    refine ⟨2509599741286964639934383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673066494191309759956255 2509599741286964639934383)
    ·
      refine ⟨3764399611930446959901575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2509599741286964639934383 3764399611930446959901575)
      ·
        refine ⟨5646599417895670439852363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764399611930446959901575 5646599417895670439852363)
        ·
          refine ⟨8469899126843505659778545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646599417895670439852363 8469899126843505659778545)
          ·
            refine ⟨6352424345132629244833909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8469899126843505659778545 6352424345132629244833909)
            ·
              refine ⟨595539782356183991703179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6352424345132629244833909 595539782356183991703179)
              ·
                refine ⟨893309673534275987554769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595539782356183991703179 893309673534275987554769)
                ·
                  refine ⟨669982255150706990666077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893309673534275987554769 669982255150706990666077)
                  ·
                    refine ⟨251243345681515121499779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669982255150706990666077 251243345681515121499779)
                    ·
                      rfl

theorem cell22_733942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_733942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_733942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_733942 prefixEnd_733942 := by exact prefixLift 733942
  have htrace : WordTrace (prefixWord ++ tailWord_733942) baseStart_733942 baseEnd_733942 := by
    simpa [prefixWord, tailWord_733942, baseEnd_733942] using wordTrace_append hprefix tailTrace_733942
  have hstable : (prefixWord ++ tailWord_733942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733942).length < 2 ^ (prefixWord ++ tailWord_733942).sum := by decide
  have hdescent : baseEnd_733942 < baseStart_733942 := by decide
  rcases family_descends (prefixWord ++ tailWord_733942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734060 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_734060 : Nat := 118140960795 + 734060 * 2 ^ 59
def prefixEnd_734060 : Nat := 4983230072969 + 3 ^ 40 * 734060 * 2
def baseEnd_734060 : Nat := 251283739493002147049417

theorem tailTrace_734060 : CollatzResearch.WordTrace tailWord_734060 prefixEnd_734060 251283739493002147049417 := by
  unfold tailWord_734060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386683860316731156047817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17848911813755641541397089 13386683860316731156047817)
  ·
    refine ⟨10040012895237548367035863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386683860316731156047817 10040012895237548367035863)
    ·
      refine ⟨15060019342856322550553795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040012895237548367035863 15060019342856322550553795)
      ·
        refine ⟨22590029014284483825830693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060019342856322550553795 22590029014284483825830693)
        ·
          refine ⟨4235630440178340717343255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22590029014284483825830693 4235630440178340717343255)
          ·
            refine ⟨6353445660267511076014883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235630440178340717343255 6353445660267511076014883)
            ·
              refine ⟨9530168490401266614022325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353445660267511076014883 9530168490401266614022325)
              ·
                refine ⟨893453295975118745064593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9530168490401266614022325 893453295975118745064593)
                ·
                  refine ⟨670089971981339058798445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893453295975118745064593 670089971981339058798445)
                  ·
                    refine ⟨251283739493002147049417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670089971981339058798445 251283739493002147049417)
                    ·
                      rfl

theorem cell22_734060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_734060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734060 prefixEnd_734060 := by exact prefixLift 734060
  have htrace : WordTrace (prefixWord ++ tailWord_734060) baseStart_734060 baseEnd_734060 := by
    simpa [prefixWord, tailWord_734060, baseEnd_734060] using wordTrace_append hprefix tailTrace_734060
  have hstable : (prefixWord ++ tailWord_734060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734060).length < 2 ^ (prefixWord ++ tailWord_734060).sum := by decide
  have hdescent : baseEnd_734060 < baseStart_734060 := by decide
  rcases family_descends (prefixWord ++ tailWord_734060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734242 : List Nat := [3, 3, 1, 1, 1, 4, 3, 6]
def baseStart_734242 : Nat := 118140960795 + 734242 * 2 ^ 59
def prefixEnd_734242 : Nat := 4983230072969 + 3 ^ 40 * 734242 * 2
def baseEnd_734242 : Nat := 27927337979157148777651

theorem tailTrace_734242 : CollatzResearch.WordTrace tailWord_734242 prefixEnd_734242 27927337979157148777651 := by
  unfold tailWord_734242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695001451493526848805245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17853337203982738263480653 6695001451493526848805245)
  ·
    refine ⟨2510625544310072568301967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6695001451493526848805245 2510625544310072568301967)
    ·
      refine ⟨3765938316465108852452951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510625544310072568301967 3765938316465108852452951)
      ·
        refine ⟨5648907474697663278679427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765938316465108852452951 5648907474697663278679427)
        ·
          refine ⟨8473361212046494918019141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648907474697663278679427 8473361212046494918019141)
          ·
            refine ⟨1588755227258717797128589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8473361212046494918019141 1588755227258717797128589)
            ·
              refine ⟨595783210222019173923221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1588755227258717797128589 595783210222019173923221)
              ·
                refine ⟨27927337979157148777651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 595783210222019173923221 27927337979157148777651)
                ·
                  rfl

theorem cell22_734242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_734242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734242 prefixEnd_734242 := by exact prefixLift 734242
  have htrace : WordTrace (prefixWord ++ tailWord_734242) baseStart_734242 baseEnd_734242 := by
    simpa [prefixWord, tailWord_734242, baseEnd_734242] using wordTrace_append hprefix tailTrace_734242
  have hstable : (prefixWord ++ tailWord_734242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734242).length < 2 ^ (prefixWord ++ tailWord_734242).sum := by decide
  have hdescent : baseEnd_734242 < baseStart_734242 := by decide
  rcases family_descends (prefixWord ++ tailWord_734242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734244 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_734244 : Nat := 118140960795 + 734244 * 2 ^ 59
def prefixEnd_734244 : Nat := 4983230072969 + 3 ^ 40 * 734244 * 2
def baseEnd_734244 : Nat := 251346726453287000448853

theorem tailTrace_734244 : CollatzResearch.WordTrace tailWord_734244 prefixEnd_734244 251346726453287000448853 := by
  unfold tailWord_734244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390039375983430868396893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17853385834644574491195857 13390039375983430868396893)
  ·
    refine ⟨5021264765993786575648835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13390039375983430868396893 5021264765993786575648835)
    ·
      refine ⟨7531897148990679863473253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5021264765993786575648835 7531897148990679863473253)
      ·
        refine ⟨1412230715435752474401235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7531897148990679863473253 1412230715435752474401235)
        ·
          refine ⟨2118346073153628711601853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412230715435752474401235 2118346073153628711601853)
          ·
            refine ⟨794379777432610766850695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2118346073153628711601853 794379777432610766850695)
            ·
              refine ⟨1191569666148916150276043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794379777432610766850695 1191569666148916150276043)
              ·
                refine ⟨1787354499223374225414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191569666148916150276043 1787354499223374225414065)
                ·
                  refine ⟨1340515874417530669060549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787354499223374225414065 1340515874417530669060549)
                  ·
                    refine ⟨251346726453287000448853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1340515874417530669060549 251346726453287000448853)
                    ·
                      rfl

theorem cell22_734244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_734244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734244 prefixEnd_734244 := by exact prefixLift 734244
  have htrace : WordTrace (prefixWord ++ tailWord_734244) baseStart_734244 baseEnd_734244 := by
    simpa [prefixWord, tailWord_734244, baseEnd_734244] using wordTrace_append hprefix tailTrace_734244
  have hstable : (prefixWord ++ tailWord_734244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734244).length < 2 ^ (prefixWord ++ tailWord_734244).sum := by decide
  have hdescent : baseEnd_734244 < baseStart_734244 := by decide
  rcases family_descends (prefixWord ++ tailWord_734244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734325 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_734325 : Nat := 118140960795 + 734325 * 2 ^ 59
def prefixEnd_734325 : Nat := 4983230072969 + 3 ^ 40 * 734325 * 2
def baseEnd_734325 : Nat := 251374454408629789173605

theorem tailTrace_734325 : CollatzResearch.WordTrace tailWord_734325 prefixEnd_734325 251374454408629789173605 := by
  unfold tailWord_734325
  simp only [CollatzResearch.WordTrace]
  refine ⟨26783033064673412570492429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17855355376448941713661619 26783033064673412570492429)
  ·
    refine ⟨10043637399252529713934661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26783033064673412570492429 10043637399252529713934661)
    ·
      refine ⟨1883182012359849321362749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10043637399252529713934661 1883182012359849321362749)
      ·
        refine ⟨706193254634943495511031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1883182012359849321362749 706193254634943495511031)
        ·
          refine ⟨1059289881952415243266547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706193254634943495511031 1059289881952415243266547)
          ·
            refine ⟨1588934822928622864899821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059289881952415243266547 1588934822928622864899821)
            ·
              refine ⟨595850558598233574337433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1588934822928622864899821 595850558598233574337433)
              ·
                refine ⟨446887918948675180753075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595850558598233574337433 446887918948675180753075)
                ·
                  refine ⟨670331878423012771129613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446887918948675180753075 670331878423012771129613)
                  ·
                    refine ⟨251374454408629789173605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670331878423012771129613 251374454408629789173605)
                    ·
                      rfl

theorem cell22_734325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_734325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734325 prefixEnd_734325 := by exact prefixLift 734325
  have htrace : WordTrace (prefixWord ++ tailWord_734325) baseStart_734325 baseEnd_734325 := by
    simpa [prefixWord, tailWord_734325, baseEnd_734325] using wordTrace_append hprefix tailTrace_734325
  have hstable : (prefixWord ++ tailWord_734325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734325).length < 2 ^ (prefixWord ++ tailWord_734325).sum := by decide
  have hdescent : baseEnd_734325 < baseStart_734325 := by decide
  rcases family_descends (prefixWord ++ tailWord_734325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734405 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 9]
def baseStart_734405 : Nat := 118140960795 + 734405 * 2 ^ 59
def prefixEnd_734405 : Nat := 4983230072969 + 3 ^ 40 * 734405 * 2
def baseEnd_734405 : Nat := 83800613347845415724453

theorem tailTrace_734405 : CollatzResearch.WordTrace tailWord_734405 prefixEnd_734405 83800613347845415724453 := by
  unfold tailWord_734405
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785950904383586233404669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17857300602922390822269779 26785950904383586233404669)
  ·
    refine ⟨10044731589143844837526751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26785950904383586233404669 10044731589143844837526751)
    ·
      refine ⟨15067097383715767256290127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10044731589143844837526751 15067097383715767256290127)
      ·
        refine ⟨22600646075573650884435191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15067097383715767256290127 22600646075573650884435191)
        ·
          refine ⟨33900969113360476326652787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22600646075573650884435191 33900969113360476326652787)
          ·
            refine ⟨50851453670040714489979181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33900969113360476326652787 50851453670040714489979181)
            ·
              refine ⟨19069295126265267933742193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50851453670040714489979181 19069295126265267933742193)
              ·
                refine ⟨14301971344698950950306645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19069295126265267933742193 14301971344698950950306645)
                ·
                  refine ⟨83800613347845415724453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14301971344698950950306645 83800613347845415724453)
                  ·
                    rfl

theorem cell22_734405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_734405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734405 prefixEnd_734405 := by exact prefixLift 734405
  have htrace : WordTrace (prefixWord ++ tailWord_734405) baseStart_734405 baseEnd_734405 := by
    simpa [prefixWord, tailWord_734405, baseEnd_734405] using wordTrace_append hprefix tailTrace_734405
  have hstable : (prefixWord ++ tailWord_734405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734405).length < 2 ^ (prefixWord ++ tailWord_734405).sum := by decide
  have hdescent : baseEnd_734405 < baseStart_734405 := by decide
  rcases family_descends (prefixWord ++ tailWord_734405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734439 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 7]
def baseStart_734439 : Nat := 118140960795 + 734439 * 2 ^ 59
def prefixEnd_734439 : Nat := 4983230072969 + 3 ^ 40 * 734439 * 2
def baseEnd_734439 : Nat := 83804492979457163941085

theorem tailTrace_734439 : CollatzResearch.WordTrace tailWord_734439 prefixEnd_734439 83804492979457163941085 := by
  unfold tailWord_734439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787190986260410040142371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17858127324173606693428247 26787190986260410040142371)
  ·
    refine ⟨40180786479390615060213557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26787190986260410040142371 40180786479390615060213557)
    ·
      refine ⟨3766948732442870161895021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40180786479390615060213557 3766948732442870161895021)
      ·
        refine ⟨1412605774666076310710633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3766948732442870161895021 1412605774666076310710633)
        ·
          refine ⟨1059454330999557233032975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412605774666076310710633 1059454330999557233032975)
          ·
            refine ⟨1589181496499335849549463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059454330999557233032975 1589181496499335849549463)
            ·
              refine ⟨2383772244749003774324195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589181496499335849549463 2383772244749003774324195)
              ·
                refine ⟨3575658367123505661486293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383772244749003774324195 3575658367123505661486293)
                ·
                  refine ⟨83804492979457163941085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3575658367123505661486293 83804492979457163941085)
                  ·
                    rfl

theorem cell22_734439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 7].length) (baseStart_734439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734439 prefixEnd_734439 := by exact prefixLift 734439
  have htrace : WordTrace (prefixWord ++ tailWord_734439) baseStart_734439 baseEnd_734439 := by
    simpa [prefixWord, tailWord_734439, baseEnd_734439] using wordTrace_append hprefix tailTrace_734439
  have hstable : (prefixWord ++ tailWord_734439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734439).length < 2 ^ (prefixWord ++ tailWord_734439).sum := by decide
  have hdescent : baseEnd_734439 < baseStart_734439 := by decide
  rcases family_descends (prefixWord ++ tailWord_734439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734467 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 6]
def baseStart_734467 : Nat := 118140960795 + 734467 * 2 ^ 59
def prefixEnd_734467 : Nat := 4983230072969 + 3 ^ 40 * 734467 * 2
def baseEnd_734467 : Nat := 83807687970196250707723

theorem tailTrace_734467 : CollatzResearch.WordTrace tailWord_734467 prefixEnd_734467 83807687970196250707723 := by
  unfold tailWord_734467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26788212230158970822161655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17858808153439313881441103 26788212230158970822161655)
  ·
    refine ⟨40182318345238456233242483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26788212230158970822161655 40182318345238456233242483)
    ·
      refine ⟨60273477517857684349863725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40182318345238456233242483 60273477517857684349863725)
      ·
        refine ⟨22602554069196631631198897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60273477517857684349863725 22602554069196631631198897)
        ·
          refine ⟨16951915551897473723399173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22602554069196631631198897 16951915551897473723399173)
          ·
            refine ⟨3178484165980776323137345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16951915551897473723399173 3178484165980776323137345)
            ·
              refine ⟨2383863124485582242353009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178484165980776323137345 2383863124485582242353009)
              ·
                refine ⟨1787897343364186681764757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383863124485582242353009 1787897343364186681764757)
                ·
                  refine ⟨83807687970196250707723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1787897343364186681764757 83807687970196250707723)
                  ·
                    rfl

theorem cell22_734467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_734467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734467 prefixEnd_734467 := by exact prefixLift 734467
  have htrace : WordTrace (prefixWord ++ tailWord_734467) baseStart_734467 baseEnd_734467 := by
    simpa [prefixWord, tailWord_734467, baseEnd_734467] using wordTrace_append hprefix tailTrace_734467
  have hstable : (prefixWord ++ tailWord_734467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734467).length < 2 ^ (prefixWord ++ tailWord_734467).sum := by decide
  have hdescent : baseEnd_734467 < baseStart_734467 := by decide
  rcases family_descends (prefixWord ++ tailWord_734467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734469 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_734469 : Nat := 118140960795 + 734469 * 2 ^ 59
def prefixEnd_734469 : Nat := 4983230072969 + 3 ^ 40 * 734469 * 2
def baseEnd_734469 : Nat := 251423748551461413573163

theorem tailTrace_734469 : CollatzResearch.WordTrace tailWord_734469 prefixEnd_734469 251423748551461413573163 := by
  unfold tailWord_734469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26788285176151725163734461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17858856784101150109156307 26788285176151725163734461)
  ·
    refine ⟨10045606941056896936400423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26788285176151725163734461 10045606941056896936400423)
    ·
      refine ⟨15068410411585345404600635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045606941056896936400423 15068410411585345404600635)
      ·
        refine ⟨22602615617378018106900953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068410411585345404600635 22602615617378018106900953)
        ·
          refine ⟨16951961713033513580175715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22602615617378018106900953 16951961713033513580175715)
          ·
            refine ⟨25427942569550270370263573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16951961713033513580175715 25427942569550270370263573)
            ·
              refine ⟨1191934807947668923606105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25427942569550270370263573 1191934807947668923606105)
              ·
                refine ⟨893951105960751692704579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191934807947668923606105 893951105960751692704579)
                ·
                  refine ⟨1340926658941127539056869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893951105960751692704579 1340926658941127539056869)
                  ·
                    refine ⟨251423748551461413573163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1340926658941127539056869 251423748551461413573163)
                    ·
                      rfl

theorem cell22_734469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_734469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734469 prefixEnd_734469 := by exact prefixLift 734469
  have htrace : WordTrace (prefixWord ++ tailWord_734469) baseStart_734469 baseEnd_734469 := by
    simpa [prefixWord, tailWord_734469, baseEnd_734469] using wordTrace_append hprefix tailTrace_734469
  have hstable : (prefixWord ++ tailWord_734469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734469).length < 2 ^ (prefixWord ++ tailWord_734469).sum := by decide
  have hdescent : baseEnd_734469 < baseStart_734469 := by decide
  rcases family_descends (prefixWord ++ tailWord_734469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734499 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 4, 3]
def baseStart_734499 : Nat := 118140960795 + 734499 * 2 ^ 59
def prefixEnd_734499 : Nat := 4983230072969 + 3 ^ 40 * 734499 * 2
def baseEnd_734499 : Nat := 251434018164551335323071

theorem tailTrace_734499 : CollatzResearch.WordTrace tailWord_734499 prefixEnd_734499 251434018164551335323071 := by
  unfold tailWord_734499
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789379366043040287326551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17859586244028693524884367 26789379366043040287326551)
  ·
    refine ⟨40184069049064560430989827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26789379366043040287326551 40184069049064560430989827)
    ·
      refine ⟨60276103573596840646484741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40184069049064560430989827 60276103573596840646484741)
      ·
        refine ⟨11301769420049407621215889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60276103573596840646484741 11301769420049407621215889)
        ·
          refine ⟨8476327065037055715911917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11301769420049407621215889 8476327065037055715911917)
          ·
            refine ⟨3178622649388895893466969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8476327065037055715911917 3178622649388895893466969)
            ·
              refine ⟨2383966987041671920100227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178622649388895893466969 2383966987041671920100227)
              ·
                refine ⟨3575950480562507880150341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383966987041671920100227 3575950480562507880150341)
                ·
                  refine ⟨670490715105470227528189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3575950480562507880150341 670490715105470227528189)
                  ·
                    refine ⟨251434018164551335323071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670490715105470227528189 251434018164551335323071)
                    ·
                      rfl

theorem cell22_734499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3].length) (baseStart_734499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734499 prefixEnd_734499 := by exact prefixLift 734499
  have htrace : WordTrace (prefixWord ++ tailWord_734499) baseStart_734499 baseEnd_734499 := by
    simpa [prefixWord, tailWord_734499, baseEnd_734499] using wordTrace_append hprefix tailTrace_734499
  have hstable : (prefixWord ++ tailWord_734499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734499).length < 2 ^ (prefixWord ++ tailWord_734499).sum := by decide
  have hdescent : baseEnd_734499 < baseStart_734499 := by decide
  rcases family_descends (prefixWord ++ tailWord_734499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734512 : List Nat := [2, 1, 1, 1, 2, 2, 6, 7]
def baseStart_734512 : Nat := 118140960795 + 734512 * 2 ^ 59
def prefixEnd_734512 : Nat := 4983230072969 + 3 ^ 40 * 734512 * 2
def baseEnd_734512 : Nat := 27937607592247070527559

theorem tailTrace_734512 : CollatzResearch.WordTrace tailWord_734512 prefixEnd_734512 27937607592247070527559 := by
  unfold tailWord_734512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394926757497971753774895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17859902343330629005033193 13394926757497971753774895)
  ·
    refine ⟨20092390136246957630662343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13394926757497971753774895 20092390136246957630662343)
    ·
      refine ⟨30138585204370436445993515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20092390136246957630662343 30138585204370436445993515)
      ·
        refine ⟨45207877806555654668990273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30138585204370436445993515 45207877806555654668990273)
        ·
          refine ⟨33905908354916741001742705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45207877806555654668990273 33905908354916741001742705)
          ·
            refine ⟨25429431266187555751307029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33905908354916741001742705 25429431266187555751307029)
            ·
              refine ⟨1192004590602541675842517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25429431266187555751307029 1192004590602541675842517)
              ·
                refine ⟨27937607592247070527559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1192004590602541675842517 27937607592247070527559)
                ·
                  rfl

theorem cell22_734512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_734512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734512 prefixEnd_734512 := by exact prefixLift 734512
  have htrace : WordTrace (prefixWord ++ tailWord_734512) baseStart_734512 baseEnd_734512 := by
    simpa [prefixWord, tailWord_734512, baseEnd_734512] using wordTrace_append hprefix tailTrace_734512
  have hstable : (prefixWord ++ tailWord_734512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734512).length < 2 ^ (prefixWord ++ tailWord_734512).sum := by decide
  have hdescent : baseEnd_734512 < baseStart_734512 := by decide
  rcases family_descends (prefixWord ++ tailWord_734512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734529 : List Nat := [1, 2, 5, 2, 1, 1, 2, 8]
def baseStart_734529 : Nat := 118140960795 + 734529 * 2 ^ 59
def prefixEnd_734529 : Nat := 4983230072969 + 3 ^ 40 * 734529 * 2
def baseEnd_734529 : Nat := 27938254197515695230331

theorem tailTrace_734529 : CollatzResearch.WordTrace tailWord_734529 prefixEnd_734529 27938254197515695230331 := by
  unfold tailWord_734529
  simp only [CollatzResearch.WordTrace]
  refine ⟨26790473555934355410918641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17860315703956236940612427 26790473555934355410918641)
  ·
    refine ⟨20092855166950766558188981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26790473555934355410918641 20092855166950766558188981)
    ·
      refine ⟨1883705171901634364830217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20092855166950766558188981 1883705171901634364830217)
      ·
        refine ⟨1412778878926225773622663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1883705171901634364830217 1412778878926225773622663)
        ·
          refine ⟨2119168318389338660433995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412778878926225773622663 2119168318389338660433995)
          ·
            refine ⟨3178752477584007990650993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119168318389338660433995 3178752477584007990650993)
            ·
              refine ⟨2384064358188005992988245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178752477584007990650993 2384064358188005992988245)
              ·
                refine ⟨27938254197515695230331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2384064358188005992988245 27938254197515695230331)
                ·
                  rfl

theorem cell22_734529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 8].length) (baseStart_734529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734529 prefixEnd_734529 := by exact prefixLift 734529
  have htrace : WordTrace (prefixWord ++ tailWord_734529) baseStart_734529 baseEnd_734529 := by
    simpa [prefixWord, tailWord_734529, baseEnd_734529] using wordTrace_append hprefix tailTrace_734529
  have hstable : (prefixWord ++ tailWord_734529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734529).length < 2 ^ (prefixWord ++ tailWord_734529).sum := by decide
  have hdescent : baseEnd_734529 < baseStart_734529 := by decide
  rcases family_descends (prefixWord ++ tailWord_734529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734666 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_734666 : Nat := 118140960795 + 734666 * 2 ^ 59
def prefixEnd_734666 : Nat := 4983230072969 + 3 ^ 40 * 734666 * 2
def baseEnd_734666 : Nat := 251491185677418566397559

theorem tailTrace_734666 : CollatzResearch.WordTrace tailWord_734666 prefixEnd_734666 251491185677418566397559 := by
  unfold tailWord_734666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698867589109506952163963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17863646904292018539103901 6698867589109506952163963)
  ·
    refine ⟨10048301383664260428245945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6698867589109506952163963 10048301383664260428245945)
    ·
      refine ⟨7536226037748195321184459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10048301383664260428245945 7536226037748195321184459)
      ·
        refine ⟨11304339056622292981776689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536226037748195321184459 11304339056622292981776689)
        ·
          refine ⟨8478254292466719736332517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11304339056622292981776689 8478254292466719736332517)
          ·
            refine ⟨1589672679837509950562347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8478254292466719736332517 1589672679837509950562347)
            ·
              refine ⟨2384509019756264925843521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589672679837509950562347 2384509019756264925843521)
              ·
                refine ⟨1788381764817198694382641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384509019756264925843521 1788381764817198694382641)
                ·
                  refine ⟨1341286323612899020786981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1788381764817198694382641 1341286323612899020786981)
                  ·
                    refine ⟨251491185677418566397559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1341286323612899020786981 251491185677418566397559)
                    ·
                      rfl

theorem cell22_734666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_734666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734666 prefixEnd_734666 := by exact prefixLift 734666
  have htrace : WordTrace (prefixWord ++ tailWord_734666) baseStart_734666 baseEnd_734666 := by
    simpa [prefixWord, tailWord_734666, baseEnd_734666] using wordTrace_append hprefix tailTrace_734666
  have hstable : (prefixWord ++ tailWord_734666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734666).length < 2 ^ (prefixWord ++ tailWord_734666).sum := by decide
  have hdescent : baseEnd_734666 < baseStart_734666 := by decide
  rcases family_descends (prefixWord ++ tailWord_734666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734685 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_734685 : Nat := 118140960795 + 734685 * 2 ^ 59
def prefixEnd_734685 : Nat := 4983230072969 + 3 ^ 40 * 734685 * 2
def baseEnd_734685 : Nat := 251497689765708850172501

theorem tailTrace_734685 : CollatzResearch.WordTrace tailWord_734685 prefixEnd_734685 251497689765708850172501 := by
  unfold tailWord_734685
  simp only [CollatzResearch.WordTrace]
  refine ⟨26796163343369194053597509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17864108895579462702398339 26796163343369194053597509)
  ·
    refine ⟨5024280626881723885049533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26796163343369194053597509 5024280626881723885049533)
    ·
      refine ⟨1884105235080646456893575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5024280626881723885049533 1884105235080646456893575)
      ·
        refine ⟨2826157852620969685340363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884105235080646456893575 2826157852620969685340363)
        ·
          refine ⟨4239236778931454528010545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826157852620969685340363 4239236778931454528010545)
          ·
            refine ⟨3179427584198590896007909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4239236778931454528010545 3179427584198590896007909)
            ·
              refine ⟨596142672037235793001483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3179427584198590896007909 596142672037235793001483)
              ·
                refine ⟨894214008055853689502225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596142672037235793001483 894214008055853689502225)
                ·
                  refine ⟨670660506041890267126669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894214008055853689502225 670660506041890267126669)
                  ·
                    refine ⟨251497689765708850172501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670660506041890267126669 251497689765708850172501)
                    ·
                      rfl

theorem cell22_734685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_734685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734685 prefixEnd_734685 := by exact prefixLift 734685
  have htrace : WordTrace (prefixWord ++ tailWord_734685) baseStart_734685 baseEnd_734685 := by
    simpa [prefixWord, tailWord_734685, baseEnd_734685] using wordTrace_append hprefix tailTrace_734685
  have hstable : (prefixWord ++ tailWord_734685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734685).length < 2 ^ (prefixWord ++ tailWord_734685).sum := by decide
  have hdescent : baseEnd_734685 < baseStart_734685 := by decide
  rcases family_descends (prefixWord ++ tailWord_734685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734696 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_734696 : Nat := 118140960795 + 734696 * 2 ^ 59
def prefixEnd_734696 : Nat := 4983230072969 + 3 ^ 40 * 734696 * 2
def baseEnd_734696 : Nat := 251501455290508488147467

theorem tailTrace_734696 : CollatzResearch.WordTrace tailWord_734696 prefixEnd_734696 251501455290508488147467 := by
  unfold tailWord_734696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398282273164671466123971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17864376364219561954831961 13398282273164671466123971)
  ·
    refine ⟨20097423409747007199185957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13398282273164671466123971 20097423409747007199185957)
    ·
      refine ⟨3768266889327563849847367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20097423409747007199185957 3768266889327563849847367)
      ·
        refine ⟨5652400333991345774771051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768266889327563849847367 5652400333991345774771051)
        ·
          refine ⟨8478600500987018662156577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652400333991345774771051 8478600500987018662156577)
          ·
            refine ⟨6358950375740263996617433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8478600500987018662156577 6358950375740263996617433)
            ·
              refine ⟨4769212781805197997463075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6358950375740263996617433 4769212781805197997463075)
              ·
                refine ⟨7153819172707796996194613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769212781805197997463075 7153819172707796996194613)
                ·
                  refine ⟨670670547441355968393245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7153819172707796996194613 670670547441355968393245)
                  ·
                    refine ⟨251501455290508488147467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670670547441355968393245 251501455290508488147467)
                    ·
                      rfl

theorem cell22_734696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_734696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734696 prefixEnd_734696 := by exact prefixLift 734696
  have htrace : WordTrace (prefixWord ++ tailWord_734696) baseStart_734696 baseEnd_734696 := by
    simpa [prefixWord, tailWord_734696, baseEnd_734696] using wordTrace_append hprefix tailTrace_734696
  have hstable : (prefixWord ++ tailWord_734696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734696).length < 2 ^ (prefixWord ++ tailWord_734696).sum := by decide
  have hdescent : baseEnd_734696 < baseStart_734696 := by decide
  rcases family_descends (prefixWord ++ tailWord_734696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734713 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 1, 3]
def baseStart_734713 : Nat := 118140960795 + 734713 * 2 ^ 59
def prefixEnd_734713 : Nat := 4983230072969 + 3 ^ 40 * 734713 * 2
def baseEnd_734713 : Nat := 251507274737926110472415

theorem tailTrace_734713 : CollatzResearch.WordTrace tailWord_734713 prefixEnd_734713 251507274737926110472415 := by
  unfold tailWord_734713
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797184587267754835616793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17864789724845169890411195 26797184587267754835616793)
  ·
    refine ⟨20097888440450816126712595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26797184587267754835616793 20097888440450816126712595)
    ·
      refine ⟨30146832660676224190068893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20097888440450816126712595 30146832660676224190068893)
      ·
        refine ⟨11305062247753584071275835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30146832660676224190068893 11305062247753584071275835)
        ·
          refine ⟨16957593371630376106913753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11305062247753584071275835 16957593371630376106913753)
          ·
            refine ⟨12718195028722782080185315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16957593371630376106913753 12718195028722782080185315)
            ·
              refine ⟨19077292543084173120277973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12718195028722782080185315 19077292543084173120277973)
              ·
                refine ⟨447124043978535307506515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19077292543084173120277973 447124043978535307506515)
                ·
                  refine ⟨670686065967802961259773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447124043978535307506515 670686065967802961259773)
                  ·
                    refine ⟨251507274737926110472415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670686065967802961259773 251507274737926110472415)
                    ·
                      rfl

theorem cell22_734713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_734713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734713 prefixEnd_734713 := by exact prefixLift 734713
  have htrace : WordTrace (prefixWord ++ tailWord_734713) baseStart_734713 baseEnd_734713 := by
    simpa [prefixWord, tailWord_734713, baseEnd_734713] using wordTrace_append hprefix tailTrace_734713
  have hstable : (prefixWord ++ tailWord_734713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734713).length < 2 ^ (prefixWord ++ tailWord_734713).sum := by decide
  have hdescent : baseEnd_734713 < baseStart_734713 := by decide
  rcases family_descends (prefixWord ++ tailWord_734713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734730 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_734730 : Nat := 118140960795 + 734730 * 2 ^ 59
def prefixEnd_734730 : Nat := 4983230072969 + 3 ^ 40 * 734730 * 2
def baseEnd_734730 : Nat := 251513094185343732797363

theorem tailTrace_734730 : CollatzResearch.WordTrace tailWord_734730 prefixEnd_734730 251513094185343732797363 := by
  unfold tailWord_734730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699451157051541684746411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17865203085470777825990429 6699451157051541684746411)
  ·
    refine ⟨10049176735577312527119617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6699451157051541684746411 10049176735577312527119617)
    ·
      refine ⟨7536882551682984395339713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10049176735577312527119617 7536882551682984395339713)
      ·
        refine ⟨5652661913762238296504785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7536882551682984395339713 5652661913762238296504785)
        ·
          refine ⟨4239496435321678722378589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5652661913762238296504785 4239496435321678722378589)
          ·
            refine ⟨1589811163245629520891971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4239496435321678722378589 1589811163245629520891971)
            ·
              refine ⟨2384716744868444281337957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589811163245629520891971 2384716744868444281337957)
              ·
                refine ⟨447134389662833302750867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2384716744868444281337957 447134389662833302750867)
                ·
                  refine ⟨670701584494249954126301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447134389662833302750867 670701584494249954126301)
                  ·
                    refine ⟨251513094185343732797363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670701584494249954126301 251513094185343732797363)
                    ·
                      rfl

theorem cell22_734730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_734730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734730 prefixEnd_734730 := by exact prefixLift 734730
  have htrace : WordTrace (prefixWord ++ tailWord_734730) baseStart_734730 baseEnd_734730 := by
    simpa [prefixWord, tailWord_734730, baseEnd_734730] using wordTrace_append hprefix tailTrace_734730
  have hstable : (prefixWord ++ tailWord_734730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734730).length < 2 ^ (prefixWord ++ tailWord_734730).sum := by decide
  have hdescent : baseEnd_734730 < baseStart_734730 := by decide
  rcases family_descends (prefixWord ++ tailWord_734730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734741 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_734741 : Nat := 118140960795 + 734741 * 2 ^ 59
def prefixEnd_734741 : Nat := 4983230072969 + 3 ^ 40 * 734741 * 2
def baseEnd_734741 : Nat := 251516859710143370772329

theorem tailTrace_734741 : CollatzResearch.WordTrace tailWord_734741 prefixEnd_734741 251516859710143370772329 := by
  unfold tailWord_734741
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798205831166315617636077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17865470554110877078424051 26798205831166315617636077)
  ·
    refine ⟨10049327186687368356613529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26798205831166315617636077 10049327186687368356613529)
    ·
      refine ⟨7536995390015526267460147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10049327186687368356613529 7536995390015526267460147)
      ·
        refine ⟨11305493085023289401190221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536995390015526267460147 11305493085023289401190221)
        ·
          refine ⟨4239559906883733525446333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11305493085023289401190221 4239559906883733525446333)
          ·
            refine ⟨1589834965081400072042375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4239559906883733525446333 1589834965081400072042375)
            ·
              refine ⟨2384752447622100108063563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589834965081400072042375 2384752447622100108063563)
              ·
                refine ⟨3577128671433150162095345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384752447622100108063563 3577128671433150162095345)
                ·
                  refine ⟨2682846503574862621571509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577128671433150162095345 2682846503574862621571509)
                  ·
                    refine ⟨251516859710143370772329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2682846503574862621571509 251516859710143370772329)
                    ·
                      rfl

theorem cell22_734741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_734741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734741 prefixEnd_734741 := by exact prefixLift 734741
  have htrace : WordTrace (prefixWord ++ tailWord_734741) baseStart_734741 baseEnd_734741 := by
    simpa [prefixWord, tailWord_734741, baseEnd_734741] using wordTrace_append hprefix tailTrace_734741
  have hstable : (prefixWord ++ tailWord_734741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734741).length < 2 ^ (prefixWord ++ tailWord_734741).sum := by decide
  have hdescent : baseEnd_734741 < baseStart_734741 := by decide
  rcases family_descends (prefixWord ++ tailWord_734741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734773 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_734773 : Nat := 118140960795 + 734773 * 2 ^ 59
def prefixEnd_734773 : Nat := 4983230072969 + 3 ^ 40 * 734773 * 2
def baseEnd_734773 : Nat := 251527813964105953972231

theorem tailTrace_734773 : CollatzResearch.WordTrace tailWord_734773 prefixEnd_734773 251527813964105953972231 := by
  unfold tailWord_734773
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799372967050385082800973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17866248644700256721867315 26799372967050385082800973)
  ·
    refine ⟨10049764862643894406050365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26799372967050385082800973 10049764862643894406050365)
    ·
      refine ⟨3768661823491460402268887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10049764862643894406050365 3768661823491460402268887)
      ·
        refine ⟨5652992735237190603403331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768661823491460402268887 5652992735237190603403331)
        ·
          refine ⟨8479489102855785905104997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652992735237190603403331 8479489102855785905104997)
          ·
            refine ⟨1589904206785459857207187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8479489102855785905104997 1589904206785459857207187)
            ·
              refine ⟨2384856310178189785810781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589904206785459857207187 2384856310178189785810781)
              ·
                refine ⟨894321116316821169679043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2384856310178189785810781 894321116316821169679043)
                ·
                  refine ⟨1341481674475231754518565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894321116316821169679043 1341481674475231754518565)
                  ·
                    refine ⟨251527813964105953972231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1341481674475231754518565 251527813964105953972231)
                    ·
                      rfl

theorem cell22_734773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_734773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734773 prefixEnd_734773 := by exact prefixLift 734773
  have htrace : WordTrace (prefixWord ++ tailWord_734773) baseStart_734773 baseEnd_734773 := by
    simpa [prefixWord, tailWord_734773, baseEnd_734773] using wordTrace_append hprefix tailTrace_734773
  have hstable : (prefixWord ++ tailWord_734773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734773).length < 2 ^ (prefixWord ++ tailWord_734773).sum := by decide
  have hdescent : baseEnd_734773 < baseStart_734773 := by decide
  rcases family_descends (prefixWord ++ tailWord_734773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734799 : List Nat := [1, 1, 2, 1, 1, 2, 3, 11]
def baseStart_734799 : Nat := 118140960795 + 734799 * 2 ^ 59
def prefixEnd_734799 : Nat := 4983230072969 + 3 ^ 40 * 734799 * 2
def baseEnd_734799 : Nat := 27948523810605616980239

theorem tailTrace_734799 : CollatzResearch.WordTrace tailWord_734799 prefixEnd_734799 27948523810605616980239 := by
  unfold tailWord_734799
  simp only [CollatzResearch.WordTrace]
  refine ⟨26800321264956191523247451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17866880843304127682164967 26800321264956191523247451)
  ·
    refine ⟨40200481897434287284871177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26800321264956191523247451 40200481897434287284871177)
    ·
      refine ⟨30150361423075715463653383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40200481897434287284871177 30150361423075715463653383)
      ·
        refine ⟨45225542134613573195480075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30150361423075715463653383 45225542134613573195480075)
        ·
          refine ⟨67838313201920359793220113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45225542134613573195480075 67838313201920359793220113)
          ·
            refine ⟨50878734901440269844915085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67838313201920359793220113 50878734901440269844915085)
            ·
              refine ⟨19079525588040101191843157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50878734901440269844915085 19079525588040101191843157)
              ·
                refine ⟨27948523810605616980239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 19079525588040101191843157 27948523810605616980239)
                ·
                  rfl

theorem cell22_734799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 11].length) (baseStart_734799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734799 prefixEnd_734799 := by exact prefixLift 734799
  have htrace : WordTrace (prefixWord ++ tailWord_734799) baseStart_734799 baseEnd_734799 := by
    simpa [prefixWord, tailWord_734799, baseEnd_734799] using wordTrace_append hprefix tailTrace_734799
  have hstable : (prefixWord ++ tailWord_734799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734799).length < 2 ^ (prefixWord ++ tailWord_734799).sum := by decide
  have hdescent : baseEnd_734799 < baseStart_734799 := by decide
  rcases family_descends (prefixWord ++ tailWord_734799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734893 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_734893 : Nat := 118140960795 + 734893 * 2 ^ 59
def prefixEnd_734893 : Nat := 4983230072969 + 3 ^ 40 * 734893 * 2
def baseEnd_734893 : Nat := 251568892416465640971863

theorem tailTrace_734893 : CollatzResearch.WordTrace tailWord_734893 prefixEnd_734893 251568892416465640971863 := by
  unfold tailWord_734893
  simp only [CollatzResearch.WordTrace]
  refine ⟨26803749726615645577169333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17869166484410430384779555 26803749726615645577169333)
  ·
    refine ⟨2512851536870216772859625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26803749726615645577169333 2512851536870216772859625)
    ·
      refine ⟨1884638652652662579644719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2512851536870216772859625 1884638652652662579644719)
      ·
        refine ⟨2826957978978993869467079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884638652652662579644719 2826957978978993869467079)
        ·
          refine ⟨4240436968468490804200619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826957978978993869467079 4240436968468490804200619)
          ·
            refine ⟨6360655452702736206300929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240436968468490804200619 6360655452702736206300929)
            ·
              refine ⟨4770491589527052154725697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6360655452702736206300929 4770491589527052154725697)
              ·
                refine ⟨3577868692145289116044273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770491589527052154725697 3577868692145289116044273)
                ·
                  refine ⟨2683401519108966837033205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577868692145289116044273 2683401519108966837033205)
                  ·
                    refine ⟨251568892416465640971863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2683401519108966837033205 251568892416465640971863)
                    ·
                      rfl

theorem cell22_734893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_734893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734893 prefixEnd_734893 := by exact prefixLift 734893
  have htrace : WordTrace (prefixWord ++ tailWord_734893) baseStart_734893 baseEnd_734893 := by
    simpa [prefixWord, tailWord_734893, baseEnd_734893] using wordTrace_append hprefix tailTrace_734893
  have hstable : (prefixWord ++ tailWord_734893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734893).length < 2 ^ (prefixWord ++ tailWord_734893).sum := by decide
  have hdescent : baseEnd_734893 < baseStart_734893 := by decide
  rcases family_descends (prefixWord ++ tailWord_734893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734908 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_734908 : Nat := 118140960795 + 734908 * 2 ^ 59
def prefixEnd_734908 : Nat := 4983230072969 + 3 ^ 40 * 734908 * 2
def baseEnd_734908 : Nat := 251574027223010601846817

theorem tailTrace_734908 : CollatzResearch.WordTrace tailWord_734908 prefixEnd_734908 251574027223010601846817 := by
  unfold tailWord_734908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13402148410780651569482689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17869531214374202092643585 13402148410780651569482689)
  ·
    refine ⟨10051611308085488677112017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13402148410780651569482689 10051611308085488677112017)
    ·
      refine ⟨7538708481064116507834013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10051611308085488677112017 7538708481064116507834013)
      ·
        refine ⟨2827015680399043690437755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7538708481064116507834013 2827015680399043690437755)
        ·
          refine ⟨4240523520598565535656633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827015680399043690437755 4240523520598565535656633)
          ·
            refine ⟨3180392640448924151742475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4240523520598565535656633 3180392640448924151742475)
            ·
              refine ⟨4770588960673386227613713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180392640448924151742475 4770588960673386227613713)
              ·
                refine ⟨3577941720505039670710285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770588960673386227613713 3577941720505039670710285)
                ·
                  refine ⟨1341728145189389876516357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3577941720505039670710285 1341728145189389876516357)
                  ·
                    refine ⟨251574027223010601846817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1341728145189389876516357 251574027223010601846817)
                    ·
                      rfl

theorem cell22_734908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_734908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734908 prefixEnd_734908 := by exact prefixLift 734908
  have htrace : WordTrace (prefixWord ++ tailWord_734908) baseStart_734908 baseEnd_734908 := by
    simpa [prefixWord, tailWord_734908, baseEnd_734908] using wordTrace_append hprefix tailTrace_734908
  have hstable : (prefixWord ++ tailWord_734908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734908).length < 2 ^ (prefixWord ++ tailWord_734908).sum := by decide
  have hdescent : baseEnd_734908 < baseStart_734908 := by decide
  rcases family_descends (prefixWord ++ tailWord_734908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734938 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_734938 : Nat := 118140960795 + 734938 * 2 ^ 59
def prefixEnd_734938 : Nat := 4983230072969 + 3 ^ 40 * 734938 * 2
def baseEnd_734938 : Nat := 251584296836100523596725

theorem tailTrace_734938 : CollatzResearch.WordTrace tailWord_734938 prefixEnd_734938 251584296836100523596725 := by
  unfold tailWord_734938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701347752863154565639367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17870260674301745508371645 6701347752863154565639367)
  ·
    refine ⟨10052021629294731848459051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701347752863154565639367 10052021629294731848459051)
    ·
      refine ⟨15078032443942097772688577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052021629294731848459051 15078032443942097772688577)
      ·
        refine ⟨11308524332956573329516433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15078032443942097772688577 11308524332956573329516433)
        ·
          refine ⟨8481393249717429997137325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11308524332956573329516433 8481393249717429997137325)
          ·
            refine ⟨3180522468644036248926497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8481393249717429997137325 3180522468644036248926497)
            ·
              refine ⟨2385391851483027186694873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180522468644036248926497 2385391851483027186694873)
              ·
                refine ⟨1789043888612270390021155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2385391851483027186694873 1789043888612270390021155)
                ·
                  refine ⟨2683565832918405585031733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789043888612270390021155 2683565832918405585031733)
                  ·
                    refine ⟨251584296836100523596725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2683565832918405585031733 251584296836100523596725)
                    ·
                      rfl

theorem cell22_734938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_734938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734938 prefixEnd_734938 := by exact prefixLift 734938
  have htrace : WordTrace (prefixWord ++ tailWord_734938) baseStart_734938 baseEnd_734938 := by
    simpa [prefixWord, tailWord_734938, baseEnd_734938] using wordTrace_append hprefix tailTrace_734938
  have hstable : (prefixWord ++ tailWord_734938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734938).length < 2 ^ (prefixWord ++ tailWord_734938).sum := by decide
  have hdescent : baseEnd_734938 < baseStart_734938 := by decide
  rcases family_descends (prefixWord ++ tailWord_734938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734955 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 2, 3]
def baseStart_734955 : Nat := 118140960795 + 734955 * 2 ^ 59
def prefixEnd_734955 : Nat := 4983230072969 + 3 ^ 40 * 734955 * 2
def baseEnd_734955 : Nat := 251590116283518145921673

theorem tailTrace_734955 : CollatzResearch.WordTrace tailWord_734955 prefixEnd_734955 251590116283518145921673 := by
  unfold tailWord_734955
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806011052391030165926319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17870674034927353443950879 26806011052391030165926319)
  ·
    refine ⟨40209016578586545248889479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26806011052391030165926319 40209016578586545248889479)
    ·
      refine ⟨60313524867879817873334219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40209016578586545248889479 60313524867879817873334219)
      ·
        refine ⟨90470287301819726810001329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60313524867879817873334219 90470287301819726810001329)
        ·
          refine ⟨67852715476364795107500997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90470287301819726810001329 67852715476364795107500997)
          ·
            refine ⟨12722384151818399082656437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67852715476364795107500997 12722384151818399082656437)
            ·
              refine ⟨1192723514232974913999041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12722384151818399082656437 1192723514232974913999041)
              ·
                refine ⟨894542635674731185499281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192723514232974913999041 894542635674731185499281)
                ·
                  refine ⟨670906976756048389124461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894542635674731185499281 670906976756048389124461)
                  ·
                    refine ⟨251590116283518145921673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670906976756048389124461 251590116283518145921673)
                    ·
                      rfl

theorem cell22_734955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3].length) (baseStart_734955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734955 prefixEnd_734955 := by exact prefixLift 734955
  have htrace : WordTrace (prefixWord ++ tailWord_734955) baseStart_734955 baseEnd_734955 := by
    simpa [prefixWord, tailWord_734955, baseEnd_734955] using wordTrace_append hprefix tailTrace_734955
  have hstable : (prefixWord ++ tailWord_734955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734955).length < 2 ^ (prefixWord ++ tailWord_734955).sum := by decide
  have hdescent : baseEnd_734955 < baseStart_734955 := by decide
  rcases family_descends (prefixWord ++ tailWord_734955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734972 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_734972 : Nat := 118140960795 + 734972 * 2 ^ 59
def prefixEnd_734972 : Nat := 4983230072969 + 3 ^ 40 * 734972 * 2
def baseEnd_734972 : Nat := 251595935730935768246621

theorem tailTrace_734972 : CollatzResearch.WordTrace tailWord_734972 prefixEnd_734972 251595935730935768246621 := by
  unfold tailWord_734972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403315546664721034647585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17871087395552961379530113 13403315546664721034647585)
  ·
    refine ⟨10052486659998540775985689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13403315546664721034647585 10052486659998540775985689)
    ·
      refine ⟨7539364994998905581989267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10052486659998540775985689 7539364994998905581989267)
      ·
        refine ⟨11309047492498358372983901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539364994998905581989267 11309047492498358372983901)
        ·
          refine ⟨4240892809686884389868963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11309047492498358372983901 4240892809686884389868963)
          ·
            refine ⟨6361339214530326584803445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240892809686884389868963 6361339214530326584803445)
            ·
              refine ⟨596375551362218117325323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6361339214530326584803445 596375551362218117325323)
              ·
                refine ⟨894563327043327175987985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596375551362218117325323 894563327043327175987985)
                ·
                  refine ⟨670922495282495381990989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894563327043327175987985 670922495282495381990989)
                  ·
                    refine ⟨251595935730935768246621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670922495282495381990989 251595935730935768246621)
                    ·
                      rfl

theorem cell22_734972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_734972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_734972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_734972 prefixEnd_734972 := by exact prefixLift 734972
  have htrace : WordTrace (prefixWord ++ tailWord_734972) baseStart_734972 baseEnd_734972 := by
    simpa [prefixWord, tailWord_734972, baseEnd_734972] using wordTrace_append hprefix tailTrace_734972
  have hstable : (prefixWord ++ tailWord_734972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734972).length < 2 ^ (prefixWord ++ tailWord_734972).sum := by decide
  have hdescent : baseEnd_734972 < baseStart_734972 := by decide
  rcases family_descends (prefixWord ++ tailWord_734972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735013 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 7]
def baseStart_735013 : Nat := 118140960795 + 735013 * 2 ^ 59
def prefixEnd_735013 : Nat := 4983230072969 + 3 ^ 40 * 735013 * 2
def baseEnd_735013 : Nat := 83869990289608442657165

theorem tailTrace_735013 : CollatzResearch.WordTrace tailWord_735013 prefixEnd_735013 83869990289608442657165 := by
  unfold tailWord_735013
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808126486180906071537693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17872084324120604047691795 26808126486180906071537693)
  ·
    refine ⟨10053047432317839776826635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26808126486180906071537693 10053047432317839776826635)
    ·
      refine ⟨15079571148476759665239953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053047432317839776826635 15079571148476759665239953)
      ·
        refine ⟨11309678361357569748929965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15079571148476759665239953 11309678361357569748929965)
        ·
          refine ⟨4241129385509088655848737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11309678361357569748929965 4241129385509088655848737)
          ·
            refine ⟨3180847039131816491886553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4241129385509088655848737 3180847039131816491886553)
            ·
              refine ⟨2385635279348862368914915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180847039131816491886553 2385635279348862368914915)
              ·
                refine ⟨3578452919023293553372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385635279348862368914915 3578452919023293553372373)
                ·
                  refine ⟨83869990289608442657165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3578452919023293553372373 83869990289608442657165)
                  ·
                    rfl

theorem cell22_735013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_735013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735013 prefixEnd_735013 := by exact prefixLift 735013
  have htrace : WordTrace (prefixWord ++ tailWord_735013) baseStart_735013 baseEnd_735013 := by
    simpa [prefixWord, tailWord_735013, baseEnd_735013] using wordTrace_append hprefix tailTrace_735013
  have hstable : (prefixWord ++ tailWord_735013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735013).length < 2 ^ (prefixWord ++ tailWord_735013).sum := by decide
  have hdescent : baseEnd_735013 < baseStart_735013 := by decide
  rcases family_descends (prefixWord ++ tailWord_735013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735068 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_735068 : Nat := 118140960795 + 735068 * 2 ^ 59
def prefixEnd_735068 : Nat := 4983230072969 + 3 ^ 40 * 735068 * 2
def baseEnd_735068 : Nat := 251628798492823517846327

theorem tailTrace_735068 : CollatzResearch.WordTrace tailWord_735068 prefixEnd_735068 251628798492823517846327 := by
  unfold tailWord_735068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405066250490825232394929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17873421667321100309859905 13405066250490825232394929)
  ·
    refine ⟨10053799687868118924296197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13405066250490825232394929 10053799687868118924296197)
    ·
      refine ⟨1885087441475272298305537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10053799687868118924296197 1885087441475272298305537)
      ·
        refine ⟨1413815581106454223729153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1885087441475272298305537 1413815581106454223729153)
        ·
          refine ⟨1060361685829840667796865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413815581106454223729153 1060361685829840667796865)
          ·
            refine ⟨795271264372380500847649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060361685829840667796865 795271264372380500847649)
            ·
              refine ⟨596453448279285375635737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795271264372380500847649 596453448279285375635737)
              ·
                refine ⟨447340086209464031726803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596453448279285375635737 447340086209464031726803)
                ·
                  refine ⟨671010129314196047590205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447340086209464031726803 671010129314196047590205)
                  ·
                    refine ⟨251628798492823517846327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671010129314196047590205 251628798492823517846327)
                    ·
                      rfl

theorem cell22_735068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_735068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735068 prefixEnd_735068 := by exact prefixLift 735068
  have htrace : WordTrace (prefixWord ++ tailWord_735068) baseStart_735068 baseEnd_735068 := by
    simpa [prefixWord, tailWord_735068, baseEnd_735068] using wordTrace_append hprefix tailTrace_735068
  have hstable : (prefixWord ++ tailWord_735068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735068).length < 2 ^ (prefixWord ++ tailWord_735068).sum := by decide
  have hdescent : baseEnd_735068 < baseStart_735068 := by decide
  rcases family_descends (prefixWord ++ tailWord_735068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735073 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_735073 : Nat := 118140960795 + 735073 * 2 ^ 59
def prefixEnd_735073 : Nat := 4983230072969 + 3 ^ 40 * 735073 * 2
def baseEnd_735073 : Nat := 251630510095005171471311

theorem tailTrace_735073 : CollatzResearch.WordTrace tailWord_735073 prefixEnd_735073 251630510095005171471311 := by
  unfold tailWord_735073
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810314865963536318721873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17873543243975690879147915 26810314865963536318721873)
  ·
    refine ⟨20107736149472652239041405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26810314865963536318721873 20107736149472652239041405)
    ·
      refine ⟨7540401056052244589640527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20107736149472652239041405 7540401056052244589640527)
      ·
        refine ⟨11310601584078366884460791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7540401056052244589640527 11310601584078366884460791)
        ·
          refine ⟨16965902376117550326691187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310601584078366884460791 16965902376117550326691187)
          ·
            refine ⟨25448853564176325490036781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965902376117550326691187 25448853564176325490036781)
            ·
              refine ⟨9543320086566122058763793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25448853564176325490036781 9543320086566122058763793)
              ·
                refine ⟨7157490064924591544072845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9543320086566122058763793 7157490064924591544072845)
                ·
                  refine ⟨2684058774346721829027317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7157490064924591544072845 2684058774346721829027317)
                  ·
                    refine ⟨251630510095005171471311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2684058774346721829027317 251630510095005171471311)
                    ·
                      rfl

theorem cell22_735073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_735073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735073 prefixEnd_735073 := by exact prefixLift 735073
  have htrace : WordTrace (prefixWord ++ tailWord_735073) baseStart_735073 baseEnd_735073 := by
    simpa [prefixWord, tailWord_735073, baseEnd_735073] using wordTrace_append hprefix tailTrace_735073
  have hstable : (prefixWord ++ tailWord_735073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735073).length < 2 ^ (prefixWord ++ tailWord_735073).sum := by decide
  have hdescent : baseEnd_735073 < baseStart_735073 := by decide
  rcases family_descends (prefixWord ++ tailWord_735073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735088 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_735088 : Nat := 118140960795 + 735088 * 2 ^ 59
def prefixEnd_735088 : Nat := 4983230072969 + 3 ^ 40 * 735088 * 2
def baseEnd_735088 : Nat := 251635644901550132346265

theorem tailTrace_735088 : CollatzResearch.WordTrace tailWord_735088 prefixEnd_735088 251635644901550132346265 := by
  unfold tailWord_735088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405430980454596940258959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17873907973939462587011945 13405430980454596940258959)
  ·
    refine ⟨20108146470681895410388439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13405430980454596940258959 20108146470681895410388439)
    ·
      refine ⟨30162219706022843115582659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20108146470681895410388439 30162219706022843115582659)
      ·
        refine ⟨45243329559034264673373989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30162219706022843115582659 45243329559034264673373989)
        ·
          refine ⟨8483124292318924626257623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45243329559034264673373989 8483124292318924626257623)
          ·
            refine ⟨12724686438478386939386435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483124292318924626257623 12724686438478386939386435)
            ·
              refine ⟨19087029657717580409079653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724686438478386939386435 19087029657717580409079653)
              ·
                refine ⟨3578818060822046326702435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19087029657717580409079653 3578818060822046326702435)
                ·
                  refine ⟨5368227091233069490053653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578818060822046326702435 5368227091233069490053653)
                  ·
                    refine ⟨251635644901550132346265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5368227091233069490053653 251635644901550132346265)
                    ·
                      rfl

theorem cell22_735088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_735088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735088 prefixEnd_735088 := by exact prefixLift 735088
  have htrace : WordTrace (prefixWord ++ tailWord_735088) baseStart_735088 baseEnd_735088 := by
    simpa [prefixWord, tailWord_735088, baseEnd_735088] using wordTrace_append hprefix tailTrace_735088
  have hstable : (prefixWord ++ tailWord_735088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735088).length < 2 ^ (prefixWord ++ tailWord_735088).sum := by decide
  have hdescent : baseEnd_735088 < baseStart_735088 := by decide
  rcases family_descends (prefixWord ++ tailWord_735088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735090 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_735090 : Nat := 118140960795 + 735090 * 2 ^ 59
def prefixEnd_735090 : Nat := 4983230072969 + 3 ^ 40 * 735090 * 2
def baseEnd_735090 : Nat := 251636329542422793796259

theorem tailTrace_735090 : CollatzResearch.WordTrace tailWord_735090 prefixEnd_735090 251636329542422793796259 := by
  unfold tailWord_735090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702733726725487055522681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17873956604601298814727149 6702733726725487055522681)
  ·
    refine ⟨5027050295044115291642011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6702733726725487055522681 5027050295044115291642011)
    ·
      refine ⟨7540575442566172937463017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5027050295044115291642011 7540575442566172937463017)
      ·
        refine ⟨5655431581924629703097263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7540575442566172937463017 5655431581924629703097263)
        ·
          refine ⟨8483147372886944554645895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655431581924629703097263 8483147372886944554645895)
          ·
            refine ⟨12724721059330416831968843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483147372886944554645895 12724721059330416831968843)
            ·
              refine ⟨19087081588995625247953265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724721059330416831968843 19087081588995625247953265)
              ·
                refine ⟨14315311191746718935964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19087081588995625247953265 14315311191746718935964949)
                ·
                  refine ⟨671030212113127450123357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14315311191746718935964949 671030212113127450123357)
                  ·
                    refine ⟨251636329542422793796259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671030212113127450123357 251636329542422793796259)
                    ·
                      rfl

theorem cell22_735090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_735090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735090 prefixEnd_735090 := by exact prefixLift 735090
  have htrace : WordTrace (prefixWord ++ tailWord_735090) baseStart_735090 baseEnd_735090 := by
    simpa [prefixWord, tailWord_735090, baseEnd_735090] using wordTrace_append hprefix tailTrace_735090
  have hstable : (prefixWord ++ tailWord_735090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735090).length < 2 ^ (prefixWord ++ tailWord_735090).sum := by decide
  have hdescent : baseEnd_735090 < baseStart_735090 := by decide
  rcases family_descends (prefixWord ++ tailWord_735090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735111 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 1, 4]
def baseStart_735111 : Nat := 118140960795 + 735111 * 2 ^ 59
def prefixEnd_735111 : Nat := 4983230072969 + 3 ^ 40 * 735111 * 2
def baseEnd_735111 : Nat := 251643518271585739021195

theorem tailTrace_735111 : CollatzResearch.WordTrace tailWord_735111 prefixEnd_735111 251643518271585739021195 := by
  unfold tailWord_735111
  simp only [CollatzResearch.WordTrace]
  refine ⟨26811700839825868808605187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17874467226550579205736791 26811700839825868808605187)
  ·
    refine ⟨40217551259738803212907781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26811700839825868808605187 40217551259738803212907781)
    ·
      refine ⟨7540790861201025602420209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40217551259738803212907781 7540790861201025602420209)
      ·
        refine ⟨5655593145900769201815157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7540790861201025602420209 5655593145900769201815157)
        ·
          refine ⟨530211857428197112670171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5655593145900769201815157 530211857428197112670171)
          ·
            refine ⟨795317786142295669005257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530211857428197112670171 795317786142295669005257)
            ·
              refine ⟨596488339606721751753943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795317786142295669005257 596488339606721751753943)
              ·
                refine ⟨894732509410082627630915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596488339606721751753943 894732509410082627630915)
                ·
                  refine ⟨1342098764115123941446373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894732509410082627630915 1342098764115123941446373)
                  ·
                    refine ⟨251643518271585739021195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1342098764115123941446373 251643518271585739021195)
                    ·
                      rfl

theorem cell22_735111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_735111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735111 prefixEnd_735111 := by exact prefixLift 735111
  have htrace : WordTrace (prefixWord ++ tailWord_735111) baseStart_735111 baseEnd_735111 := by
    simpa [prefixWord, tailWord_735111, baseEnd_735111] using wordTrace_append hprefix tailTrace_735111
  have hstable : (prefixWord ++ tailWord_735111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735111).length < 2 ^ (prefixWord ++ tailWord_735111).sum := by decide
  have hdescent : baseEnd_735111 < baseStart_735111 := by decide
  rcases family_descends (prefixWord ++ tailWord_735111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735124 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_735124 : Nat := 118140960795 + 735124 * 2 ^ 59
def prefixEnd_735124 : Nat := 4983230072969 + 3 ^ 40 * 735124 * 2
def baseEnd_735124 : Nat := 251647968437258038446155

theorem tailTrace_735124 : CollatzResearch.WordTrace tailWord_735124 prefixEnd_735124 251647968437258038446155 := by
  unfold tailWord_735124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406087494389386014414213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17874783325852514685885617 13406087494389386014414213)
  ·
    refine ⟨2513641405198009877702665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13406087494389386014414213 2513641405198009877702665)
    ·
      refine ⟨1885231053898507408276999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2513641405198009877702665 1885231053898507408276999)
      ·
        refine ⟨2827846580847761112415499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885231053898507408276999 2827846580847761112415499)
        ·
          refine ⟨4241769871271641668623249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827846580847761112415499 4241769871271641668623249)
          ·
            refine ⟨3181327403453731251467437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4241769871271641668623249 3181327403453731251467437)
            ·
              refine ⟨1192997776295149219300289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3181327403453731251467437 1192997776295149219300289)
              ·
                refine ⟨894748332221361914475217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192997776295149219300289 894748332221361914475217)
                ·
                  refine ⟨671061249166021435856413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894748332221361914475217 671061249166021435856413)
                  ·
                    refine ⟨251647968437258038446155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671061249166021435856413 251647968437258038446155)
                    ·
                      rfl

theorem cell22_735124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_735124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735124 prefixEnd_735124 := by exact prefixLift 735124
  have htrace : WordTrace (prefixWord ++ tailWord_735124) baseStart_735124 baseEnd_735124 := by
    simpa [prefixWord, tailWord_735124, baseEnd_735124] using wordTrace_append hprefix tailTrace_735124
  have hstable : (prefixWord ++ tailWord_735124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735124).length < 2 ^ (prefixWord ++ tailWord_735124).sum := by decide
  have hdescent : baseEnd_735124 < baseStart_735124 := by decide
  rcases family_descends (prefixWord ++ tailWord_735124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735126 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_735126 : Nat := 118140960795 + 735126 * 2 ^ 59
def prefixEnd_735126 : Nat := 4983230072969 + 3 ^ 40 * 735126 * 2
def baseEnd_735126 : Nat := 83882884359376899965383

theorem tailTrace_735126 : CollatzResearch.WordTrace tailWord_735126 prefixEnd_735126 83882884359376899965383 := by
  unfold tailWord_735126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675765495923220398150077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17874831956514350913600821 1675765495923220398150077)
  ·
    refine ⟨628412060971207649306279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1675765495923220398150077 628412060971207649306279)
    ·
      refine ⟨942618091456811473959419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628412060971207649306279 942618091456811473959419)
      ·
        refine ⟨1413927137185217210939129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942618091456811473959419 1413927137185217210939129)
        ·
          refine ⟨1060445352888912908204347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413927137185217210939129 1060445352888912908204347)
          ·
            refine ⟨1590668029333369362306521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060445352888912908204347 1590668029333369362306521)
            ·
              refine ⟨1193001022000027021729891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590668029333369362306521 1193001022000027021729891)
              ·
                refine ⟨1789501533000040532594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193001022000027021729891 1789501533000040532594837)
                ·
                  refine ⟨83882884359376899965383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1789501533000040532594837 83882884359376899965383)
                  ·
                    rfl

theorem cell22_735126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_735126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735126 prefixEnd_735126 := by exact prefixLift 735126
  have htrace : WordTrace (prefixWord ++ tailWord_735126) baseStart_735126 baseEnd_735126 := by
    simpa [prefixWord, tailWord_735126, baseEnd_735126] using wordTrace_append hprefix tailTrace_735126
  have hstable : (prefixWord ++ tailWord_735126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735126).length < 2 ^ (prefixWord ++ tailWord_735126).sum := by decide
  have hdescent : baseEnd_735126 < baseStart_735126 := by decide
  rcases family_descends (prefixWord ++ tailWord_735126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735148 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_735148 : Nat := 118140960795 + 735148 * 2 ^ 59
def prefixEnd_735148 : Nat := 4983230072969 + 3 ^ 40 * 735148 * 2
def baseEnd_735148 : Nat := 83885394709243325282027

theorem tailTrace_735148 : CollatzResearch.WordTrace tailWord_735148 prefixEnd_735148 83885394709243325282027 := by
  unfold tailWord_735148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406525170345912063851049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17875366893794549418468065 13406525170345912063851049)
  ·
    refine ⟨10054893877759434047888287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13406525170345912063851049 10054893877759434047888287)
    ·
      refine ⟨15082340816639151071832431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054893877759434047888287 15082340816639151071832431)
      ·
        refine ⟨22623511224958726607748647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15082340816639151071832431 22623511224958726607748647)
        ·
          refine ⟨33935266837438089911622971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22623511224958726607748647 33935266837438089911622971)
          ·
            refine ⟨50902900256157134867434457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33935266837438089911622971 50902900256157134867434457)
            ·
              refine ⟨38177175192117851150575843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50902900256157134867434457 38177175192117851150575843)
              ·
                refine ⟨57265762788176776725863765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38177175192117851150575843 57265762788176776725863765)
                ·
                  refine ⟨83885394709243325282027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 57265762788176776725863765 83885394709243325282027)
                  ·
                    rfl

theorem cell22_735148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_735148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735148 prefixEnd_735148 := by exact prefixLift 735148
  have htrace : WordTrace (prefixWord ++ tailWord_735148) baseStart_735148 baseEnd_735148 := by
    simpa [prefixWord, tailWord_735148, baseEnd_735148] using wordTrace_append hprefix tailTrace_735148
  have hstable : (prefixWord ++ tailWord_735148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735148).length < 2 ^ (prefixWord ++ tailWord_735148).sum := by decide
  have hdescent : baseEnd_735148 < baseStart_735148 := by decide
  rcases family_descends (prefixWord ++ tailWord_735148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735163 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_735163 : Nat := 118140960795 + 735163 * 2 ^ 59
def prefixEnd_735163 : Nat := 4983230072969 + 3 ^ 40 * 735163 * 2
def baseEnd_735163 : Nat := 251661318934274936721035

theorem tailTrace_735163 : CollatzResearch.WordTrace tailWord_735163 prefixEnd_735163 251661318934274936721035 := by
  unfold tailWord_735163
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813597435637481689498143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875731623758321126332095 26813597435637481689498143)
  ·
    refine ⟨40220396153456222534247215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26813597435637481689498143 40220396153456222534247215)
    ·
      refine ⟨60330594230184333801370823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40220396153456222534247215 60330594230184333801370823)
      ·
        refine ⟨90495891345276500702056235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60330594230184333801370823 90495891345276500702056235)
        ·
          refine ⟨135743837017914751053084353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90495891345276500702056235 135743837017914751053084353)
          ·
            refine ⟨101807877763436063289813265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135743837017914751053084353 101807877763436063289813265)
            ·
              refine ⟨76355908322577047467359949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101807877763436063289813265 76355908322577047467359949)
              ·
                refine ⟨28633465620966392800259981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76355908322577047467359949 28633465620966392800259981)
                ·
                  refine ⟨10737549607862397300097493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28633465620966392800259981 10737549607862397300097493)
                  ·
                    refine ⟨251661318934274936721035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10737549607862397300097493 251661318934274936721035)
                    ·
                      rfl

theorem cell22_735163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_735163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735163 prefixEnd_735163 := by exact prefixLift 735163
  have htrace : WordTrace (prefixWord ++ tailWord_735163) baseStart_735163 baseEnd_735163 := by
    simpa [prefixWord, tailWord_735163, baseEnd_735163] using wordTrace_append hprefix tailTrace_735163
  have hstable : (prefixWord ++ tailWord_735163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735163).length < 2 ^ (prefixWord ++ tailWord_735163).sum := by decide
  have hdescent : baseEnd_735163 < baseStart_735163 := by decide
  rcases family_descends (prefixWord ++ tailWord_735163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735165 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 7]
def baseStart_735165 : Nat := 118140960795 + 735165 * 2 ^ 59
def prefixEnd_735165 : Nat := 4983230072969 + 3 ^ 40 * 735165 * 2
def baseEnd_735165 : Nat := 83887334525049199390343

theorem tailTrace_735165 : CollatzResearch.WordTrace tailWord_735165 prefixEnd_735165 83887334525049199390343 := by
  unfold tailWord_735165
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813670381630236031070949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875780254420157354047299 26813670381630236031070949)
  ·
    refine ⟨5027563196555669255825803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26813670381630236031070949 5027563196555669255825803)
    ·
      refine ⟨7541344794833503883738705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5027563196555669255825803 7541344794833503883738705)
      ·
        refine ⟨5656008596125127912804029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7541344794833503883738705 5656008596125127912804029)
        ·
          refine ⟨2121003223546922967301511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5656008596125127912804029 2121003223546922967301511)
          ·
            refine ⟨3181504835320384450952267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121003223546922967301511 3181504835320384450952267)
            ·
              refine ⟨4772257252980576676428401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181504835320384450952267 4772257252980576676428401)
              ·
                refine ⟨3579192939735432507321301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772257252980576676428401 3579192939735432507321301)
                ·
                  refine ⟨83887334525049199390343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3579192939735432507321301 83887334525049199390343)
                  ·
                    rfl

theorem cell22_735165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_735165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735165 prefixEnd_735165 := by exact prefixLift 735165
  have htrace : WordTrace (prefixWord ++ tailWord_735165) baseStart_735165 baseEnd_735165 := by
    simpa [prefixWord, tailWord_735165, baseEnd_735165] using wordTrace_append hprefix tailTrace_735165
  have hstable : (prefixWord ++ tailWord_735165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735165).length < 2 ^ (prefixWord ++ tailWord_735165).sum := by decide
  have hdescent : baseEnd_735165 < baseStart_735165 := by decide
  rcases family_descends (prefixWord ++ tailWord_735165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735186 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_735186 : Nat := 118140960795 + 735186 * 2 ^ 59
def prefixEnd_735186 : Nat := 4983230072969 + 3 ^ 40 * 735186 * 2
def baseEnd_735186 : Nat := 251669192304310543395965

theorem tailTrace_735186 : CollatzResearch.WordTrace tailWord_735186 prefixEnd_735186 251669192304310543395965 := by
  unfold tailWord_735186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703609078638539154396353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17876290876369437745056941 6703609078638539154396353)
  ·
    refine ⟨5027706808978904365797265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6703609078638539154396353 5027706808978904365797265)
    ·
      refine ⟨3770780106734178274347949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027706808978904365797265 3770780106734178274347949)
      ·
        refine ⟨1414042540025316852880481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3770780106734178274347949 1414042540025316852880481)
        ·
          refine ⟨1060531905018987639660361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414042540025316852880481 1060531905018987639660361)
          ·
            refine ⟨795398928764240729745271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060531905018987639660361 795398928764240729745271)
            ·
              refine ⟨1193098393146361094617907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795398928764240729745271 1193098393146361094617907)
              ·
                refine ⟨1789647589719541641926861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193098393146361094617907 1789647589719541641926861)
                ·
                  refine ⟨671117846144828115722573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1789647589719541641926861 671117846144828115722573)
                  ·
                    refine ⟨251669192304310543395965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671117846144828115722573 251669192304310543395965)
                    ·
                      rfl

theorem cell22_735186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_735186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735186 prefixEnd_735186 := by exact prefixLift 735186
  have htrace : WordTrace (prefixWord ++ tailWord_735186) baseStart_735186 baseEnd_735186 := by
    simpa [prefixWord, tailWord_735186, baseEnd_735186] using wordTrace_append hprefix tailTrace_735186
  have hstable : (prefixWord ++ tailWord_735186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735186).length < 2 ^ (prefixWord ++ tailWord_735186).sum := by decide
  have hdescent : baseEnd_735186 < baseStart_735186 := by decide
  rcases family_descends (prefixWord ++ tailWord_735186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735199 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 5]
def baseStart_735199 : Nat := 118140960795 + 735199 * 2 ^ 59
def prefixEnd_735199 : Nat := 4983230072969 + 3 ^ 40 * 735199 * 2
def baseEnd_735199 : Nat := 83891214156660947606975

theorem tailTrace_735199 : CollatzResearch.WordTrace tailWord_735199 prefixEnd_735199 83891214156660947606975 := by
  unfold tailWord_735199
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814910463507059837808651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17876606975671373225205767 26814910463507059837808651)
  ·
    refine ⟨40222365695260589756712977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26814910463507059837808651 40222365695260589756712977)
    ·
      refine ⟨30166774271445442317534733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40222365695260589756712977 30166774271445442317534733)
      ·
        refine ⟨11312540351792040869075525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30166774271445442317534733 11312540351792040869075525)
        ·
          refine ⟨2121101315961007662951661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11312540351792040869075525 2121101315961007662951661)
          ·
            refine ⟨795412993485377873606873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2121101315961007662951661 795412993485377873606873)
            ·
              refine ⟨596559745114033405205155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795412993485377873606873 596559745114033405205155)
              ·
                refine ⟨894839617671050107807733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596559745114033405205155 894839617671050107807733)
                ·
                  refine ⟨83891214156660947606975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 894839617671050107807733 83891214156660947606975)
                  ·
                    rfl

theorem cell22_735199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 5].length) (baseStart_735199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735199 prefixEnd_735199 := by exact prefixLift 735199
  have htrace : WordTrace (prefixWord ++ tailWord_735199) baseStart_735199 baseEnd_735199 := by
    simpa [prefixWord, tailWord_735199, baseEnd_735199] using wordTrace_append hprefix tailTrace_735199
  have hstable : (prefixWord ++ tailWord_735199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735199).length < 2 ^ (prefixWord ++ tailWord_735199).sum := by decide
  have hdescent : baseEnd_735199 < baseStart_735199 := by decide
  rcases family_descends (prefixWord ++ tailWord_735199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735210 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_735210 : Nat := 118140960795 + 735210 * 2 ^ 59
def prefixEnd_735210 : Nat := 4983230072969 + 3 ^ 40 * 735210 * 2
def baseEnd_735210 : Nat := 83892469331594160265297

theorem tailTrace_735210 : CollatzResearch.WordTrace tailWord_735210 prefixEnd_735210 83892469331594160265297 := by
  unfold tailWord_735210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703827916616802179114771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17876874444311472477639389 6703827916616802179114771)
  ·
    refine ⟨10055741874925203268672157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6703827916616802179114771 10055741874925203268672157)
    ·
      refine ⟨3770903203096951225752059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10055741874925203268672157 3770903203096951225752059)
      ·
        refine ⟨5656354804645426838628089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770903203096951225752059 5656354804645426838628089)
        ·
          refine ⟨4242266103484070128971067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656354804645426838628089 4242266103484070128971067)
          ·
            refine ⟨6363399155226105193456601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242266103484070128971067 6363399155226105193456601)
            ·
              refine ⟨4772549366419578895092451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6363399155226105193456601 4772549366419578895092451)
              ·
                refine ⟨7158824049629368342638677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772549366419578895092451 7158824049629368342638677)
                ·
                  refine ⟨83892469331594160265297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7158824049629368342638677 83892469331594160265297)
                  ·
                    rfl

theorem cell22_735210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_735210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735210 prefixEnd_735210 := by exact prefixLift 735210
  have htrace : WordTrace (prefixWord ++ tailWord_735210) baseStart_735210 baseEnd_735210 := by
    simpa [prefixWord, tailWord_735210, baseEnd_735210] using wordTrace_append hprefix tailTrace_735210
  have hstable : (prefixWord ++ tailWord_735210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735210).length < 2 ^ (prefixWord ++ tailWord_735210).sum := by decide
  have hdescent : baseEnd_735210 < baseStart_735210 := by decide
  rcases family_descends (prefixWord ++ tailWord_735210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735225 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_735225 : Nat := 118140960795 + 735225 * 2 ^ 59
def prefixEnd_735225 : Nat := 4983230072969 + 3 ^ 40 * 735225 * 2
def baseEnd_735225 : Nat := 251682542801327441670845

theorem tailTrace_735225 : CollatzResearch.WordTrace tailWord_735225 prefixEnd_735225 251682542801327441670845 := by
  unfold tailWord_735225
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815858761412866278255129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17877239174275244185503419 26815858761412866278255129)
  ·
    refine ⟨20111894071059649708691347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26815858761412866278255129 20111894071059649708691347)
    ·
      refine ⟨30167841106589474563037021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20111894071059649708691347 30167841106589474563037021)
      ·
        refine ⟨11312940414971052961138883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30167841106589474563037021 11312940414971052961138883)
        ·
          refine ⟨16969410622456579441708325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11312940414971052961138883 16969410622456579441708325)
          ·
            refine ⟨3181764491710608645320311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16969410622456579441708325 3181764491710608645320311)
            ·
              refine ⟨4772646737565912967980467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181764491710608645320311 4772646737565912967980467)
              ·
                refine ⟨7158970106348869451970701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772646737565912967980467 7158970106348869451970701)
                ·
                  refine ⟨2684613789880826044489013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7158970106348869451970701 2684613789880826044489013)
                  ·
                    refine ⟨251682542801327441670845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2684613789880826044489013 251682542801327441670845)
                    ·
                      rfl

theorem cell22_735225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_735225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735225 prefixEnd_735225 := by exact prefixLift 735225
  have htrace : WordTrace (prefixWord ++ tailWord_735225) baseStart_735225 baseEnd_735225 := by
    simpa [prefixWord, tailWord_735225, baseEnd_735225] using wordTrace_append hprefix tailTrace_735225
  have hstable : (prefixWord ++ tailWord_735225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735225).length < 2 ^ (prefixWord ++ tailWord_735225).sum := by decide
  have hdescent : baseEnd_735225 < baseStart_735225 := by decide
  rcases family_descends (prefixWord ++ tailWord_735225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735274 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_735274 : Nat := 118140960795 + 735274 * 2 ^ 59
def prefixEnd_735274 : Nat := 4983230072969 + 3 ^ 40 * 735274 * 2
def baseEnd_735274 : Nat := 251699316502707647195695

theorem tailTrace_735274 : CollatzResearch.WordTrace tailWord_735274 prefixEnd_735274 251699316502707647195695 := by
  unfold tailWord_735274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704411484558836911697219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17878430625490231764525917 6704411484558836911697219)
  ·
    refine ⟨10056617226838255367545829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704411484558836911697219 10056617226838255367545829)
    ·
      refine ⟨1885615730032172881414843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10056617226838255367545829 1885615730032172881414843)
      ·
        refine ⟨2828423595048259322122265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885615730032172881414843 2828423595048259322122265)
        ·
          refine ⟨2121317696286194491591699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828423595048259322122265 2121317696286194491591699)
          ·
            refine ⟨3181976544429291737387549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121317696286194491591699 3181976544429291737387549)
            ·
              refine ⟨1193241204160984401520331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3181976544429291737387549 1193241204160984401520331)
              ·
                refine ⟨1789861806241476602280497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193241204160984401520331 1789861806241476602280497)
                ·
                  refine ⟨1342396354681107451710373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789861806241476602280497 1342396354681107451710373)
                  ·
                    refine ⟨251699316502707647195695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1342396354681107451710373 251699316502707647195695)
                    ·
                      rfl

theorem cell22_735274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_735274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735274 prefixEnd_735274 := by exact prefixLift 735274
  have htrace : WordTrace (prefixWord ++ tailWord_735274) baseStart_735274 baseEnd_735274 := by
    simpa [prefixWord, tailWord_735274, baseEnd_735274] using wordTrace_append hprefix tailTrace_735274
  have hstable : (prefixWord ++ tailWord_735274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735274).length < 2 ^ (prefixWord ++ tailWord_735274).sum := by decide
  have hdescent : baseEnd_735274 < baseStart_735274 := by decide
  rcases family_descends (prefixWord ++ tailWord_735274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735315 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_735315 : Nat := 118140960795 + 735315 * 2 ^ 59
def prefixEnd_735315 : Nat := 4983230072969 + 3 ^ 40 * 735315 * 2
def baseEnd_735315 : Nat := 251713351640597206920569

theorem tailTrace_735315 : CollatzResearch.WordTrace tailWord_735315 prefixEnd_735315 251713351640597206920569 := by
  unfold tailWord_735315
  simp only [CollatzResearch.WordTrace]
  refine ⟨26819141331086811649031399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17879427554057874432687599 26819141331086811649031399)
  ·
    refine ⟨40228711996630217473547099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26819141331086811649031399 40228711996630217473547099)
    ·
      refine ⟨60343067994945326210320649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40228711996630217473547099 60343067994945326210320649)
      ·
        refine ⟨45257300996208994657740487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60343067994945326210320649 45257300996208994657740487)
        ·
          refine ⟨67885951494313491986610731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45257300996208994657740487 67885951494313491986610731)
          ·
            refine ⟨101828927241470237979916097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67885951494313491986610731 101828927241470237979916097)
            ·
              refine ⟨76371695431102678484937073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101828927241470237979916097 76371695431102678484937073)
              ·
                refine ⟨57278771573327008863702805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76371695431102678484937073 57278771573327008863702805)
                ·
                  refine ⟨2684942417499703540486069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57278771573327008863702805 2684942417499703540486069)
                  ·
                    refine ⟨251713351640597206920569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2684942417499703540486069 251713351640597206920569)
                    ·
                      rfl

theorem cell22_735315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_735315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735315 prefixEnd_735315 := by exact prefixLift 735315
  have htrace : WordTrace (prefixWord ++ tailWord_735315) baseStart_735315 baseEnd_735315 := by
    simpa [prefixWord, tailWord_735315, baseEnd_735315] using wordTrace_append hprefix tailTrace_735315
  have hstable : (prefixWord ++ tailWord_735315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735315).length < 2 ^ (prefixWord ++ tailWord_735315).sum := by decide
  have hdescent : baseEnd_735315 < baseStart_735315 := by decide
  rcases family_descends (prefixWord ++ tailWord_735315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735394 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_735394 : Nat := 118140960795 + 735394 * 2 ^ 59
def prefixEnd_735394 : Nat := 4983230072969 + 3 ^ 40 * 735394 * 2
def baseEnd_735394 : Nat := 251740394955067334195327

theorem tailTrace_735394 : CollatzResearch.WordTrace tailWord_735394 prefixEnd_735394 251740394955067334195327 := by
  unfold tailWord_735394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705505674450152035289309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17881348465200405427438157 6705505674450152035289309)
  ·
    refine ⟨2514564627918807013233491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6705505674450152035289309 2514564627918807013233491)
    ·
      refine ⟨3771846941878210519850237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514564627918807013233491 3771846941878210519850237)
      ·
        refine ⟨1414442603204328944943839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3771846941878210519850237 1414442603204328944943839)
        ·
          refine ⟨2121663904806493417415759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414442603204328944943839 2121663904806493417415759)
          ·
            refine ⟨3182495857209740126123639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121663904806493417415759 3182495857209740126123639)
            ·
              refine ⟨4773743785814610189185459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182495857209740126123639 4773743785814610189185459)
              ·
                refine ⟨7160615678721915283778189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773743785814610189185459 7160615678721915283778189)
                ·
                  refine ⟨2685230879520718231416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7160615678721915283778189 2685230879520718231416821)
                  ·
                    refine ⟨251740394955067334195327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2685230879520718231416821 251740394955067334195327)
                    ·
                      rfl

theorem cell22_735394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_735394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735394 prefixEnd_735394 := by exact prefixLift 735394
  have htrace : WordTrace (prefixWord ++ tailWord_735394) baseStart_735394 baseEnd_735394 := by
    simpa [prefixWord, tailWord_735394, baseEnd_735394] using wordTrace_append hprefix tailTrace_735394
  have hstable : (prefixWord ++ tailWord_735394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735394).length < 2 ^ (prefixWord ++ tailWord_735394).sum := by decide
  have hdescent : baseEnd_735394 < baseStart_735394 := by decide
  rcases family_descends (prefixWord ++ tailWord_735394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735413 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 4]
def baseStart_735413 : Nat := 118140960795 + 735413 * 2 ^ 59
def prefixEnd_735413 : Nat := 4983230072969 + 3 ^ 40 * 735413 * 2
def baseEnd_735413 : Nat := 83915633014452539323423

theorem tailTrace_735413 : CollatzResearch.WordTrace tailWord_735413 prefixEnd_735413 83915633014452539323423 := by
  unfold tailWord_735413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26822715684731774386098893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17881810456487849590732595 26822715684731774386098893)
  ·
    refine ⟨10058518381774415394787085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26822715684731774386098893 10058518381774415394787085)
    ·
      refine ⟨3771944393165405773045157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10058518381774415394787085 3771944393165405773045157)
      ·
        refine ⟨707239573718513582445967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3771944393165405773045157 707239573718513582445967)
        ·
          refine ⟨1060859360577770373668951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707239573718513582445967 1060859360577770373668951)
          ·
            refine ⟨1591289040866655560503427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060859360577770373668951 1591289040866655560503427)
            ·
              refine ⟨2386933561299983340755141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591289040866655560503427 2386933561299983340755141)
              ·
                refine ⟨447550042743746876391589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2386933561299983340755141 447550042743746876391589)
                ·
                  refine ⟨83915633014452539323423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447550042743746876391589 83915633014452539323423)
                  ·
                    rfl

theorem cell22_735413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_735413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735413 prefixEnd_735413 := by exact prefixLift 735413
  have htrace : WordTrace (prefixWord ++ tailWord_735413) baseStart_735413 baseEnd_735413 := by
    simpa [prefixWord, tailWord_735413, baseEnd_735413] using wordTrace_append hprefix tailTrace_735413
  have hstable : (prefixWord ++ tailWord_735413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735413).length < 2 ^ (prefixWord ++ tailWord_735413).sum := by decide
  have hdescent : baseEnd_735413 < baseStart_735413 := by decide
  rcases family_descends (prefixWord ++ tailWord_735413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735424 : List Nat := [2, 1, 1, 2, 5, 3, 1, 7]
def baseStart_735424 : Nat := 118140960795 + 735424 * 2 ^ 59
def prefixEnd_735424 : Nat := 4983230072969 + 3 ^ 40 * 735424 * 2
def baseEnd_735424 : Nat := 27972296063128583993915

theorem tailTrace_735424 : CollatzResearch.WordTrace tailWord_735424 prefixEnd_735424 27972296063128583993915 := by
  unfold tailWord_735424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411558443845961632374663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17882077925127948843166217 13411558443845961632374663)
  ·
    refine ⟨20117337665768942448561995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13411558443845961632374663 20117337665768942448561995)
    ·
      refine ⟨30176006498653413672842993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20117337665768942448561995 30176006498653413672842993)
      ·
        refine ⟨22632004873990060254632245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30176006498653413672842993 22632004873990060254632245)
        ·
          refine ⟨2121750456936568148871773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22632004873990060254632245 2121750456936568148871773)
          ·
            refine ⟨795656421351213055826915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2121750456936568148871773 795656421351213055826915)
            ·
              refine ⟨1193484632026819583740373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795656421351213055826915 1193484632026819583740373)
              ·
                refine ⟨27972296063128583993915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1193484632026819583740373 27972296063128583993915)
                ·
                  rfl

theorem cell22_735424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_735424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735424 prefixEnd_735424 := by exact prefixLift 735424
  have htrace : WordTrace (prefixWord ++ tailWord_735424) baseStart_735424 baseEnd_735424 := by
    simpa [prefixWord, tailWord_735424, baseEnd_735424] using wordTrace_append hprefix tailTrace_735424
  have hstable : (prefixWord ++ tailWord_735424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735424).length < 2 ^ (prefixWord ++ tailWord_735424).sum := by decide
  have hdescent : baseEnd_735424 < baseStart_735424 := by decide
  rcases family_descends (prefixWord ++ tailWord_735424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735439 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 3, 3]
def baseStart_735439 : Nat := 118140960795 + 735439 * 2 ^ 59
def prefixEnd_735439 : Nat := 4983230072969 + 3 ^ 40 * 735439 * 2
def baseEnd_735439 : Nat := 251755799374702216820189

theorem tailTrace_735439 : CollatzResearch.WordTrace tailWord_735439 prefixEnd_735439 251755799374702216820189 := by
  unfold tailWord_735439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26823663982637580826545371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17882442655091720551030247 26823663982637580826545371)
  ·
    refine ⟨40235495973956371239818057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26823663982637580826545371 40235495973956371239818057)
    ·
      refine ⟨30176621980467278429863543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40235495973956371239818057 30176621980467278429863543)
      ·
        refine ⟨45264932970700917644795315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30176621980467278429863543 45264932970700917644795315)
        ·
          refine ⟨67897399456051376467192973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45264932970700917644795315 67897399456051376467192973)
          ·
            refine ⟨25461524796019266175197365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67897399456051376467192973 25461524796019266175197365)
            ·
              refine ⟨2387017949626806203924753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25461524796019266175197365 2387017949626806203924753)
              ·
                refine ⟨1790263462220104652943565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387017949626806203924753 1790263462220104652943565)
                ·
                  refine ⟨671348798332539244853837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1790263462220104652943565 671348798332539244853837)
                  ·
                    refine ⟨251755799374702216820189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671348798332539244853837 251755799374702216820189)
                    ·
                      rfl

theorem cell22_735439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_735439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735439 prefixEnd_735439 := by exact prefixLift 735439
  have htrace : WordTrace (prefixWord ++ tailWord_735439) baseStart_735439 baseEnd_735439 := by
    simpa [prefixWord, tailWord_735439, baseEnd_735439] using wordTrace_append hprefix tailTrace_735439
  have hstable : (prefixWord ++ tailWord_735439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735439).length < 2 ^ (prefixWord ++ tailWord_735439).sum := by decide
  have hdescent : baseEnd_735439 < baseStart_735439 := by decide
  rcases family_descends (prefixWord ++ tailWord_735439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735458 : List Nat := [3, 3, 4, 1, 1, 1, 9]
def baseStart_735458 : Nat := 118140960795 + 735458 * 2 ^ 59
def prefixEnd_735458 : Nat := 4983230072969 + 3 ^ 40 * 735458 * 2
def baseEnd_735458 : Nat := 9324529757888611133153

theorem tailTrace_735458 : CollatzResearch.WordTrace tailWord_735458 prefixEnd_735458 9324529757888611133153 := by
  unfold tailWord_735458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706089242392186767871757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17882904646379164714324685 6706089242392186767871757)
  ·
    refine ⟨2514783465897070037951909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6706089242392186767871757 2514783465897070037951909)
    ·
      refine ⟨471521899855700632115983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2514783465897070037951909 471521899855700632115983)
      ·
        refine ⟨707282849783550948173975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471521899855700632115983 707282849783550948173975)
        ·
          refine ⟨1060924274675326422260963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707282849783550948173975 1060924274675326422260963)
          ·
            refine ⟨1591386412012989633391445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060924274675326422260963 1591386412012989633391445)
            ·
              refine ⟨9324529757888611133153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1591386412012989633391445 9324529757888611133153)
              ·
                rfl

theorem cell22_735458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 9].length) (baseStart_735458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735458 prefixEnd_735458 := by exact prefixLift 735458
  have htrace : WordTrace (prefixWord ++ tailWord_735458) baseStart_735458 baseEnd_735458 := by
    simpa [prefixWord, tailWord_735458, baseEnd_735458] using wordTrace_append hprefix tailTrace_735458
  have hstable : (prefixWord ++ tailWord_735458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735458).length < 2 ^ (prefixWord ++ tailWord_735458).sum := by decide
  have hdescent : baseEnd_735458 < baseStart_735458 := by decide
  rcases family_descends (prefixWord ++ tailWord_735458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735467 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_735467 : Nat := 118140960795 + 735467 * 2 ^ 59
def prefixEnd_735467 : Nat := 4983230072969 + 3 ^ 40 * 735467 * 2
def baseEnd_735467 : Nat := 251765384346919477120103

theorem tailTrace_735467 : CollatzResearch.WordTrace tailWord_735467 prefixEnd_735467 251765384346919477120103 := by
  unfold tailWord_735467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26824685226536141608564655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17883123484357427739043103 26824685226536141608564655)
  ·
    refine ⟨40237027839804212412846983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26824685226536141608564655 40237027839804212412846983)
    ·
      refine ⟨60355541759706318619270475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40237027839804212412846983 60355541759706318619270475)
      ·
        refine ⟨90533312639559477928905713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60355541759706318619270475 90533312639559477928905713)
        ·
          refine ⟨67899984479669608446679285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90533312639559477928905713 67899984479669608446679285)
          ·
            refine ⟨6365623544969025791876183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67899984479669608446679285 6365623544969025791876183)
            ·
              refine ⟨9548435317453538687814275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365623544969025791876183 9548435317453538687814275)
              ·
                refine ⟨14322652976180308031721413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548435317453538687814275 14322652976180308031721413)
                ·
                  refine ⟨2685497433033807755947765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14322652976180308031721413 2685497433033807755947765)
                  ·
                    refine ⟨251765384346919477120103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2685497433033807755947765 251765384346919477120103)
                    ·
                      rfl

theorem cell22_735467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_735467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735467 prefixEnd_735467 := by exact prefixLift 735467
  have htrace : WordTrace (prefixWord ++ tailWord_735467) baseStart_735467 baseEnd_735467 := by
    simpa [prefixWord, tailWord_735467, baseEnd_735467] using wordTrace_append hprefix tailTrace_735467
  have hstable : (prefixWord ++ tailWord_735467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735467).length < 2 ^ (prefixWord ++ tailWord_735467).sum := by decide
  have hdescent : baseEnd_735467 < baseStart_735467 := by decide
  rcases family_descends (prefixWord ++ tailWord_735467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735484 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_735484 : Nat := 118140960795 + 735484 * 2 ^ 59
def prefixEnd_735484 : Nat := 4983230072969 + 3 ^ 40 * 735484 * 2
def baseEnd_735484 : Nat := 251771203794337099445051

theorem tailTrace_735484 : CollatzResearch.WordTrace tailWord_735484 prefixEnd_735484 251771203794337099445051 := by
  unfold tailWord_735484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412652633737276755966753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17883536844983035674622337 13412652633737276755966753)
  ·
    refine ⟨10059489475302957566975065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13412652633737276755966753 10059489475302957566975065)
    ·
      refine ⟨7544617106477218175231299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10059489475302957566975065 7544617106477218175231299)
      ·
        refine ⟨11316925659715827262846949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7544617106477218175231299 11316925659715827262846949)
        ·
          refine ⟨2121923561196717611783803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11316925659715827262846949 2121923561196717611783803)
          ·
            refine ⟨3182885341795076417675705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121923561196717611783803 3182885341795076417675705)
            ·
              refine ⟨2387164006346307313256779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182885341795076417675705 2387164006346307313256779)
              ·
                refine ⟨3580746009519460969885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387164006346307313256779 3580746009519460969885169)
                ·
                  refine ⟨2685559507139595727413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580746009519460969885169 2685559507139595727413877)
                  ·
                    refine ⟨251771203794337099445051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2685559507139595727413877 251771203794337099445051)
                    ·
                      rfl

theorem cell22_735484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_735484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735484 prefixEnd_735484 := by exact prefixLift 735484
  have htrace : WordTrace (prefixWord ++ tailWord_735484) baseStart_735484 baseEnd_735484 := by
    simpa [prefixWord, tailWord_735484, baseEnd_735484] using wordTrace_append hprefix tailTrace_735484
  have hstable : (prefixWord ++ tailWord_735484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735484).length < 2 ^ (prefixWord ++ tailWord_735484).sum := by decide
  have hdescent : baseEnd_735484 < baseStart_735484 := by decide
  rcases family_descends (prefixWord ++ tailWord_735484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735589 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_735589 : Nat := 118140960795 + 735589 * 2 ^ 59
def prefixEnd_735589 : Nat := 4983230072969 + 3 ^ 40 * 735589 * 2
def baseEnd_735589 : Nat := 251807147440151825569729

theorem tailTrace_735589 : CollatzResearch.WordTrace tailWord_735589 prefixEnd_735589 251807147440151825569729 := by
  unfold tailWord_735589
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829134932094156444505821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17886089954729437629670547 26829134932094156444505821)
  ·
    refine ⟨10060925599535308666689683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26829134932094156444505821 10060925599535308666689683)
    ·
      refine ⟨15091388399302963000034525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10060925599535308666689683 15091388399302963000034525)
      ·
        refine ⟨5659270649738611125012947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15091388399302963000034525 5659270649738611125012947)
        ·
          refine ⟨8488905974607916687519421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659270649738611125012947 8488905974607916687519421)
          ·
            refine ⟨3183339740477968757819783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8488905974607916687519421 3183339740477968757819783)
            ·
              refine ⟨4775009610716953136729675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183339740477968757819783 4775009610716953136729675)
              ·
                refine ⟨7162514416075429705094513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775009610716953136729675 7162514416075429705094513)
                ·
                  refine ⟨5371885812056572278820885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162514416075429705094513 5371885812056572278820885)
                  ·
                    refine ⟨251807147440151825569729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5371885812056572278820885 251807147440151825569729)
                    ·
                      rfl

theorem cell22_735589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_735589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735589 prefixEnd_735589 := by exact prefixLift 735589
  have htrace : WordTrace (prefixWord ++ tailWord_735589) baseStart_735589 baseEnd_735589 := by
    simpa [prefixWord, tailWord_735589, baseEnd_735589] using wordTrace_append hprefix tailTrace_735589
  have hstable : (prefixWord ++ tailWord_735589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735589).length < 2 ^ (prefixWord ++ tailWord_735589).sum := by decide
  have hdescent : baseEnd_735589 < baseStart_735589 := by decide
  rcases family_descends (prefixWord ++ tailWord_735589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735625 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 1, 3]
def baseStart_735625 : Nat := 118140960795 + 735625 * 2 ^ 59
def prefixEnd_735625 : Nat := 4983230072969 + 3 ^ 40 * 735625 * 2
def baseEnd_735625 : Nat := 251819470975859731669619

theorem tailTrace_735625 : CollatzResearch.WordTrace tailWord_735625 prefixEnd_735625 251819470975859731669619 := by
  unfold tailWord_735625
  simp only [CollatzResearch.WordTrace]
  refine ⟨26830447959963734592816329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17886965306642489728544219 26830447959963734592816329)
  ·
    refine ⟨20122835969972800944612247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26830447959963734592816329 20122835969972800944612247)
    ·
      refine ⟨30184253954959201416918371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20122835969972800944612247 30184253954959201416918371)
      ·
        refine ⟨45276380932438802125377557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30184253954959201416918371 45276380932438802125377557)
        ·
          refine ⟨2122330356208068849627073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45276380932438802125377557 2122330356208068849627073)
          ·
            refine ⟨1591747767156051637220305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122330356208068849627073 1591747767156051637220305)
            ·
              refine ⟨1193810825367038727915229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591747767156051637220305 1193810825367038727915229)
              ·
                refine ⟨447679059512639522968211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193810825367038727915229 447679059512639522968211)
                ·
                  refine ⟨671518589268959284452317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447679059512639522968211 671518589268959284452317)
                  ·
                    refine ⟨251819470975859731669619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671518589268959284452317 251819470975859731669619)
                    ·
                      rfl

theorem cell22_735625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_735625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735625 prefixEnd_735625 := by exact prefixLift 735625
  have htrace : WordTrace (prefixWord ++ tailWord_735625) baseStart_735625 baseEnd_735625 := by
    simpa [prefixWord, tailWord_735625, baseEnd_735625] using wordTrace_append hprefix tailTrace_735625
  have hstable : (prefixWord ++ tailWord_735625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735625).length < 2 ^ (prefixWord ++ tailWord_735625).sum := by decide
  have hdescent : baseEnd_735625 < baseStart_735625 := by decide
  rcases family_descends (prefixWord ++ tailWord_735625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735711 : List Nat := [1, 1, 2, 3, 3, 3, 2, 7]
def baseStart_735711 : Nat := 118140960795 + 735711 * 2 ^ 59
def prefixEnd_735711 : Nat := 4983230072969 + 3 ^ 40 * 735711 * 2
def baseEnd_735711 : Nat := 27983212281487130446595

theorem tailTrace_735711 : CollatzResearch.WordTrace tailWord_735711 prefixEnd_735711 27983212281487130446595 := by
  unfold tailWord_735711
  simp only [CollatzResearch.WordTrace]
  refine ⟨26833584637652171280446987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17889056425101447520297991 26833584637652171280446987)
  ·
    refine ⟨40250376956478256920670481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26833584637652171280446987 40250376956478256920670481)
    ·
      refine ⟨30187782717358692690502861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40250376956478256920670481 30187782717358692690502861)
      ·
        refine ⟨11320418519009509758938573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30187782717358692690502861 11320418519009509758938573)
        ·
          refine ⟨4245156944628566159601965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11320418519009509758938573 4245156944628566159601965)
          ·
            refine ⟨1591933854235712309850737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4245156944628566159601965 1591933854235712309850737)
            ·
              refine ⟨1193950390676784232388053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591933854235712309850737 1193950390676784232388053)
              ·
                refine ⟨27983212281487130446595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1193950390676784232388053 27983212281487130446595)
                ·
                  rfl

theorem cell22_735711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 7].length) (baseStart_735711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735711 prefixEnd_735711 := by exact prefixLift 735711
  have htrace : WordTrace (prefixWord ++ tailWord_735711) baseStart_735711 baseEnd_735711 := by
    simpa [prefixWord, tailWord_735711, baseEnd_735711] using wordTrace_append hprefix tailTrace_735711
  have hstable : (prefixWord ++ tailWord_735711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735711).length < 2 ^ (prefixWord ++ tailWord_735711).sum := by decide
  have hdescent : baseEnd_735711 < baseStart_735711 := by decide
  rcases family_descends (prefixWord ++ tailWord_735711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735715 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 2, 3]
def baseStart_735715 : Nat := 118140960795 + 735715 * 2 ^ 59
def prefixEnd_735715 : Nat := 4983230072969 + 3 ^ 40 * 735715 * 2
def baseEnd_735715 : Nat := 251850279815129496919343

theorem tailTrace_735715 : CollatzResearch.WordTrace tailWord_735715 prefixEnd_735715 251850279815129496919343 := by
  unfold tailWord_735715
  simp only [CollatzResearch.WordTrace]
  refine ⟨26833730529637679963592599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17889153686425119975728399 26833730529637679963592599)
  ·
    refine ⟨40250595794456519945388899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26833730529637679963592599 40250595794456519945388899)
    ·
      refine ⟨60375893691684779918083349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40250595794456519945388899 60375893691684779918083349)
      ·
        refine ⟨2830120016797724058660157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60375893691684779918083349 2830120016797724058660157)
        ·
          refine ⟨1061295006299146521997559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2830120016797724058660157 1061295006299146521997559)
          ·
            refine ⟨1591942509448719782996339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061295006299146521997559 1591942509448719782996339)
            ·
              refine ⟨2387913764173079674494509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591942509448719782996339 2387913764173079674494509)
              ·
                refine ⟨895467661564904877935441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2387913764173079674494509 895467661564904877935441)
                ·
                  refine ⟨671600746173678658451581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 895467661564904877935441 671600746173678658451581)
                  ·
                    refine ⟨251850279815129496919343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671600746173678658451581 251850279815129496919343)
                    ·
                      rfl

theorem cell22_735715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3].length) (baseStart_735715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735715 prefixEnd_735715 := by exact prefixLift 735715
  have htrace : WordTrace (prefixWord ++ tailWord_735715) baseStart_735715 baseEnd_735715 := by
    simpa [prefixWord, tailWord_735715, baseEnd_735715] using wordTrace_append hprefix tailTrace_735715
  have hstable : (prefixWord ++ tailWord_735715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735715).length < 2 ^ (prefixWord ++ tailWord_735715).sum := by decide
  have hdescent : baseEnd_735715 < baseStart_735715 := by decide
  rcases family_descends (prefixWord ++ tailWord_735715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735730 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_735730 : Nat := 118140960795 + 735730 * 2 ^ 59
def prefixEnd_735730 : Nat := 4983230072969 + 3 ^ 40 * 735730 * 2
def baseEnd_735730 : Nat := 251855414621674457794297

theorem tailTrace_735730 : CollatzResearch.WordTrace tailWord_735730 prefixEnd_735730 251855414621674457794297 := by
  unfold tailWord_735730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708569406145834381347161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17889518416388891683592429 6708569406145834381347161)
  ·
    refine ⟨5031427054609375786010371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6708569406145834381347161 5031427054609375786010371)
    ·
      refine ⟨7547140581914063679015557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5031427054609375786010371 7547140581914063679015557)
      ·
        refine ⟨1415088859108886939815417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7547140581914063679015557 1415088859108886939815417)
        ·
          refine ⟨1061316644331665204861563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415088859108886939815417 1061316644331665204861563)
          ·
            refine ⟨1591974966497497807292345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061316644331665204861563 1591974966497497807292345)
            ·
              refine ⟨1193981224873123355469259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591974966497497807292345 1193981224873123355469259)
              ·
                refine ⟨1790971837309685033203889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193981224873123355469259 1790971837309685033203889)
                ·
                  refine ⟨1343228877982263774902917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790971837309685033203889 1343228877982263774902917)
                  ·
                    refine ⟨251855414621674457794297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1343228877982263774902917 251855414621674457794297)
                    ·
                      rfl

theorem cell22_735730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_735730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735730 prefixEnd_735730 := by exact prefixLift 735730
  have htrace : WordTrace (prefixWord ++ tailWord_735730) baseStart_735730 baseEnd_735730 := by
    simpa [prefixWord, tailWord_735730, baseEnd_735730] using wordTrace_append hprefix tailTrace_735730
  have hstable : (prefixWord ++ tailWord_735730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735730).length < 2 ^ (prefixWord ++ tailWord_735730).sum := by decide
  have hdescent : baseEnd_735730 < baseStart_735730 := by decide
  rcases family_descends (prefixWord ++ tailWord_735730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735773 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 5]
def baseStart_735773 : Nat := 118140960795 + 735773 * 2 ^ 59
def prefixEnd_735773 : Nat := 4983230072969 + 3 ^ 40 * 735773 * 2
def baseEnd_735773 : Nat := 83956711466812226323055

theorem tailTrace_735773 : CollatzResearch.WordTrace tailWord_735773 prefixEnd_735773 83956711466812226323055 := by
  unfold tailWord_735773
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835845963427555869203973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17890563975618370579469315 26835845963427555869203973)
  ·
    refine ⟨5031721118142666725475745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26835845963427555869203973 5031721118142666725475745)
    ·
      refine ⟨3773790838607000044106809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5031721118142666725475745 3773790838607000044106809)
      ·
        refine ⟨2830343128955250033080107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3773790838607000044106809 2830343128955250033080107)
        ·
          refine ⟨4245514693432875049620161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830343128955250033080107 4245514693432875049620161)
          ·
            refine ⟨3184136020074656287215121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245514693432875049620161 3184136020074656287215121)
            ·
              refine ⟨2388102015055992215411341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184136020074656287215121 2388102015055992215411341)
              ·
                refine ⟨895538255645997080779253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2388102015055992215411341 895538255645997080779253)
                ·
                  refine ⟨83956711466812226323055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895538255645997080779253 83956711466812226323055)
                  ·
                    rfl

theorem cell22_735773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_735773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735773 prefixEnd_735773 := by exact prefixLift 735773
  have htrace : WordTrace (prefixWord ++ tailWord_735773) baseStart_735773 baseEnd_735773 := by
    simpa [prefixWord, tailWord_735773, baseEnd_735773] using wordTrace_append hprefix tailTrace_735773
  have hstable : (prefixWord ++ tailWord_735773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735773).length < 2 ^ (prefixWord ++ tailWord_735773).sum := by decide
  have hdescent : baseEnd_735773 < baseStart_735773 := by decide
  rcases family_descends (prefixWord ++ tailWord_735773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735801 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 8]
def baseStart_735801 : Nat := 118140960795 + 735801 * 2 ^ 59
def prefixEnd_735801 : Nat := 4983230072969 + 3 ^ 40 * 735801 * 2
def baseEnd_735801 : Nat := 83959906457551313089693

theorem tailTrace_735801 : CollatzResearch.WordTrace tailWord_735801 prefixEnd_735801 83959906457551313089693 := by
  unfold tailWord_735801
  simp only [CollatzResearch.WordTrace]
  refine ⟨26836867207326116651223257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17891244804884077767482171 26836867207326116651223257)
  ·
    refine ⟨20127650405494587488417443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26836867207326116651223257 20127650405494587488417443)
    ·
      refine ⟨30191475608241881232626165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20127650405494587488417443 30191475608241881232626165)
      ·
        refine ⟨2830450838272676365558703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30191475608241881232626165 2830450838272676365558703)
        ·
          refine ⟨4245676257409014548338055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830450838272676365558703 4245676257409014548338055)
          ·
            refine ⟨6368514386113521822507083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245676257409014548338055 6368514386113521822507083)
            ·
              refine ⟨9552771579170282733760625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368514386113521822507083 9552771579170282733760625)
              ·
                refine ⟨7164578684377712050320469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9552771579170282733760625 7164578684377712050320469)
                ·
                  refine ⟨83959906457551313089693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7164578684377712050320469 83959906457551313089693)
                  ·
                    rfl

theorem cell22_735801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_735801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735801 prefixEnd_735801 := by exact prefixLift 735801
  have htrace : WordTrace (prefixWord ++ tailWord_735801) baseStart_735801 baseEnd_735801 := by
    simpa [prefixWord, tailWord_735801, baseEnd_735801] using wordTrace_append hprefix tailTrace_735801
  have hstable : (prefixWord ++ tailWord_735801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735801).length < 2 ^ (prefixWord ++ tailWord_735801).sum := by decide
  have hdescent : baseEnd_735801 < baseStart_735801 := by decide
  rcases family_descends (prefixWord ++ tailWord_735801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735816 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_735816 : Nat := 118140960795 + 735816 * 2 ^ 59
def prefixEnd_735816 : Nat := 4983230072969 + 3 ^ 40 * 735816 * 2
def baseEnd_735816 : Nat := 251884854179198900144033

theorem tailTrace_735816 : CollatzResearch.WordTrace tailWord_735816 prefixEnd_735816 251884854179198900144033 := by
  unfold tailWord_735816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418707151135887106509651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17891609534847849475346201 13418707151135887106509651)
  ·
    refine ⟨20128060726703830659764477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13418707151135887106509651 20128060726703830659764477)
    ·
      refine ⟨7548022772513936497411679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20128060726703830659764477 7548022772513936497411679)
      ·
        refine ⟨11322034158770904746117519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7548022772513936497411679 11322034158770904746117519)
        ·
          refine ⟨16983051238156357119176279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11322034158770904746117519 16983051238156357119176279)
          ·
            refine ⟨25474576857234535678764419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16983051238156357119176279 25474576857234535678764419)
            ·
              refine ⟨38211865285851803518146629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25474576857234535678764419 38211865285851803518146629)
              ·
                refine ⟨7164724741097213159652493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38211865285851803518146629 7164724741097213159652493)
                ·
                  refine ⟨2686771777911454934869685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7164724741097213159652493 2686771777911454934869685)
                  ·
                    refine ⟨251884854179198900144033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2686771777911454934869685 251884854179198900144033)
                    ·
                      rfl

theorem cell22_735816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_735816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735816 prefixEnd_735816 := by exact prefixLift 735816
  have htrace : WordTrace (prefixWord ++ tailWord_735816) baseStart_735816 baseEnd_735816 := by
    simpa [prefixWord, tailWord_735816, baseEnd_735816] using wordTrace_append hprefix tailTrace_735816
  have hstable : (prefixWord ++ tailWord_735816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735816).length < 2 ^ (prefixWord ++ tailWord_735816).sum := by decide
  have hdescent : baseEnd_735816 < baseStart_735816 := by decide
  rcases family_descends (prefixWord ++ tailWord_735816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735818 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_735818 : Nat := 118140960795 + 735818 * 2 ^ 59
def prefixEnd_735818 : Nat := 4983230072969 + 3 ^ 40 * 735818 * 2
def baseEnd_735818 : Nat := 83961846273357187198009

theorem tailTrace_735818 : CollatzResearch.WordTrace tailWord_735818 prefixEnd_735818 83961846273357187198009 := by
  unfold tailWord_735818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709371812066132138648027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17891658165509685703061405 6709371812066132138648027)
  ·
    refine ⟨10064057718099198207972041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6709371812066132138648027 10064057718099198207972041)
    ·
      refine ⟨7548043288574398655979031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10064057718099198207972041 7548043288574398655979031)
      ·
        refine ⟨11322064932861597983968547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7548043288574398655979031 11322064932861597983968547)
        ·
          refine ⟨16983097399292396975952821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11322064932861597983968547 16983097399292396975952821)
          ·
            refine ⟨1592165381183662216495577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16983097399292396975952821 1592165381183662216495577)
            ·
              refine ⟨1194124035887746662371683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592165381183662216495577 1194124035887746662371683)
              ·
                refine ⟨1791186053831619993557525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194124035887746662371683 1791186053831619993557525)
                ·
                  refine ⟨83961846273357187198009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1791186053831619993557525 83961846273357187198009)
                  ·
                    rfl

theorem cell22_735818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_735818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735818 prefixEnd_735818 := by exact prefixLift 735818
  have htrace : WordTrace (prefixWord ++ tailWord_735818) baseStart_735818 baseEnd_735818 := by
    simpa [prefixWord, tailWord_735818, baseEnd_735818] using wordTrace_append hprefix tailTrace_735818
  have hstable : (prefixWord ++ tailWord_735818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735818).length < 2 ^ (prefixWord ++ tailWord_735818).sum := by decide
  have hdescent : baseEnd_735818 < baseStart_735818 := by decide
  rcases family_descends (prefixWord ++ tailWord_735818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735831 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_735831 : Nat := 118140960795 + 735831 * 2 ^ 59
def prefixEnd_735831 : Nat := 4983230072969 + 3 ^ 40 * 735831 * 2
def baseEnd_735831 : Nat := 251889988985743861018987

theorem tailTrace_735831 : CollatzResearch.WordTrace tailWord_735831 prefixEnd_735831 251889988985743861018987 := by
  unfold tailWord_735831
  simp only [CollatzResearch.WordTrace]
  refine ⟨26837961397217431774815347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17891974264811621183210231 26837961397217431774815347)
  ·
    refine ⟨40256942095826147662223021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26837961397217431774815347 40256942095826147662223021)
    ·
      refine ⟨15096353285934805373333633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40256942095826147662223021 15096353285934805373333633)
      ·
        refine ⟨11322264964451104030000225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15096353285934805373333633 11322264964451104030000225)
        ·
          refine ⟨8491698723338328022500169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11322264964451104030000225 8491698723338328022500169)
          ·
            refine ⟨6368774042503746016875127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491698723338328022500169 6368774042503746016875127)
            ·
              refine ⟨9553161063755619025312691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368774042503746016875127 9553161063755619025312691)
              ·
                refine ⟨14329741595633428537969037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9553161063755619025312691 14329741595633428537969037)
                ·
                  refine ⟨5373653098362535701738389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14329741595633428537969037 5373653098362535701738389)
                  ·
                    refine ⟨251889988985743861018987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5373653098362535701738389 251889988985743861018987)
                    ·
                      rfl

theorem cell22_735831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_735831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735831 prefixEnd_735831 := by exact prefixLift 735831
  have htrace : WordTrace (prefixWord ++ tailWord_735831) baseStart_735831 baseEnd_735831 := by
    simpa [prefixWord, tailWord_735831, baseEnd_735831] using wordTrace_append hprefix tailTrace_735831
  have hstable : (prefixWord ++ tailWord_735831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735831).length < 2 ^ (prefixWord ++ tailWord_735831).sum := by decide
  have hdescent : baseEnd_735831 < baseStart_735831 := by decide
  rcases family_descends (prefixWord ++ tailWord_735831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735925 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 5]
def baseStart_735925 : Nat := 118140960795 + 735925 * 2 ^ 59
def prefixEnd_735925 : Nat := 4983230072969 + 3 ^ 40 * 735925 * 2
def baseEnd_735925 : Nat := 83974055702252983056233

theorem tailTrace_735925 : CollatzResearch.WordTrace tailWord_735925 prefixEnd_735925 83974055702252983056233 := by
  unfold tailWord_735925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26841389858876885828737229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17894259905917923885824819 26841389858876885828737229)
  ·
    refine ⟨10065521197078832185776461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26841389858876885828737229 10065521197078832185776461)
    ·
      refine ⟨3774570448904562069666173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10065521197078832185776461 3774570448904562069666173)
      ·
        refine ⟨1415463918339210776124815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3774570448904562069666173 1415463918339210776124815)
        ·
          refine ⟨2123195877508816164187223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415463918339210776124815 2123195877508816164187223)
          ·
            refine ⟨3184793816263224246280835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123195877508816164187223 3184793816263224246280835)
            ·
              refine ⟨4777190724394836369421253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184793816263224246280835 4777190724394836369421253)
              ·
                refine ⟨895723260824031819266485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4777190724394836369421253 895723260824031819266485)
                ·
                  refine ⟨83974055702252983056233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895723260824031819266485 83974055702252983056233)
                  ·
                    rfl

theorem cell22_735925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_735925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735925 prefixEnd_735925 := by exact prefixLift 735925
  have htrace : WordTrace (prefixWord ++ tailWord_735925) baseStart_735925 baseEnd_735925 := by
    simpa [prefixWord, tailWord_735925, baseEnd_735925] using wordTrace_append hprefix tailTrace_735925
  have hstable : (prefixWord ++ tailWord_735925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735925).length < 2 ^ (prefixWord ++ tailWord_735925).sum := by decide
  have hdescent : baseEnd_735925 < baseStart_735925 := by decide
  rcases family_descends (prefixWord ++ tailWord_735925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735940 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_735940 : Nat := 118140960795 + 735940 * 2 ^ 59
def prefixEnd_735940 : Nat := 4983230072969 + 3 ^ 40 * 735940 * 2
def baseEnd_735940 : Nat := 251927301913303910043653

theorem tailTrace_735940 : CollatzResearch.WordTrace tailWord_735940 prefixEnd_735940 251927301913303910043653 := by
  unfold tailWord_735940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420968476911271695266637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17894624635881695593688849 13420968476911271695266637)
  ·
    refine ⟨5032863178841726885724989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13420968476911271695266637 5032863178841726885724989)
    ·
      refine ⟨1887323692065647582146871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5032863178841726885724989 1887323692065647582146871)
      ·
        refine ⟨2830985538098471373220307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887323692065647582146871 2830985538098471373220307)
        ·
          refine ⟨4246478307147707059830461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830985538098471373220307 4246478307147707059830461)
          ·
            refine ⟨1592429365180390147436423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4246478307147707059830461 1592429365180390147436423)
            ·
              refine ⟨2388644047770585221154635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592429365180390147436423 2388644047770585221154635)
              ·
                refine ⟨3582966071655877831731953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388644047770585221154635 3582966071655877831731953)
                ·
                  refine ⟨2687224553741908373798965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3582966071655877831731953 2687224553741908373798965)
                  ·
                    refine ⟨251927301913303910043653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2687224553741908373798965 251927301913303910043653)
                    ·
                      rfl

theorem cell22_735940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_735940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735940 prefixEnd_735940 := by exact prefixLift 735940
  have htrace : WordTrace (prefixWord ++ tailWord_735940) baseStart_735940 baseEnd_735940 := by
    simpa [prefixWord, tailWord_735940, baseEnd_735940] using wordTrace_append hprefix tailTrace_735940
  have hstable : (prefixWord ++ tailWord_735940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735940).length < 2 ^ (prefixWord ++ tailWord_735940).sum := by decide
  have hdescent : baseEnd_735940 < baseStart_735940 := by decide
  rcases family_descends (prefixWord ++ tailWord_735940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735953 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 6]
def baseStart_735953 : Nat := 118140960795 + 735953 * 2 ^ 59
def prefixEnd_735953 : Nat := 4983230072969 + 3 ^ 40 * 735953 * 2
def baseEnd_735953 : Nat := 83977250692992069822871

theorem tailTrace_735953 : CollatzResearch.WordTrace tailWord_735953 prefixEnd_735953 83977250692992069822871 := by
  unfold tailWord_735953
  simp only [CollatzResearch.WordTrace]
  refine ⟨26842411102775446610756513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17894940735183631073837675 26842411102775446610756513)
  ·
    refine ⟨20131808327081584958067385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26842411102775446610756513 20131808327081584958067385)
    ·
      refine ⟨15098856245311188718550539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20131808327081584958067385 15098856245311188718550539)
      ·
        refine ⟨22648284367966783077825809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15098856245311188718550539 22648284367966783077825809)
        ·
          refine ⟨16986213275975087308369357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22648284367966783077825809 16986213275975087308369357)
          ·
            refine ⟨6369829978490657740638509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16986213275975087308369357 6369829978490657740638509)
            ·
              refine ⟨2388686241933996652739441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6369829978490657740638509 2388686241933996652739441)
              ·
                refine ⟨1791514681450497489554581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388686241933996652739441 1791514681450497489554581)
                ·
                  refine ⟨83977250692992069822871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1791514681450497489554581 83977250692992069822871)
                  ·
                    rfl

theorem cell22_735953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_735953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735953 prefixEnd_735953 := by exact prefixLift 735953
  have htrace : WordTrace (prefixWord ++ tailWord_735953) baseStart_735953 baseEnd_735953 := by
    simpa [prefixWord, tailWord_735953, baseEnd_735953] using wordTrace_append hprefix tailTrace_735953
  have hstable : (prefixWord ++ tailWord_735953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735953).length < 2 ^ (prefixWord ++ tailWord_735953).sum := by decide
  have hdescent : baseEnd_735953 < baseStart_735953 := by decide
  rcases family_descends (prefixWord ++ tailWord_735953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735972 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_735972 : Nat := 118140960795 + 735972 * 2 ^ 59
def prefixEnd_735972 : Nat := 4983230072969 + 3 ^ 40 * 735972 * 2
def baseEnd_735972 : Nat := 251938256167266493243555

theorem tailTrace_735972 : CollatzResearch.WordTrace tailWord_735972 prefixEnd_735972 251938256167266493243555 := by
  unfold tailWord_735972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13421552044853306427849085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17895402726471075237132113 13421552044853306427849085)
  ·
    refine ⟨5033082016819989910443407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13421552044853306427849085 5033082016819989910443407)
    ·
      refine ⟨7549623025229984865665111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033082016819989910443407 7549623025229984865665111)
      ·
        refine ⟨11324434537844977298497667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7549623025229984865665111 11324434537844977298497667)
        ·
          refine ⟨16986651806767465947746501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11324434537844977298497667 16986651806767465947746501)
          ·
            refine ⟨3184997213768899865202469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16986651806767465947746501 3184997213768899865202469)
            ·
              refine ⟨597186977581668724725463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3184997213768899865202469 597186977581668724725463)
              ·
                refine ⟨895780466372503087088195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597186977581668724725463 895780466372503087088195)
                ·
                  refine ⟨1343670699558754630632293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895780466372503087088195 1343670699558754630632293)
                  ·
                    refine ⟨251938256167266493243555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1343670699558754630632293 251938256167266493243555)
                    ·
                      rfl

theorem cell22_735972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_735972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735972 prefixEnd_735972 := by exact prefixLift 735972
  have htrace : WordTrace (prefixWord ++ tailWord_735972) baseStart_735972 baseEnd_735972 := by
    simpa [prefixWord, tailWord_735972, baseEnd_735972] using wordTrace_append hprefix tailTrace_735972
  have hstable : (prefixWord ++ tailWord_735972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735972).length < 2 ^ (prefixWord ++ tailWord_735972).sum := by decide
  have hdescent : baseEnd_735972 < baseStart_735972 := by decide
  rcases family_descends (prefixWord ++ tailWord_735972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735985 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_735985 : Nat := 118140960795 + 735985 * 2 ^ 59
def prefixEnd_735985 : Nat := 4983230072969 + 3 ^ 40 * 735985 * 2
def baseEnd_735985 : Nat := 251942706332938792668515

theorem tailTrace_735985 : CollatzResearch.WordTrace tailWord_735985 prefixEnd_735985 251942706332938792668515 := by
  unfold tailWord_735985
  simp only [CollatzResearch.WordTrace]
  refine ⟨26843578238659516075921409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17895718825773010717280939 26843578238659516075921409)
  ·
    refine ⟨20132683678994637056941057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26843578238659516075921409 20132683678994637056941057)
    ·
      refine ⟨15099512759245977792705793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20132683678994637056941057 15099512759245977792705793)
      ·
        refine ⟨11324634569434483344529345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15099512759245977792705793 11324634569434483344529345)
        ·
          refine ⟨8493475927075862508397009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11324634569434483344529345 8493475927075862508397009)
          ·
            refine ⟨6370106945306896881297757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493475927075862508397009 6370106945306896881297757)
            ·
              refine ⟨2388790104490086330486659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6370106945306896881297757 2388790104490086330486659)
              ·
                refine ⟨3583185156735129495729989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388790104490086330486659 3583185156735129495729989)
                ·
                  refine ⟨671847216887836780449373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3583185156735129495729989 671847216887836780449373)
                  ·
                    refine ⟨251942706332938792668515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671847216887836780449373 251942706332938792668515)
                    ·
                      rfl

theorem cell22_735985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_735985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_735985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_735985 prefixEnd_735985 := by exact prefixLift 735985
  have htrace : WordTrace (prefixWord ++ tailWord_735985) baseStart_735985 baseEnd_735985 := by
    simpa [prefixWord, tailWord_735985, baseEnd_735985] using wordTrace_append hprefix tailTrace_735985
  have hstable : (prefixWord ++ tailWord_735985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735985).length < 2 ^ (prefixWord ++ tailWord_735985).sum := by decide
  have hdescent : baseEnd_735985 < baseStart_735985 := by decide
  rcases family_descends (prefixWord ++ tailWord_735985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736002 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_736002 : Nat := 118140960795 + 736002 * 2 ^ 59
def prefixEnd_736002 : Nat := 4983230072969 + 3 ^ 40 * 736002 * 2
def baseEnd_736002 : Nat := 251948525780356414993463

theorem tailTrace_736002 : CollatzResearch.WordTrace tailWord_736002 prefixEnd_736002 251948525780356414993463 := by
  unfold tailWord_736002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711049569899481994822565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17896132186398618652860173 6711049569899481994822565)
  ·
    refine ⟨1258321794356152874029231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6711049569899481994822565 1258321794356152874029231)
    ·
      refine ⟨1887482691534229311043847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258321794356152874029231 1887482691534229311043847)
      ·
        refine ⟨2831224037301343966565771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887482691534229311043847 2831224037301343966565771)
        ·
          refine ⟨4246836055952015949848657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831224037301343966565771 4246836055952015949848657)
          ·
            refine ⟨3185127041964011962386493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246836055952015949848657 3185127041964011962386493)
            ·
              refine ⟨1194422640736504485894935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3185127041964011962386493 1194422640736504485894935)
              ·
                refine ⟨1791633961104756728842403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194422640736504485894935 1791633961104756728842403)
                ·
                  refine ⟨2687450941657135093263605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791633961104756728842403 2687450941657135093263605)
                  ·
                    refine ⟨251948525780356414993463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2687450941657135093263605 251948525780356414993463)
                    ·
                      rfl

theorem cell22_736002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_736002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736002 prefixEnd_736002 := by exact prefixLift 736002
  have htrace : WordTrace (prefixWord ++ tailWord_736002) baseStart_736002 baseEnd_736002 := by
    simpa [prefixWord, tailWord_736002, baseEnd_736002] using wordTrace_append hprefix tailTrace_736002
  have hstable : (prefixWord ++ tailWord_736002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736002).length < 2 ^ (prefixWord ++ tailWord_736002).sum := by decide
  have hdescent : baseEnd_736002 < baseStart_736002 := by decide
  rcases family_descends (prefixWord ++ tailWord_736002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736154 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_736154 : Nat := 118140960795 + 736154 * 2 ^ 59
def prefixEnd_736154 : Nat := 4983230072969 + 3 ^ 40 * 736154 * 2
def baseEnd_736154 : Nat := 252000558486678685192997

theorem tailTrace_736154 : CollatzResearch.WordTrace tailWord_736154 prefixEnd_736154 252000558486678685192997 := by
  unfold tailWord_736154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712435543761814484705879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17899828116698171959215677 6712435543761814484705879)
  ·
    refine ⟨10068653315642721727058819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6712435543761814484705879 10068653315642721727058819)
    ·
      refine ⟨15102979973464082590588229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10068653315642721727058819 15102979973464082590588229)
      ·
        refine ⟨2831808745024515485735293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15102979973464082590588229 2831808745024515485735293)
        ·
          refine ⟨1061928279384193307150735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2831808745024515485735293 1061928279384193307150735)
          ·
            refine ⟨1592892419076289960726103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061928279384193307150735 1592892419076289960726103)
            ·
              refine ⟨2389338628614434941089155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592892419076289960726103 2389338628614434941089155)
              ·
                refine ⟨3584007942921652411633733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389338628614434941089155 3584007942921652411633733)
                ·
                  refine ⟨672001489297809827181325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3584007942921652411633733 672001489297809827181325)
                  ·
                    refine ⟨252000558486678685192997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672001489297809827181325 252000558486678685192997)
                    ·
                      rfl

theorem cell22_736154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_736154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736154 prefixEnd_736154 := by exact prefixLift 736154
  have htrace : WordTrace (prefixWord ++ tailWord_736154) baseStart_736154 baseEnd_736154 := by
    simpa [prefixWord, tailWord_736154, baseEnd_736154] using wordTrace_append hprefix tailTrace_736154
  have hstable : (prefixWord ++ tailWord_736154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736154).length < 2 ^ (prefixWord ++ tailWord_736154).sum := by decide
  have hdescent : baseEnd_736154 < baseStart_736154 := by decide
  rcases family_descends (prefixWord ++ tailWord_736154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736212 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_736212 : Nat := 118140960795 + 736212 * 2 ^ 59
def prefixEnd_736212 : Nat := 4983230072969 + 3 ^ 40 * 736212 * 2
def baseEnd_736212 : Nat := 84006804357328622414273

theorem tailTrace_736212 : CollatzResearch.WordTrace tailWord_736212 prefixEnd_736212 84006804357328622414273 := by
  unfold tailWord_736212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425928804418566922217445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17901238405891422562956593 13425928804418566922217445)
  ·
    refine ⟨2517361650828481297915771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13425928804418566922217445 2517361650828481297915771)
    ·
      refine ⟨3776042476242721946873657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517361650828481297915771 3776042476242721946873657)
      ·
        refine ⟨2832031857182041460155243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3776042476242721946873657 2832031857182041460155243)
        ·
          refine ⟨4248047785773062190232865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832031857182041460155243 4248047785773062190232865)
          ·
            refine ⟨3186035839329796642674649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248047785773062190232865 3186035839329796642674649)
            ·
              refine ⟨2389526879497347482005987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186035839329796642674649 2389526879497347482005987)
              ·
                refine ⟨3584290319246021223008981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389526879497347482005987 3584290319246021223008981)
                ·
                  refine ⟨84006804357328622414273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3584290319246021223008981 84006804357328622414273)
                  ·
                    rfl

theorem cell22_736212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_736212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736212 prefixEnd_736212 := by exact prefixLift 736212
  have htrace : WordTrace (prefixWord ++ tailWord_736212) baseStart_736212 baseEnd_736212 := by
    simpa [prefixWord, tailWord_736212, baseEnd_736212] using wordTrace_append hprefix tailTrace_736212
  have hstable : (prefixWord ++ tailWord_736212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736212).length < 2 ^ (prefixWord ++ tailWord_736212).sum := by decide
  have hdescent : baseEnd_736212 < baseStart_736212 := by decide
  rcases family_descends (prefixWord ++ tailWord_736212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736225 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_736225 : Nat := 118140960795 + 736225 * 2 ^ 59
def prefixEnd_736225 : Nat := 4983230072969 + 3 ^ 40 * 736225 * 2
def baseEnd_736225 : Nat := 252024863237658166667779

theorem tailTrace_736225 : CollatzResearch.WordTrace tailWord_736225 prefixEnd_736225 252024863237658166667779 := by
  unfold tailWord_736225
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852331757790037064658129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17901554505193358043105419 26852331757790037064658129)
  ·
    refine ⟨20139248818342527798493597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26852331757790037064658129 20139248818342527798493597)
    ·
      refine ⟨7552218306878447924435099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20139248818342527798493597 7552218306878447924435099)
      ·
        refine ⟨11328327460317671886652649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7552218306878447924435099 11328327460317671886652649)
        ·
          refine ⟨8496245595238253914989487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11328327460317671886652649 8496245595238253914989487)
          ·
            refine ⟨12744368392857380872484231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496245595238253914989487 12744368392857380872484231)
            ·
              refine ⟨19116552589286071308726347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744368392857380872484231 19116552589286071308726347)
              ·
                refine ⟨28674828883929106963089521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19116552589286071308726347 28674828883929106963089521)
                ·
                  refine ⟨21506121662946830222317141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28674828883929106963089521 21506121662946830222317141)
                  ·
                    refine ⟨252024863237658166667779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21506121662946830222317141 252024863237658166667779)
                    ·
                      rfl

theorem cell22_736225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_736225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736225 prefixEnd_736225 := by exact prefixLift 736225
  have htrace : WordTrace (prefixWord ++ tailWord_736225) baseStart_736225 baseEnd_736225 := by
    simpa [prefixWord, tailWord_736225, baseEnd_736225] using wordTrace_append hprefix tailTrace_736225
  have hstable : (prefixWord ++ tailWord_736225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736225).length < 2 ^ (prefixWord ++ tailWord_736225).sum := by decide
  have hdescent : baseEnd_736225 < baseStart_736225 := by decide
  rcases family_descends (prefixWord ++ tailWord_736225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736240 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_736240 : Nat := 118140960795 + 736240 * 2 ^ 59
def prefixEnd_736240 : Nat := 4983230072969 + 3 ^ 40 * 736240 * 2
def baseEnd_736240 : Nat := 84009999348067709180911

theorem tailTrace_736240 : CollatzResearch.WordTrace tailWord_736240 prefixEnd_736240 84009999348067709180911 := by
  unfold tailWord_736240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426439426367847313227087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17901919235157129750969449 13426439426367847313227087)
  ·
    refine ⟨20139659139551770969840631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13426439426367847313227087 20139659139551770969840631)
    ·
      refine ⟨30209488709327656454760947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20139659139551770969840631 30209488709327656454760947)
      ·
        refine ⟨45314233063991484682141421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30209488709327656454760947 45314233063991484682141421)
        ·
          refine ⟨16992837398996806755803033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45314233063991484682141421 16992837398996806755803033)
          ·
            refine ⟨12744628049247605066852275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16992837398996806755803033 12744628049247605066852275)
            ·
              refine ⟨19116942073871407600278413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744628049247605066852275 19116942073871407600278413)
              ·
                refine ⟨7168853277701777850104405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19116942073871407600278413 7168853277701777850104405)
                ·
                  refine ⟨84009999348067709180911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7168853277701777850104405 84009999348067709180911)
                  ·
                    rfl

theorem cell22_736240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_736240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736240 prefixEnd_736240 := by exact prefixLift 736240
  have htrace : WordTrace (prefixWord ++ tailWord_736240) baseStart_736240 baseEnd_736240 := by
    simpa [prefixWord, tailWord_736240, baseEnd_736240] using wordTrace_append hprefix tailTrace_736240
  have hstable : (prefixWord ++ tailWord_736240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736240).length < 2 ^ (prefixWord ++ tailWord_736240).sum := by decide
  have hdescent : baseEnd_736240 < baseStart_736240 := by decide
  rcases family_descends (prefixWord ++ tailWord_736240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736289 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_736289 : Nat := 118140960795 + 736289 * 2 ^ 59
def prefixEnd_736289 : Nat := 4983230072969 + 3 ^ 40 * 736289 * 2
def baseEnd_736289 : Nat := 252046771745583333067583

theorem tailTrace_736289 : CollatzResearch.WordTrace tailWord_736289 prefixEnd_736289 252046771745583333067583 := by
  unfold tailWord_736289
  simp only [CollatzResearch.WordTrace]
  refine ⟨26854666029558175994987921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17903110686372117329991947 26854666029558175994987921)
  ·
    refine ⟨20140999522168631996240941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26854666029558175994987921 20140999522168631996240941)
    ·
      refine ⟨7552874820813236998590353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20140999522168631996240941 7552874820813236998590353)
      ·
        refine ⟨5664656115609927748942765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7552874820813236998590353 5664656115609927748942765)
        ·
          refine ⟨2124246043353722905853537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5664656115609927748942765 2124246043353722905853537)
          ·
            refine ⟨1593184532515292179390153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124246043353722905853537 1593184532515292179390153)
            ·
              refine ⟨1194888399386469134542615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593184532515292179390153 1194888399386469134542615)
              ·
                refine ⟨1792332599079703701813923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194888399386469134542615 1792332599079703701813923)
                ·
                  refine ⟨2688498898619555552720885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792332599079703701813923 2688498898619555552720885)
                  ·
                    refine ⟨252046771745583333067583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2688498898619555552720885 252046771745583333067583)
                    ·
                      rfl

theorem cell22_736289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_736289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736289 prefixEnd_736289 := by exact prefixLift 736289
  have htrace : WordTrace (prefixWord ++ tailWord_736289) baseStart_736289 baseEnd_736289 := by
    simpa [prefixWord, tailWord_736289, baseEnd_736289] using wordTrace_append hprefix tailTrace_736289
  have hstable : (prefixWord ++ tailWord_736289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736289).length < 2 ^ (prefixWord ++ tailWord_736289).sum := by decide
  have hdescent : baseEnd_736289 < baseStart_736289 := by decide
  rcases family_descends (prefixWord ++ tailWord_736289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736308 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_736308 : Nat := 118140960795 + 736308 * 2 ^ 59
def prefixEnd_736308 : Nat := 4983230072969 + 3 ^ 40 * 736308 * 2
def baseEnd_736308 : Nat := 84017758611291205614175

theorem tailTrace_736308 : CollatzResearch.WordTrace tailWord_736308 prefixEnd_736308 84017758611291205614175 := by
  unfold tailWord_736308
  simp only [CollatzResearch.WordTrace]
  refine ⟨13427679508244671119964789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17903572677659561493286385 13427679508244671119964789)
  ·
    refine ⟨1258844953897937917496699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13427679508244671119964789 1258844953897937917496699)
    ·
      refine ⟨1888267430846906876245049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258844953897937917496699 1888267430846906876245049)
      ·
        refine ⟨1416200573135180157183787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888267430846906876245049 1416200573135180157183787)
        ·
          refine ⟨2124300859702770235775681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416200573135180157183787 2124300859702770235775681)
          ·
            refine ⟨1593225644777077676831761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124300859702770235775681 1593225644777077676831761)
            ·
              refine ⟨1194919233582808257623821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593225644777077676831761 1194919233582808257623821)
              ·
                refine ⟨448094712593553096608933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194919233582808257623821 448094712593553096608933)
                ·
                  refine ⟨84017758611291205614175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448094712593553096608933 84017758611291205614175)
                  ·
                    rfl

theorem cell22_736308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_736308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736308 prefixEnd_736308 := by exact prefixLift 736308
  have htrace : WordTrace (prefixWord ++ tailWord_736308) baseStart_736308 baseEnd_736308 := by
    simpa [prefixWord, tailWord_736308, baseEnd_736308] using wordTrace_append hprefix tailTrace_736308
  have hstable : (prefixWord ++ tailWord_736308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736308).length < 2 ^ (prefixWord ++ tailWord_736308).sum := by decide
  have hdescent : baseEnd_736308 < baseStart_736308 := by decide
  rcases family_descends (prefixWord ++ tailWord_736308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736385 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 1, 3]
def baseStart_736385 : Nat := 118140960795 + 736385 * 2 ^ 59
def prefixEnd_736385 : Nat := 4983230072969 + 3 ^ 40 * 736385 * 2
def baseEnd_736385 : Nat := 252079634507471082667289

theorem tailTrace_736385 : CollatzResearch.WordTrace tailWord_736385 prefixEnd_736385 252079634507471082667289 := by
  unfold tailWord_736385
  simp only [CollatzResearch.WordTrace]
  refine ⟨26858167437210384390482609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17905444958140256260321739 26858167437210384390482609)
  ·
    refine ⟨20143625577907788292861957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26858167437210384390482609 20143625577907788292861957)
    ·
      refine ⟨3776929795857710304911617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20143625577907788292861957 3776929795857710304911617)
      ·
        refine ⟨2832697346893282728683713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3776929795857710304911617 2832697346893282728683713)
        ·
          refine ⟨2124523010169962046512785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832697346893282728683713 2124523010169962046512785)
          ·
            refine ⟨1593392257627471534884589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124523010169962046512785 1593392257627471534884589)
            ·
              refine ⟨597522096610301825581721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593392257627471534884589 597522096610301825581721)
              ·
                refine ⟨448141572457726369186291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597522096610301825581721 448141572457726369186291)
                ·
                  refine ⟨672212358686589553779437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448141572457726369186291 672212358686589553779437)
                  ·
                    refine ⟨252079634507471082667289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672212358686589553779437 252079634507471082667289)
                    ·
                      rfl

theorem cell22_736385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_736385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736385 prefixEnd_736385 := by exact prefixLift 736385
  have htrace : WordTrace (prefixWord ++ tailWord_736385) baseStart_736385 baseEnd_736385 := by
    simpa [prefixWord, tailWord_736385, baseEnd_736385] using wordTrace_append hprefix tailTrace_736385
  have hstable : (prefixWord ++ tailWord_736385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736385).length < 2 ^ (prefixWord ++ tailWord_736385).sum := by decide
  have hdescent : baseEnd_736385 < baseStart_736385 := by decide
  rcases family_descends (prefixWord ++ tailWord_736385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736394 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_736394 : Nat := 118140960795 + 736394 * 2 ^ 59
def prefixEnd_736394 : Nat := 4983230072969 + 3 ^ 40 * 736394 * 2
def baseEnd_736394 : Nat := 252082715391398059192261

theorem tailTrace_736394 : CollatzResearch.WordTrace tailWord_736394 prefixEnd_736394 252082715391398059192261 := by
  unfold tailWord_736394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714623923544444731890059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17905663796118519285040157 6714623923544444731890059)
  ·
    refine ⟨10071935885316667097835089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714623923544444731890059 10071935885316667097835089)
    ·
      refine ⟨7553951913987500323376317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10071935885316667097835089 7553951913987500323376317)
      ·
        refine ⟨2832731967745312621266119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7553951913987500323376317 2832731967745312621266119)
        ·
          refine ⟨4249097951617968931899179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832731967745312621266119 4249097951617968931899179)
          ·
            refine ⟨6373646927426953397848769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249097951617968931899179 6373646927426953397848769)
            ·
              refine ⟨4780235195570215048386577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6373646927426953397848769 4780235195570215048386577)
              ·
                refine ⟨3585176396677661286289933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780235195570215048386577 3585176396677661286289933)
                ·
                  refine ⟨1344441148754122982358725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3585176396677661286289933 1344441148754122982358725)
                  ·
                    refine ⟨252082715391398059192261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344441148754122982358725 252082715391398059192261)
                    ·
                      rfl

theorem cell22_736394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_736394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736394 prefixEnd_736394 := by exact prefixLift 736394
  have htrace : WordTrace (prefixWord ++ tailWord_736394) baseStart_736394 baseEnd_736394 := by
    simpa [prefixWord, tailWord_736394, baseEnd_736394] using wordTrace_append hprefix tailTrace_736394
  have hstable : (prefixWord ++ tailWord_736394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736394).length < 2 ^ (prefixWord ++ tailWord_736394).sum := by decide
  have hdescent : baseEnd_736394 < baseStart_736394 := by decide
  rcases family_descends (prefixWord ++ tailWord_736394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
