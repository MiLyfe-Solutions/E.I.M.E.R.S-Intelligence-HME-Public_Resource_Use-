import V185TrunkScan23Chunk0367

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2175848 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2175848 : Nat := 118140960795 + 2175848 * 2 ^ 59
def prefixEnd_2175848 : Nat := 4983230072969 + 3 ^ 40 * 2175848 * 2
def baseEnd_2175848 : Nat := 1117255855124108218393463

theorem tailTrace_2175848 : CollatzResearch.WordTrace tailWord_2175848 prefixEnd_2175848 1117255855124108218393463 := by
  unfold tailWord_2175848
  simp only [CollatzResearch.WordTrace]
  refine ⟨39679848110640888049252099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52906464147521184065669465 39679848110640888049252099)
  ·
    refine ⟨59519772165961332073878149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39679848110640888049252099 59519772165961332073878149)
    ·
      refine ⟨11159957281117749763852153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59519772165961332073878149 11159957281117749763852153)
      ·
        refine ⟨8369967960838312322889115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11159957281117749763852153 8369967960838312322889115)
        ·
          refine ⟨12554951941257468484333673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8369967960838312322889115 12554951941257468484333673)
          ·
            refine ⟨9416213955943101363250255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12554951941257468484333673 9416213955943101363250255)
            ·
              refine ⟨14124320933914652044875383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9416213955943101363250255 14124320933914652044875383)
              ·
                refine ⟨21186481400871978067313075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14124320933914652044875383 21186481400871978067313075)
                ·
                  refine ⟨31779722101307967100969613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21186481400871978067313075 31779722101307967100969613)
                  ·
                    refine ⟨11917395787990487662863605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31779722101307967100969613 11917395787990487662863605)
                    ·
                      refine ⟨1117255855124108218393463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11917395787990487662863605 1117255855124108218393463)
                      ·
                        rfl

theorem cell23_2175848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2175848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175848 prefixEnd_2175848 := by exact prefixLift 2175848
  have htrace : WordTrace (prefixWord ++ tailWord_2175848) baseStart_2175848 baseEnd_2175848 := by
    simpa [prefixWord, tailWord_2175848, baseEnd_2175848] using wordTrace_append hprefix tailTrace_2175848
  have hstable : (prefixWord ++ tailWord_2175848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175848).length < 2 ^ (prefixWord ++ tailWord_2175848).sum := by decide
  have hdescent : baseEnd_2175848 < baseStart_2175848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175851 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 9]
def baseStart_2175851 : Nat := 118140960795 + 2175851 * 2 ^ 59
def prefixEnd_2175851 : Nat := 4983230072969 + 3 ^ 40 * 2175851 * 2
def baseEnd_2175851 : Nat := 124139710618452411850661

theorem tailTrace_2175851 : CollatzResearch.WordTrace tailWord_2175851 prefixEnd_2175851 124139710618452411850661 := by
  unfold tailWord_2175851
  simp only [CollatzResearch.WordTrace]
  refine ⟨79359805640270907610863407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52906537093513938407242271 79359805640270907610863407)
  ·
    refine ⟨119039708460406361416295111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79359805640270907610863407 119039708460406361416295111)
    ·
      refine ⟨178559562690609542124442667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119039708460406361416295111 178559562690609542124442667)
      ·
        refine ⟨267839344035914313186664001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178559562690609542124442667 267839344035914313186664001)
        ·
          refine ⟨200879508026935734889998001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267839344035914313186664001 200879508026935734889998001)
          ·
            refine ⟨150659631020201801167498501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200879508026935734889998001 150659631020201801167498501)
            ·
              refine ⟨28248680816287837718905969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150659631020201801167498501 28248680816287837718905969)
              ·
                refine ⟨21186510612215878289179477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28248680816287837718905969 21186510612215878289179477)
                ·
                  refine ⟨124139710618452411850661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21186510612215878289179477 124139710618452411850661)
                  ·
                    rfl

theorem cell23_2175851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 9].length) (baseStart_2175851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175851 prefixEnd_2175851 := by exact prefixLift 2175851
  have htrace : WordTrace (prefixWord ++ tailWord_2175851) baseStart_2175851 baseEnd_2175851 := by
    simpa [prefixWord, tailWord_2175851, baseEnd_2175851] using wordTrace_append hprefix tailTrace_2175851
  have hstable : (prefixWord ++ tailWord_2175851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175851).length < 2 ^ (prefixWord ++ tailWord_2175851).sum := by decide
  have hdescent : baseEnd_2175851 < baseStart_2175851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175858 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2175858 : Nat := 118140960795 + 2175858 * 2 ^ 59
def prefixEnd_2175858 : Nat := 4983230072969 + 3 ^ 40 * 2175858 * 2
def baseEnd_2175858 : Nat := 1117260989930653179268417

theorem tailTrace_2175858 : CollatzResearch.WordTrace tailWord_2175858 prefixEnd_2175858 1117260989930653179268417 := by
  unfold tailWord_2175858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19840015237811386951592057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52906707300830365204245485 19840015237811386951592057)
  ·
    refine ⟨14880011428358540213694043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19840015237811386951592057 14880011428358540213694043)
    ·
      refine ⟨22320017142537810320541065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14880011428358540213694043 22320017142537810320541065)
      ·
        refine ⟨16740012856903357740405799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22320017142537810320541065 16740012856903357740405799)
        ·
          refine ⟨25110019285355036610608699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16740012856903357740405799 25110019285355036610608699)
          ·
            refine ⟨37665028928032554915913049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25110019285355036610608699 37665028928032554915913049)
            ·
              refine ⟨28248771696024416186934787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37665028928032554915913049 28248771696024416186934787)
              ·
                refine ⟨42373157544036624280402181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28248771696024416186934787 42373157544036624280402181)
                ·
                  refine ⟨7944967039506867052575409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42373157544036624280402181 7944967039506867052575409)
                  ·
                    refine ⟨5958725279630150289431557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7944967039506867052575409 5958725279630150289431557)
                    ·
                      refine ⟨1117260989930653179268417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5958725279630150289431557 1117260989930653179268417)
                      ·
                        rfl

theorem cell23_2175858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2175858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175858 prefixEnd_2175858 := by exact prefixLift 2175858
  have htrace : WordTrace (prefixWord ++ tailWord_2175858) baseStart_2175858 baseEnd_2175858 := by
    simpa [prefixWord, tailWord_2175858, baseEnd_2175858] using wordTrace_append hprefix tailTrace_2175858
  have hstable : (prefixWord ++ tailWord_2175858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175858).length < 2 ^ (prefixWord ++ tailWord_2175858).sum := by decide
  have hdescent : baseEnd_2175858 < baseStart_2175858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175879 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_2175879 : Nat := 118140960795 + 2175879 * 2 ^ 59
def prefixEnd_2175879 : Nat := 4983230072969 + 3 ^ 40 * 2175879 * 2
def baseEnd_2175879 : Nat := 1117271773024397597105821

theorem tailTrace_2175879 : CollatzResearch.WordTrace tailWord_2175879 prefixEnd_2175879 1117271773024397597105821 := by
  unfold tailWord_2175879
  simp only [CollatzResearch.WordTrace]
  refine ⟨79360826884169468392882691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52907217922779645595255127 79360826884169468392882691)
  ·
    refine ⟨119041240326254202589324037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79360826884169468392882691 119041240326254202589324037)
    ·
      refine ⟨22320232561172662985498257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119041240326254202589324037 22320232561172662985498257)
      ·
        refine ⟨16740174420879497239123693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22320232561172662985498257 16740174420879497239123693)
        ·
          refine ⟨6277565407829811464671385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16740174420879497239123693 6277565407829811464671385)
          ·
            refine ⟨4708174055872358598503539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6277565407829811464671385 4708174055872358598503539)
            ·
              refine ⟨7062261083808537897755309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708174055872358598503539 7062261083808537897755309)
              ·
                refine ⟨2648347906428201711658241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7062261083808537897755309 2648347906428201711658241)
                ·
                  refine ⟨1986260929821151283743681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2648347906428201711658241 1986260929821151283743681)
                  ·
                    refine ⟨1489695697365863462807761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986260929821151283743681 1489695697365863462807761)
                    ·
                      refine ⟨1117271773024397597105821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489695697365863462807761 1117271773024397597105821)
                      ·
                        rfl

theorem cell23_2175879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_2175879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175879 prefixEnd_2175879 := by exact prefixLift 2175879
  have htrace : WordTrace (prefixWord ++ tailWord_2175879) baseStart_2175879 baseEnd_2175879 := by
    simpa [prefixWord, tailWord_2175879, baseEnd_2175879] using wordTrace_append hprefix tailTrace_2175879
  have hstable : (prefixWord ++ tailWord_2175879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175879).length < 2 ^ (prefixWord ++ tailWord_2175879).sum := by decide
  have hdescent : baseEnd_2175879 < baseStart_2175879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175908 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2175908 : Nat := 118140960795 + 2175908 * 2 ^ 59
def prefixEnd_2175908 : Nat := 4983230072969 + 3 ^ 40 * 2175908 * 2
def baseEnd_2175908 : Nat := 1117286663963377983643187

theorem tailTrace_2175908 : CollatzResearch.WordTrace tailWord_2175908 prefixEnd_2175908 1117286663963377983643187 := by
  unfold tailWord_2175908
  simp only [CollatzResearch.WordTrace]
  refine ⟨39680942300532203172844189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52907923067376270897125585 39680942300532203172844189)
  ·
    refine ⟨14880353362699576189816571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39680942300532203172844189 14880353362699576189816571)
    ·
      refine ⟨22320530044049364284724857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14880353362699576189816571 22320530044049364284724857)
      ·
        refine ⟨16740397533037023213543643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22320530044049364284724857 16740397533037023213543643)
        ·
          refine ⟨25110596299555534820315465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16740397533037023213543643 25110596299555534820315465)
          ·
            refine ⟨18832947224666651115236599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25110596299555534820315465 18832947224666651115236599)
            ·
              refine ⟨28249420836999976672854899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18832947224666651115236599 28249420836999976672854899)
              ·
                refine ⟨42374131255499965009282349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28249420836999976672854899 42374131255499965009282349)
                ·
                  refine ⟨15890299220812486878480881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42374131255499965009282349 15890299220812486878480881)
                  ·
                    refine ⟨11917724415609365158860661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15890299220812486878480881 11917724415609365158860661)
                    ·
                      refine ⟨1117286663963377983643187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11917724415609365158860661 1117286663963377983643187)
                      ·
                        rfl

theorem cell23_2175908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2175908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175908 prefixEnd_2175908 := by exact prefixLift 2175908
  have htrace : WordTrace (prefixWord ++ tailWord_2175908) baseStart_2175908 baseEnd_2175908 := by
    simpa [prefixWord, tailWord_2175908, baseEnd_2175908] using wordTrace_append hprefix tailTrace_2175908
  have hstable : (prefixWord ++ tailWord_2175908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175908).length < 2 ^ (prefixWord ++ tailWord_2175908).sum := by decide
  have hdescent : baseEnd_2175908 < baseStart_2175908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175926 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2175926 : Nat := 118140960795 + 2175926 * 2 ^ 59
def prefixEnd_2175926 : Nat := 4983230072969 + 3 ^ 40 * 2175926 * 2
def baseEnd_2175926 : Nat := 1117295906615158913218105

theorem tailTrace_2175926 : CollatzResearch.WordTrace tailWord_2175926 prefixEnd_2175926 1117295906615158913218105 := by
  unfold tailWord_2175926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960158819687449713740227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52908360743332796946562421 4960158819687449713740227)
  ·
    refine ⟨7440238229531174570610341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4960158819687449713740227 7440238229531174570610341)
    ·
      refine ⟨1395044668037095231989439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7440238229531174570610341 1395044668037095231989439)
      ·
        refine ⟨2092567002055642847984159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395044668037095231989439 2092567002055642847984159)
        ·
          refine ⟨3138850503083464271976239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092567002055642847984159 3138850503083464271976239)
          ·
            refine ⟨4708275754625196407964359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138850503083464271976239 4708275754625196407964359)
            ·
              refine ⟨7062413631937794611946539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708275754625196407964359 7062413631937794611946539)
              ·
                refine ⟨10593620447906691917919809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7062413631937794611946539 10593620447906691917919809)
                ·
                  refine ⟨7945215335930018938439857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10593620447906691917919809 7945215335930018938439857)
                  ·
                    refine ⟨5958911501947514203829893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7945215335930018938439857 5958911501947514203829893)
                    ·
                      refine ⟨1117295906615158913218105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5958911501947514203829893 1117295906615158913218105)
                      ·
                        rfl

theorem cell23_2175926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2175926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175926 prefixEnd_2175926 := by exact prefixLift 2175926
  have htrace : WordTrace (prefixWord ++ tailWord_2175926) baseStart_2175926 baseEnd_2175926 := by
    simpa [prefixWord, tailWord_2175926, baseEnd_2175926] using wordTrace_append hprefix tailTrace_2175926
  have hstable : (prefixWord ++ tailWord_2175926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175926).length < 2 ^ (prefixWord ++ tailWord_2175926).sum := by decide
  have hdescent : baseEnd_2175926 < baseStart_2175926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175965 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2175965 : Nat := 118140960795 + 2175965 * 2 ^ 59
def prefixEnd_2175965 : Nat := 4983230072969 + 3 ^ 40 * 2175965 * 2
def baseEnd_2175965 : Nat := 1117315932360684260630425

theorem tailTrace_2175965 : CollatzResearch.WordTrace tailWord_2175965 prefixEnd_2175965 1117315932360684260630425 := by
  unfold tailWord_2175965
  simp only [CollatzResearch.WordTrace]
  refine ⟨79363963561857905080513349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52909309041238603387008899 79363963561857905080513349)
  ·
    refine ⟨14880743167848357202596253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79363963561857905080513349 14880743167848357202596253)
    ·
      refine ⟨5580278687943133950973595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14880743167848357202596253 5580278687943133950973595)
      ·
        refine ⟨8370418031914700926460393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5580278687943133950973595 8370418031914700926460393)
        ·
          refine ⟨6277813523936025694845295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8370418031914700926460393 6277813523936025694845295)
          ·
            refine ⟨9416720285904038542267943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277813523936025694845295 9416720285904038542267943)
            ·
              refine ⟨14125080428856057813401915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9416720285904038542267943 14125080428856057813401915)
              ·
                refine ⟨21187620643284086720102873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14125080428856057813401915 21187620643284086720102873)
                ·
                  refine ⟨15890715482463065040077155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21187620643284086720102873 15890715482463065040077155)
                  ·
                    refine ⟨23836073223694597560115733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15890715482463065040077155 23836073223694597560115733)
                    ·
                      refine ⟨1117315932360684260630425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23836073223694597560115733 1117315932360684260630425)
                      ·
                        rfl

theorem cell23_2175965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2175965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175965 prefixEnd_2175965 := by exact prefixLift 2175965
  have htrace : WordTrace (prefixWord ++ tailWord_2175965) baseStart_2175965 baseEnd_2175965 := by
    simpa [prefixWord, tailWord_2175965, baseEnd_2175965] using wordTrace_append hprefix tailTrace_2175965
  have hstable : (prefixWord ++ tailWord_2175965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175965).length < 2 ^ (prefixWord ++ tailWord_2175965).sum := by decide
  have hdescent : baseEnd_2175965 < baseStart_2175965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175975 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 8]
def baseStart_2175975 : Nat := 118140960795 + 2175975 * 2 ^ 59
def prefixEnd_2175975 : Nat := 4983230072969 + 3 ^ 40 * 2175975 * 2
def baseEnd_2175975 : Nat := 124146785240803246833931

theorem tailTrace_2175975 : CollatzResearch.WordTrace tailWord_2175975 prefixEnd_2175975 124146785240803246833931 := by
  unfold tailWord_2175975
  simp only [CollatzResearch.WordTrace]
  refine ⟨79364328291821676788377379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52909552194547784525584919 79364328291821676788377379)
  ·
    refine ⟨119046492437732515182566069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79364328291821676788377379 119046492437732515182566069)
    ·
      refine ⟨11160608666037423298365569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119046492437732515182566069 11160608666037423298365569)
      ·
        refine ⟨8370456499528067473774177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11160608666037423298365569 8370456499528067473774177)
        ·
          refine ⟨6277842374646050605330633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8370456499528067473774177 6277842374646050605330633)
          ·
            refine ⟨4708381780984537953997975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6277842374646050605330633 4708381780984537953997975)
            ·
              refine ⟨7062572671476806930996963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708381780984537953997975 7062572671476806930996963)
              ·
                refine ⟨10593859007215210396495445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7062572671476806930996963 10593859007215210396495445)
                ·
                  refine ⟨124146785240803246833931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10593859007215210396495445 124146785240803246833931)
                  ·
                    rfl

theorem cell23_2175975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 8].length) (baseStart_2175975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175975 prefixEnd_2175975 := by exact prefixLift 2175975
  have htrace : WordTrace (prefixWord ++ tailWord_2175975) baseStart_2175975 baseEnd_2175975 := by
    simpa [prefixWord, tailWord_2175975, baseEnd_2175975] using wordTrace_append hprefix tailTrace_2175975
  have hstable : (prefixWord ++ tailWord_2175975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175975).length < 2 ^ (prefixWord ++ tailWord_2175975).sum := by decide
  have hdescent : baseEnd_2175975 < baseStart_2175975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176012 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_2176012 : Nat := 118140960795 + 2176012 * 2 ^ 59
def prefixEnd_2176012 : Nat := 4983230072969 + 3 ^ 40 * 2176012 * 2
def baseEnd_2176012 : Nat := 1117340065951445576742709

theorem tailTrace_2176012 : CollatzResearch.WordTrace tailWord_2176012 prefixEnd_2176012 1117340065951445576742709 := by
  unfold tailWord_2176012
  simp only [CollatzResearch.WordTrace]
  refine ⟨39682838896343816053737145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52910451861791754738316193 39682838896343816053737145)
  ·
    refine ⟨29762129172257862040302859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39682838896343816053737145 29762129172257862040302859)
    ·
      refine ⟨44643193758386793060454289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29762129172257862040302859 44643193758386793060454289)
      ·
        refine ⟨33482395318790094795340717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44643193758386793060454289 33482395318790094795340717)
        ·
          refine ⟨12555898244546285548252769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33482395318790094795340717 12555898244546285548252769)
          ·
            refine ⟨9416923683409714161189577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12555898244546285548252769 9416923683409714161189577)
            ·
              refine ⟨7062692762557285620892183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9416923683409714161189577 7062692762557285620892183)
              ·
                refine ⟨10594039143835928431338275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7062692762557285620892183 10594039143835928431338275)
                ·
                  refine ⟨15891058715753892647007413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10594039143835928431338275 15891058715753892647007413)
                  ·
                    refine ⟨1489786754601927435656945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15891058715753892647007413 1489786754601927435656945)
                    ·
                      refine ⟨1117340065951445576742709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489786754601927435656945 1117340065951445576742709)
                      ·
                        rfl

theorem cell23_2176012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_2176012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176012 prefixEnd_2176012 := by exact prefixLift 2176012
  have htrace : WordTrace (prefixWord ++ tailWord_2176012) baseStart_2176012 baseEnd_2176012 := by
    simpa [prefixWord, tailWord_2176012, baseEnd_2176012] using wordTrace_append hprefix tailTrace_2176012
  have hstable : (prefixWord ++ tailWord_2176012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176012).length < 2 ^ (prefixWord ++ tailWord_2176012).sum := by decide
  have hdescent : baseEnd_2176012 < baseStart_2176012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176036 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2176036 : Nat := 118140960795 + 2176036 * 2 ^ 59
def prefixEnd_2176036 : Nat := 4983230072969 + 3 ^ 40 * 2176036 * 2
def baseEnd_2176036 : Nat := 1117352389487153482842599

theorem tailTrace_2176036 : CollatzResearch.WordTrace tailWord_2176036 prefixEnd_2176036 1117352389487153482842599 := by
  unfold tailWord_2176036
  simp only [CollatzResearch.WordTrace]
  refine ⟨39683276572300342103173981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52911035429733789470898641 39683276572300342103173981)
  ·
    refine ⟨14881228714612628288690243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39683276572300342103173981 14881228714612628288690243)
    ·
      refine ⟨22321843071918942433035365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14881228714612628288690243 22321843071918942433035365)
      ·
        refine ⟨4185345575984801706194131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22321843071918942433035365 4185345575984801706194131)
        ·
          refine ⟨6278018363977202559291197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185345575984801706194131 6278018363977202559291197)
          ·
            refine ⟨2354256886491450959734199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6278018363977202559291197 2354256886491450959734199)
            ·
              refine ⟨3531385329737176439601299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354256886491450959734199 3531385329737176439601299)
              ·
                refine ⟨5297077994605764659401949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531385329737176439601299 5297077994605764659401949)
                ·
                  refine ⟨1986404247977161747275731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5297077994605764659401949 1986404247977161747275731)
                  ·
                    refine ⟨2979606371965742620913597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1986404247977161747275731 2979606371965742620913597)
                    ·
                      refine ⟨1117352389487153482842599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2979606371965742620913597 1117352389487153482842599)
                      ·
                        rfl

theorem cell23_2176036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2176036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176036 prefixEnd_2176036 := by exact prefixLift 2176036
  have htrace : WordTrace (prefixWord ++ tailWord_2176036) baseStart_2176036 baseEnd_2176036 := by
    simpa [prefixWord, tailWord_2176036, baseEnd_2176036] using wordTrace_append hprefix tailTrace_2176036
  have hstable : (prefixWord ++ tailWord_2176036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176036).length < 2 ^ (prefixWord ++ tailWord_2176036).sum := by decide
  have hdescent : baseEnd_2176036 < baseStart_2176036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176055 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_2176055 : Nat := 118140960795 + 2176055 * 2 ^ 59
def prefixEnd_2176055 : Nat := 4983230072969 + 3 ^ 40 * 2176055 * 2
def baseEnd_2176055 : Nat := 1117362145619588908505011

theorem tailTrace_2176055 : CollatzResearch.WordTrace tailWord_2176055 prefixEnd_2176055 1117362145619588908505011 := by
  unfold tailWord_2176055
  simp only [CollatzResearch.WordTrace]
  refine ⟨79367246131531850451289619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52911497421021233634193079 79367246131531850451289619)
  ·
    refine ⟨119050869197297775676934429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79367246131531850451289619 119050869197297775676934429)
    ·
      refine ⟨44644075948986665878850411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119050869197297775676934429 44644075948986665878850411)
      ·
        refine ⟨66966113923479998818275617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44644075948986665878850411 66966113923479998818275617)
        ·
          refine ⟨50224585442609999113706713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66966113923479998818275617 50224585442609999113706713)
          ·
            refine ⟨37668439081957499335280035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50224585442609999113706713 37668439081957499335280035)
            ·
              refine ⟨56502658622936249002920053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37668439081957499335280035 56502658622936249002920053)
              ·
                refine ⟨5297124245900273344023755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56502658622936249002920053 5297124245900273344023755)
                ·
                  refine ⟨7945686368850410016035633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297124245900273344023755 7945686368850410016035633)
                  ·
                    refine ⟨5959264776637807512026725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7945686368850410016035633 5959264776637807512026725)
                    ·
                      refine ⟨1117362145619588908505011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5959264776637807512026725 1117362145619588908505011)
                      ·
                        rfl

theorem cell23_2176055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_2176055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176055 prefixEnd_2176055 := by exact prefixLift 2176055
  have htrace : WordTrace (prefixWord ++ tailWord_2176055) baseStart_2176055 baseEnd_2176055 := by
    simpa [prefixWord, tailWord_2176055, baseEnd_2176055] using wordTrace_append hprefix tailTrace_2176055
  have hstable : (prefixWord ++ tailWord_2176055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176055).length < 2 ^ (prefixWord ++ tailWord_2176055).sum := by decide
  have hdescent : baseEnd_2176055 < baseStart_2176055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176076 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2176076 : Nat := 118140960795 + 2176076 * 2 ^ 59
def prefixEnd_2176076 : Nat := 4983230072969 + 3 ^ 40 * 2176076 * 2
def baseEnd_2176076 : Nat := 1117372928713333326342415

theorem tailTrace_2176076 : CollatzResearch.WordTrace tailWord_2176076 prefixEnd_2176076 1117372928713333326342415 := by
  unfold tailWord_2176076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39684006032227885518902041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52912008042970514025202721 39684006032227885518902041)
  ·
    refine ⟨29763004524170914139176531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39684006032227885518902041 29763004524170914139176531)
    ·
      refine ⟨44644506786256371208764797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29763004524170914139176531 44644506786256371208764797)
      ·
        refine ⟨16741690044846139203286799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44644506786256371208764797 16741690044846139203286799)
        ·
          refine ⟨25112535067269208804930199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16741690044846139203286799 25112535067269208804930199)
          ·
            refine ⟨37668802600903813207395299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25112535067269208804930199 37668802600903813207395299)
            ·
              refine ⟨56503203901355719811092949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37668802600903813207395299 56503203901355719811092949)
              ·
                refine ⟨1324293841438024683072491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56503203901355719811092949 1324293841438024683072491)
                ·
                  refine ⟨1986440762157037024608737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324293841438024683072491 1986440762157037024608737)
                  ·
                    refine ⟨1489830571617777768456553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986440762157037024608737 1489830571617777768456553)
                    ·
                      refine ⟨1117372928713333326342415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489830571617777768456553 1117372928713333326342415)
                      ·
                        rfl

theorem cell23_2176076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2176076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176076 prefixEnd_2176076 := by exact prefixLift 2176076
  have htrace : WordTrace (prefixWord ++ tailWord_2176076) baseStart_2176076 baseEnd_2176076 := by
    simpa [prefixWord, tailWord_2176076, baseEnd_2176076] using wordTrace_append hprefix tailTrace_2176076
  have hstable : (prefixWord ++ tailWord_2176076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176076).length < 2 ^ (prefixWord ++ tailWord_2176076).sum := by decide
  have hdescent : baseEnd_2176076 < baseStart_2176076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176092 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2176092 : Nat := 118140960795 + 2176092 * 2 ^ 59
def prefixEnd_2176092 : Nat := 4983230072969 + 3 ^ 40 * 2176092 * 2
def baseEnd_2176092 : Nat := 1117381144403805263742341

theorem tailTrace_2176092 : CollatzResearch.WordTrace tailWord_2176092 prefixEnd_2176092 1117381144403805263742341 := by
  unfold tailWord_2176092
  simp only [CollatzResearch.WordTrace]
  refine ⟨39684297816198902885193265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52912397088265203846924353 39684297816198902885193265)
  ·
    refine ⟨29763223362149177163894949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39684297816198902885193265 29763223362149177163894949)
    ·
      refine ⟨5580604380402970718230303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29763223362149177163894949 5580604380402970718230303)
      ·
        refine ⟨8370906570604456077345455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5580604380402970718230303 8370906570604456077345455)
        ·
          refine ⟨12556359855906684116018183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8370906570604456077345455 12556359855906684116018183)
          ·
            refine ⟨18834539783860026174027275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12556359855906684116018183 18834539783860026174027275)
            ·
              refine ⟨28251809675790039261040913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18834539783860026174027275 28251809675790039261040913)
              ·
                refine ⟨21188857256842529445780685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28251809675790039261040913 21188857256842529445780685)
                ·
                  refine ⟨7945821471315948542167757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21188857256842529445780685 7945821471315948542167757)
                  ·
                    refine ⟨2979683051743480703312909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945821471315948542167757 2979683051743480703312909)
                    ·
                      refine ⟨1117381144403805263742341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2979683051743480703312909 1117381144403805263742341)
                      ·
                        rfl

theorem cell23_2176092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2176092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176092 prefixEnd_2176092 := by exact prefixLift 2176092
  have htrace : WordTrace (prefixWord ++ tailWord_2176092) baseStart_2176092 baseEnd_2176092 := by
    simpa [prefixWord, tailWord_2176092, baseEnd_2176092] using wordTrace_append hprefix tailTrace_2176092
  have hstable : (prefixWord ++ tailWord_2176092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176092).length < 2 ^ (prefixWord ++ tailWord_2176092).sum := by decide
  have hdescent : baseEnd_2176092 < baseStart_2176092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176109 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2176109 : Nat := 118140960795 + 2176109 * 2 ^ 59
def prefixEnd_2176109 : Nat := 4983230072969 + 3 ^ 40 * 2176109 * 2
def baseEnd_2176109 : Nat := 1117389873574931697229763

theorem tailTrace_2176109 : CollatzResearch.WordTrace tailWord_2176109 prefixEnd_2176109 1117389873574931697229763 := by
  unfold tailWord_2176109
  simp only [CollatzResearch.WordTrace]
  refine ⟨79369215673336217673755381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52912810448890811782503587 79369215673336217673755381)
  ·
    refine ⟨7440863969375270406914567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79369215673336217673755381 7440863969375270406914567)
    ·
      refine ⟨11161295954062905610371851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7440863969375270406914567 11161295954062905610371851)
      ·
        refine ⟨16741943931094358415557777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11161295954062905610371851 16741943931094358415557777)
        ·
          refine ⟨12556457948320768811668333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16741943931094358415557777 12556457948320768811668333)
          ·
            refine ⟨4708671730620288304375625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12556457948320768811668333 4708671730620288304375625)
            ·
              refine ⟨3531503797965216228281719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4708671730620288304375625 3531503797965216228281719)
              ·
                refine ⟨5297255696947824342422579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531503797965216228281719 5297255696947824342422579)
                ·
                  refine ⟨7945883545421736513633869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297255696947824342422579 7945883545421736513633869)
                  ·
                    refine ⟨2979706329533151192612701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945883545421736513633869 2979706329533151192612701)
                    ·
                      refine ⟨1117389873574931697229763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2979706329533151192612701 1117389873574931697229763)
                      ·
                        rfl

theorem cell23_2176109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2176109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176109 prefixEnd_2176109 := by exact prefixLift 2176109
  have htrace : WordTrace (prefixWord ++ tailWord_2176109) baseStart_2176109 baseEnd_2176109 := by
    simpa [prefixWord, tailWord_2176109, baseEnd_2176109] using wordTrace_append hprefix tailTrace_2176109
  have hstable : (prefixWord ++ tailWord_2176109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176109).length < 2 ^ (prefixWord ++ tailWord_2176109).sum := by decide
  have hdescent : baseEnd_2176109 < baseStart_2176109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176119 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_2176119 : Nat := 118140960795 + 2176119 * 2 ^ 59
def prefixEnd_2176119 : Nat := 4983230072969 + 3 ^ 40 * 2176119 * 2
def baseEnd_2176119 : Nat := 1117395008381476658104717

theorem tailTrace_2176119 : CollatzResearch.WordTrace tailWord_2176119 prefixEnd_2176119 1117395008381476658104717 := by
  unfold tailWord_2176119
  simp only [CollatzResearch.WordTrace]
  refine ⟨79369580403299989381619411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52913053602199992921079607 79369580403299989381619411)
  ·
    refine ⟨119054370604949984072429117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79369580403299989381619411 119054370604949984072429117)
    ·
      refine ⟨44645388976856244027160919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119054370604949984072429117 44645388976856244027160919)
      ·
        refine ⟨66968083465284366040741379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44645388976856244027160919 66968083465284366040741379)
        ·
          refine ⟨100452125197926549061112069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66968083465284366040741379 100452125197926549061112069)
          ·
            refine ⟨18834773474611227948958513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100452125197926549061112069 18834773474611227948958513)
            ·
              refine ⟨14126080105958420961718885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18834773474611227948958513 14126080105958420961718885)
              ·
                refine ⟨2648640019867203930322291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14126080105958420961718885 2648640019867203930322291)
                ·
                  refine ⟨3972960029800805895483437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648640019867203930322291 3972960029800805895483437)
                  ·
                    refine ⟨1489860011175302210806289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3972960029800805895483437 1489860011175302210806289)
                    ·
                      refine ⟨1117395008381476658104717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489860011175302210806289 1117395008381476658104717)
                      ·
                        rfl

theorem cell23_2176119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_2176119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176119 prefixEnd_2176119 := by exact prefixLift 2176119
  have htrace : WordTrace (prefixWord ++ tailWord_2176119) baseStart_2176119 baseEnd_2176119 := by
    simpa [prefixWord, tailWord_2176119, baseEnd_2176119] using wordTrace_append hprefix tailTrace_2176119
  have hstable : (prefixWord ++ tailWord_2176119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176119).length < 2 ^ (prefixWord ++ tailWord_2176119).sum := by decide
  have hdescent : baseEnd_2176119 < baseStart_2176119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176125 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2176125 : Nat := 118140960795 + 2176125 * 2 ^ 59
def prefixEnd_2176125 : Nat := 4983230072969 + 3 ^ 40 * 2176125 * 2
def baseEnd_2176125 : Nat := 372466029755134544876563

theorem tailTrace_2176125 : CollatzResearch.WordTrace tailWord_2176125 prefixEnd_2176125 372466029755134544876563 := by
  unfold tailWord_2176125
  simp only [CollatzResearch.WordTrace]
  refine ⟨79369799241278252406337829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52913199494185501604225219 79369799241278252406337829)
  ·
    refine ⟨14881837357739672326188343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79369799241278252406337829 14881837357739672326188343)
    ·
      refine ⟨22322756036609508489282515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14881837357739672326188343 22322756036609508489282515)
      ·
        refine ⟨33484134054914262733923773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22322756036609508489282515 33484134054914262733923773)
        ·
          refine ⟨12556550270592848525221415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33484134054914262733923773 12556550270592848525221415)
          ·
            refine ⟨18834825405889272787832123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12556550270592848525221415 18834825405889272787832123)
            ·
              refine ⟨28252238108833909181748185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18834825405889272787832123 28252238108833909181748185)
              ·
                refine ⟨21189178581625431886311139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28252238108833909181748185 21189178581625431886311139)
                ·
                  refine ⟨31783767872438147829466709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21189178581625431886311139 31783767872438147829466709)
                  ·
                    refine ⟨372466029755134544876563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31783767872438147829466709 372466029755134544876563)
                    ·
                      rfl

theorem cell23_2176125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2176125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176125 prefixEnd_2176125 := by exact prefixLift 2176125
  have htrace : WordTrace (prefixWord ++ tailWord_2176125) baseStart_2176125 baseEnd_2176125 := by
    simpa [prefixWord, tailWord_2176125, baseEnd_2176125] using wordTrace_append hprefix tailTrace_2176125
  have hstable : (prefixWord ++ tailWord_2176125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176125).length < 2 ^ (prefixWord ++ tailWord_2176125).sum := by decide
  have hdescent : baseEnd_2176125 < baseStart_2176125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176135 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2176135 : Nat := 118140960795 + 2176135 * 2 ^ 59
def prefixEnd_2176135 : Nat := 4983230072969 + 3 ^ 40 * 2176135 * 2
def baseEnd_2176135 : Nat := 1117403224071948595504643

theorem tailTrace_2176135 : CollatzResearch.WordTrace tailWord_2176135 prefixEnd_2176135 1117403224071948595504643 := by
  unfold tailWord_2176135
  simp only [CollatzResearch.WordTrace]
  refine ⟨79370163971242024114201859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52913442647494682742801239 79370163971242024114201859)
  ·
    refine ⟨119055245956863036171302789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79370163971242024114201859 119055245956863036171302789)
    ·
      refine ⟨22322858616911819282119273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119055245956863036171302789 22322858616911819282119273)
      ·
        refine ⟨16742143962683864461589455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22322858616911819282119273 16742143962683864461589455)
        ·
          refine ⟨25113215944025796692384183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16742143962683864461589455 25113215944025796692384183)
          ·
            refine ⟨37669823916038695038576275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25113215944025796692384183 37669823916038695038576275)
            ·
              refine ⟨56504735874058042557864413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37669823916038695038576275 56504735874058042557864413)
              ·
                refine ⟨21189275952771765959199155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56504735874058042557864413 21189275952771765959199155)
                ·
                  refine ⟨31783913929157648938798733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21189275952771765959199155 31783913929157648938798733)
                  ·
                    refine ⟨11918967723434118352049525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31783913929157648938798733 11918967723434118352049525)
                    ·
                      refine ⟨1117403224071948595504643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11918967723434118352049525 1117403224071948595504643)
                      ·
                        rfl

theorem cell23_2176135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2176135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176135 prefixEnd_2176135 := by exact prefixLift 2176135
  have htrace : WordTrace (prefixWord ++ tailWord_2176135) baseStart_2176135 baseEnd_2176135 := by
    simpa [prefixWord, tailWord_2176135, baseEnd_2176135] using wordTrace_append hprefix tailTrace_2176135
  have hstable : (prefixWord ++ tailWord_2176135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176135).length < 2 ^ (prefixWord ++ tailWord_2176135).sum := by decide
  have hdescent : baseEnd_2176135 < baseStart_2176135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176142 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2176142 : Nat := 118140960795 + 2176142 * 2 ^ 59
def prefixEnd_2176142 : Nat := 4983230072969 + 3 ^ 40 * 2176142 * 2
def baseEnd_2176142 : Nat := 372468939478843356039037

theorem tailTrace_2176142 : CollatzResearch.WordTrace tailWord_2176142 prefixEnd_2176142 372468939478843356039037 := by
  unfold tailWord_2176142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921302410277083038713335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52913612854811109539804453 9921302410277083038713335)
  ·
    refine ⟨14881953615415624558070003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9921302410277083038713335 14881953615415624558070003)
    ·
      refine ⟨22322930423123436837105005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14881953615415624558070003 22322930423123436837105005)
      ·
        refine ⟨8371098908671288813914377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22322930423123436837105005 8371098908671288813914377)
        ·
          refine ⟨6278324181503466610435783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8371098908671288813914377 6278324181503466610435783)
          ·
            refine ⟨9417486272255199915653675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6278324181503466610435783 9417486272255199915653675)
            ·
              refine ⟨14126229408382799873480513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9417486272255199915653675 14126229408382799873480513)
              ·
                refine ⟨10594672056287099905110385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14126229408382799873480513 10594672056287099905110385)
                ·
                  refine ⟨7946004042215324928832789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10594672056287099905110385 7946004042215324928832789)
                  ·
                    refine ⟨372468939478843356039037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7946004042215324928832789 372468939478843356039037)
                    ·
                      rfl

theorem cell23_2176142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2176142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176142 prefixEnd_2176142 := by exact prefixLift 2176142
  have htrace : WordTrace (prefixWord ++ tailWord_2176142) baseStart_2176142 baseEnd_2176142 := by
    simpa [prefixWord, tailWord_2176142, baseEnd_2176142] using wordTrace_append hprefix tailTrace_2176142
  have hstable : (prefixWord ++ tailWord_2176142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176142).length < 2 ^ (prefixWord ++ tailWord_2176142).sum := by decide
  have hdescent : baseEnd_2176142 < baseStart_2176142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176189 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 5]
def baseStart_2176189 : Nat := 118140960795 + 2176189 * 2 ^ 59
def prefixEnd_2176189 : Nat := 4983230072969 + 3 ^ 40 * 2176189 * 2
def baseEnd_2176189 : Nat := 124158994669699042692155

theorem tailTrace_2176189 : CollatzResearch.WordTrace tailWord_2176189 prefixEnd_2176189 124158994669699042692155 := by
  unfold tailWord_2176189
  simp only [CollatzResearch.WordTrace]
  refine ⟨79372133513046391336667621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52914755675364260891111747 79372133513046391336667621)
  ·
    refine ⟨14882275033696198375625179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79372133513046391336667621 14882275033696198375625179)
    ·
      refine ⟨22323412550544297563437769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14882275033696198375625179 22323412550544297563437769)
      ·
        refine ⟨16742559412908223172578327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22323412550544297563437769 16742559412908223172578327)
        ·
          refine ⟨25113839119362334758867491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16742559412908223172578327 25113839119362334758867491)
          ·
            refine ⟨37670758679043502138301237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25113839119362334758867491 37670758679043502138301237)
            ·
              refine ⟨3531633626160328325465741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37670758679043502138301237 3531633626160328325465741)
              ·
                refine ⟨1324362609810123122049653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3531633626160328325465741 1324362609810123122049653)
                ·
                  refine ⟨124158994669699042692155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1324362609810123122049653 124158994669699042692155)
                  ·
                    rfl

theorem cell23_2176189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_2176189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176189 prefixEnd_2176189 := by exact prefixLift 2176189
  have htrace : WordTrace (prefixWord ++ tailWord_2176189) baseStart_2176189 baseEnd_2176189 := by
    simpa [prefixWord, tailWord_2176189, baseEnd_2176189] using wordTrace_append hprefix tailTrace_2176189
  have hstable : (prefixWord ++ tailWord_2176189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176189).length < 2 ^ (prefixWord ++ tailWord_2176189).sum := by decide
  have hdescent : baseEnd_2176189 < baseStart_2176189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176202 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_2176202 : Nat := 118140960795 + 2176202 * 2 ^ 59
def prefixEnd_2176202 : Nat := 4983230072969 + 3 ^ 40 * 2176202 * 2
def baseEnd_2176202 : Nat := 372479209091933277788945

theorem tailTrace_2176202 : CollatzResearch.WordTrace tailWord_2176202 prefixEnd_2176202 372479209091933277788945 := by
  unfold tailWord_2176202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843151915499823639222715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52915071774666196371260573 19843151915499823639222715)
  ·
    refine ⟨29764727873249735458834073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19843151915499823639222715 29764727873249735458834073)
    ·
      refine ⟨22323545904937301594125555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29764727873249735458834073 22323545904937301594125555)
      ·
        refine ⟨33485318857405952391188333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22323545904937301594125555 33485318857405952391188333)
        ·
          refine ⟨12556994571527232146695625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33485318857405952391188333 12556994571527232146695625)
          ·
            refine ⟨9417745928645424110021719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12556994571527232146695625 9417745928645424110021719)
            ·
              refine ⟨14126618892968136165032579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9417745928645424110021719 14126618892968136165032579)
              ·
                refine ⟨21189928339452204247548869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14126618892968136165032579 21189928339452204247548869)
                ·
                  refine ⟨3973111563647288296415413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21189928339452204247548869 3973111563647288296415413)
                  ·
                    refine ⟨372479209091933277788945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3973111563647288296415413 372479209091933277788945)
                    ·
                      rfl

theorem cell23_2176202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_2176202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176202 prefixEnd_2176202 := by exact prefixLift 2176202
  have htrace : WordTrace (prefixWord ++ tailWord_2176202) baseStart_2176202 baseEnd_2176202 := by
    simpa [prefixWord, tailWord_2176202, baseEnd_2176202] using wordTrace_append hprefix tailTrace_2176202
  have hstable : (prefixWord ++ tailWord_2176202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176202).length < 2 ^ (prefixWord ++ tailWord_2176202).sum := by decide
  have hdescent : baseEnd_2176202 < baseStart_2176202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176206 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_2176206 : Nat := 118140960795 + 2176206 * 2 ^ 59
def prefixEnd_2176206 : Nat := 4983230072969 + 3 ^ 40 * 2176206 * 2
def baseEnd_2176206 : Nat := 124159964577601979746313

theorem tailTrace_2176206 : CollatzResearch.WordTrace tailWord_2176206 prefixEnd_2176206 124159964577601979746313 := by
  unfold tailWord_2176206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921594194248100405004559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52915169035989868826690981 9921594194248100405004559)
  ·
    refine ⟨14882391291372150607506839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9921594194248100405004559 14882391291372150607506839)
    ·
      refine ⟨22323586937058225911260259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14882391291372150607506839 22323586937058225911260259)
      ·
        refine ⟨33485380405587338866890389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22323586937058225911260259 33485380405587338866890389)
        ·
          refine ⟨1569627206511906509385487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33485380405587338866890389 1569627206511906509385487)
          ·
            refine ⟨2354440809767859764078231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569627206511906509385487 2354440809767859764078231)
            ·
              refine ⟨3531661214651789646117347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354440809767859764078231 3531661214651789646117347)
              ·
                refine ⟨5297491821977684469176021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531661214651789646117347 5297491821977684469176021)
                ·
                  refine ⟨124159964577601979746313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5297491821977684469176021 124159964577601979746313)
                  ·
                    rfl

theorem cell23_2176206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_2176206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176206 prefixEnd_2176206 := by exact prefixLift 2176206
  have htrace : WordTrace (prefixWord ++ tailWord_2176206) baseStart_2176206 baseEnd_2176206 := by
    simpa [prefixWord, tailWord_2176206, baseEnd_2176206] using wordTrace_append hprefix tailTrace_2176206
  have hstable : (prefixWord ++ tailWord_2176206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176206).length < 2 ^ (prefixWord ++ tailWord_2176206).sum := by decide
  have hdescent : baseEnd_2176206 < baseStart_2176206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176259 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3]
def baseStart_2176259 : Nat := 118140960795 + 2176259 * 2 ^ 59
def prefixEnd_2176259 : Nat := 4983230072969 + 3 ^ 40 * 2176259 * 2
def baseEnd_2176259 : Nat := 1117466895673106110354073

theorem tailTrace_2176259 : CollatzResearch.WordTrace tailWord_2176259 prefixEnd_2176259 1117466895673106110354073 := by
  unfold tailWord_2176259
  simp only [CollatzResearch.WordTrace]
  refine ⟨79374686622792793291715831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52916457748528528861143887 79374686622792793291715831)
  ·
    refine ⟨119062029934189189937573747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79374686622792793291715831 119062029934189189937573747)
    ·
      refine ⟨178593044901283784906360621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119062029934189189937573747 178593044901283784906360621)
      ·
        refine ⟨66972391837981419339885233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178593044901283784906360621 66972391837981419339885233)
        ·
          refine ⟨50229293878486064504913925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66972391837981419339885233 50229293878486064504913925)
          ·
            refine ⟨9417992602216137094671361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50229293878486064504913925 9417992602216137094671361)
            ·
              refine ⟨7063494451662102821003521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9417992602216137094671361 7063494451662102821003521)
              ·
                refine ⟨5297620838746577115752641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7063494451662102821003521 5297620838746577115752641)
                ·
                  refine ⟨3973215629059932836814481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5297620838746577115752641 3973215629059932836814481)
                  ·
                    refine ⟨2979911721794949627610861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3973215629059932836814481 2979911721794949627610861)
                    ·
                      refine ⟨1117466895673106110354073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2979911721794949627610861 1117466895673106110354073)
                      ·
                        rfl

theorem cell23_2176259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_2176259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176259 prefixEnd_2176259 := by exact prefixLift 2176259
  have htrace : WordTrace (prefixWord ++ tailWord_2176259) baseStart_2176259 baseEnd_2176259 := by
    simpa [prefixWord, tailWord_2176259, baseEnd_2176259] using wordTrace_append hprefix tailTrace_2176259
  have hstable : (prefixWord ++ tailWord_2176259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176259).length < 2 ^ (prefixWord ++ tailWord_2176259).sum := by decide
  have hdescent : baseEnd_2176259 < baseStart_2176259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176299 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 8, 3, 2]
def baseStart_2176299 : Nat := 118140960795 + 2176299 * 2 ^ 59
def prefixEnd_2176299 : Nat := 4983230072969 + 3 ^ 40 * 2176299 * 2
def baseEnd_2176299 : Nat := 1117487434899285953853889

theorem tailTrace_2176299 : CollatzResearch.WordTrace tailWord_2176299 prefixEnd_2176299 1117487434899285953853889 := by
  unfold tailWord_2176299
  simp only [CollatzResearch.WordTrace]
  refine ⟨79376145542647880123171951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52917430361765253415447967 79376145542647880123171951)
  ·
    refine ⟨119064218313971820184757927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79376145542647880123171951 119064218313971820184757927)
    ·
      refine ⟨178596327470957730277136891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119064218313971820184757927 178596327470957730277136891)
      ·
        refine ⟨267894491206436595415705337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178596327470957730277136891 267894491206436595415705337)
        ·
          refine ⟨200920868404827446561779003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267894491206436595415705337 200920868404827446561779003)
          ·
            refine ⟨301381302607241169842668505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200920868404827446561779003 301381302607241169842668505)
            ·
              refine ⟨226035976955430877382001379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301381302607241169842668505 226035976955430877382001379)
              ·
                refine ⟨339053965433146316073002069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226035976955430877382001379 339053965433146316073002069)
                ·
                  refine ⟨3973288657419683391480493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 339053965433146316073002069 3973288657419683391480493)
                  ·
                    refine ⟨1489983246532381271805185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3973288657419683391480493 1489983246532381271805185)
                    ·
                      refine ⟨1117487434899285953853889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489983246532381271805185 1117487434899285953853889)
                      ·
                        rfl

theorem cell23_2176299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3, 2].length) (baseStart_2176299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176299 prefixEnd_2176299 := by exact prefixLift 2176299
  have htrace : WordTrace (prefixWord ++ tailWord_2176299) baseStart_2176299 baseEnd_2176299 := by
    simpa [prefixWord, tailWord_2176299, baseEnd_2176299] using wordTrace_append hprefix tailTrace_2176299
  have hstable : (prefixWord ++ tailWord_2176299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176299).length < 2 ^ (prefixWord ++ tailWord_2176299).sum := by decide
  have hdescent : baseEnd_2176299 < baseStart_2176299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176313 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 6]
def baseStart_2176313 : Nat := 118140960795 + 2176313 * 2 ^ 59
def prefixEnd_2176313 : Nat := 4983230072969 + 3 ^ 40 * 2176313 * 2
def baseEnd_2176313 : Nat := 124166069292049877675425

theorem tailTrace_2176313 : CollatzResearch.WordTrace tailWord_2176313 prefixEnd_2176313 124166069292049877675425 := by
  unfold tailWord_2176313
  simp only [CollatzResearch.WordTrace]
  refine ⟨79376656164597160514181593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52917770776398107009454395 79376656164597160514181593)
  ·
    refine ⟨59532492123447870385636195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79376656164597160514181593 59532492123447870385636195)
    ·
      refine ⟨89298738185171805578454293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59532492123447870385636195 89298738185171805578454293)
      ·
        refine ⟨4185878352429928386490045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89298738185171805578454293 4185878352429928386490045)
        ·
          refine ⟨1569704382161223144933767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4185878352429928386490045 1569704382161223144933767)
          ·
            refine ⟨2354556573241834717400651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569704382161223144933767 2354556573241834717400651)
            ·
              refine ⟨3531834859862752076100977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354556573241834717400651 3531834859862752076100977)
              ·
                refine ⟨2648876144897064057075733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3531834859862752076100977 2648876144897064057075733)
                ·
                  refine ⟨124166069292049877675425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2648876144897064057075733 124166069292049877675425)
                  ·
                    rfl

theorem cell23_2176313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 6].length) (baseStart_2176313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176313 prefixEnd_2176313 := by exact prefixLift 2176313
  have htrace : WordTrace (prefixWord ++ tailWord_2176313) baseStart_2176313 baseEnd_2176313 := by
    simpa [prefixWord, tailWord_2176313, baseEnd_2176313] using wordTrace_append hprefix tailTrace_2176313
  have hstable : (prefixWord ++ tailWord_2176313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176313).length < 2 ^ (prefixWord ++ tailWord_2176313).sum := by decide
  have hdescent : baseEnd_2176313 < baseStart_2176313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176386 : List Nat := [3, 4, 2, 1, 1, 1, 1, 10]
def baseStart_2176386 : Nat := 118140960795 + 2176386 * 2 ^ 59
def prefixEnd_2176386 : Nat := 4983230072969 + 3 ^ 40 * 2176386 * 2
def baseEnd_2176386 : Nat := 41390078063563967165407

theorem tailTrace_2176386 : CollatzResearch.WordTrace tailWord_2176386 prefixEnd_2176386 41390078063563967165407 := by
  unfold tailWord_2176386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19844829673333173495397253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52919545795555129321059341 19844829673333173495397253)
  ·
    refine ⟨3720905563749970030386985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19844829673333173495397253 3720905563749970030386985)
    ·
      refine ⟨2790679172812477522790239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3720905563749970030386985 2790679172812477522790239)
      ·
        refine ⟨4186018759218716284185359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790679172812477522790239 4186018759218716284185359)
        ·
          refine ⟨6279028138828074426278039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186018759218716284185359 6279028138828074426278039)
          ·
            refine ⟨9418542208242111639417059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6279028138828074426278039 9418542208242111639417059)
            ·
              refine ⟨14127813312363167459125589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9418542208242111639417059 14127813312363167459125589)
              ·
                refine ⟨41390078063563967165407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14127813312363167459125589 41390078063563967165407)
                ·
                  rfl

theorem cell23_2176386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_2176386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176386 prefixEnd_2176386 := by exact prefixLift 2176386
  have htrace : WordTrace (prefixWord ++ tailWord_2176386) baseStart_2176386 baseEnd_2176386 := by
    simpa [prefixWord, tailWord_2176386, baseEnd_2176386] using wordTrace_append hprefix tailTrace_2176386
  have hstable : (prefixWord ++ tailWord_2176386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176386).length < 2 ^ (prefixWord ++ tailWord_2176386).sum := by decide
  have hdescent : baseEnd_2176386 < baseStart_2176386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176439 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_2176439 : Nat := 118140960795 + 2176439 * 2 ^ 59
def prefixEnd_2176439 : Nat := 4983230072969 + 3 ^ 40 * 2176439 * 2
def baseEnd_2176439 : Nat := 1117559322190915406103245

theorem tailTrace_2176439 : CollatzResearch.WordTrace tailWord_2176439 prefixEnd_2176439 1117559322190915406103245 := by
  unfold tailWord_2176439
  simp only [CollatzResearch.WordTrace]
  refine ⟨79381251762140684033268371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52920834508093789355512247 79381251762140684033268371)
  ·
    refine ⟨119071877643211026049902557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79381251762140684033268371 119071877643211026049902557)
    ·
      refine ⟨44651954116204134768713459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119071877643211026049902557 44651954116204134768713459)
      ·
        refine ⟨66977931174306202153070189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44651954116204134768713459 66977931174306202153070189)
        ·
          refine ⟨25116724190364825807401321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66977931174306202153070189 25116724190364825807401321)
          ·
            refine ⟨18837543142773619355550991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25116724190364825807401321 18837543142773619355550991)
            ·
              refine ⟨28256314714160429033326487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18837543142773619355550991 28256314714160429033326487)
              ·
                refine ⟨42384472071240643549989731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28256314714160429033326487 42384472071240643549989731)
                ·
                  refine ⟨63576708106860965324984597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42384472071240643549989731 63576708106860965324984597)
                  ·
                    refine ⟨2980158192509107749608653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63576708106860965324984597 2980158192509107749608653)
                    ·
                      refine ⟨1117559322190915406103245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980158192509107749608653 1117559322190915406103245)
                      ·
                        rfl

theorem cell23_2176439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_2176439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176439 prefixEnd_2176439 := by exact prefixLift 2176439
  have htrace : WordTrace (prefixWord ++ tailWord_2176439) baseStart_2176439 baseEnd_2176439 := by
    simpa [prefixWord, tailWord_2176439, baseEnd_2176439] using wordTrace_append hprefix tailTrace_2176439
  have hstable : (prefixWord ++ tailWord_2176439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176439).length < 2 ^ (prefixWord ++ tailWord_2176439).sum := by decide
  have hdescent : baseEnd_2176439 < baseStart_2176439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176470 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2176470 : Nat := 118140960795 + 2176470 * 2 ^ 59
def prefixEnd_2176470 : Nat := 4983230072969 + 3 ^ 40 * 2176470 * 2
def baseEnd_2176470 : Nat := 1117575240091204784815603

theorem tailTrace_2176470 : CollatzResearch.WordTrace tailWord_2176470 prefixEnd_2176470 1117575240091204784815603 := by
  unfold tailWord_2176470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961398901564273520477929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52921588283352250885097909 4961398901564273520477929)
  ·
    refine ⟨3721049176173205140358447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4961398901564273520477929 3721049176173205140358447)
    ·
      refine ⟨5581573764259807710537671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721049176173205140358447 5581573764259807710537671)
      ·
        refine ⟨8372360646389711565806507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581573764259807710537671 8372360646389711565806507)
        ·
          refine ⟨12558540969584567348709761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8372360646389711565806507 12558540969584567348709761)
          ·
            refine ⟨9418905727188425511532321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12558540969584567348709761 9418905727188425511532321)
            ·
              refine ⟨7064179295391319133649241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9418905727188425511532321 7064179295391319133649241)
              ·
                refine ⟨5298134471543489350236931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7064179295391319133649241 5298134471543489350236931)
                ·
                  refine ⟨7947201707315234025355397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298134471543489350236931 7947201707315234025355397)
                  ·
                    refine ⟨1490100320121606379754137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7947201707315234025355397 1490100320121606379754137)
                    ·
                      refine ⟨1117575240091204784815603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490100320121606379754137 1117575240091204784815603)
                      ·
                        rfl

theorem cell23_2176470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2176470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176470 prefixEnd_2176470 := by exact prefixLift 2176470
  have htrace : WordTrace (prefixWord ++ tailWord_2176470) baseStart_2176470 baseEnd_2176470 := by
    simpa [prefixWord, tailWord_2176470, baseEnd_2176470] using wordTrace_append hprefix tailTrace_2176470
  have hstable : (prefixWord ++ tailWord_2176470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176470).length < 2 ^ (prefixWord ++ tailWord_2176470).sum := by decide
  have hdescent : baseEnd_2176470 < baseStart_2176470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176487 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2176487 : Nat := 118140960795 + 2176487 * 2 ^ 59
def prefixEnd_2176487 : Nat := 4983230072969 + 3 ^ 40 * 2176487 * 2
def baseEnd_2176487 : Nat := 1117583969262331218303025

theorem tailTrace_2176487 : CollatzResearch.WordTrace tailWord_2176487 prefixEnd_2176487 1117583969262331218303025 := by
  unfold tailWord_2176487
  simp only [CollatzResearch.WordTrace]
  refine ⟨79383002465966788231015715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52922001643977858820677143 79383002465966788231015715)
  ·
    refine ⟨119074503698950182346523573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79383002465966788231015715 119074503698950182346523573)
    ·
      refine ⟨11163234721776579594986585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119074503698950182346523573 11163234721776579594986585)
      ·
        refine ⟨8372426041332434696239939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11163234721776579594986585 8372426041332434696239939)
        ·
          refine ⟨12558639061998652044359909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8372426041332434696239939 12558639061998652044359909)
          ·
            refine ⟨2354744824124747258317483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12558639061998652044359909 2354744824124747258317483)
            ·
              refine ⟨3532117236187120887476225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354744824124747258317483 3532117236187120887476225)
              ·
                refine ⟨2649087927140340665607169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3532117236187120887476225 2649087927140340665607169)
                ·
                  refine ⟨1986815945355255499205377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649087927140340665607169 1986815945355255499205377)
                  ·
                    refine ⟨1490111959016441624404033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986815945355255499205377 1490111959016441624404033)
                    ·
                      refine ⟨1117583969262331218303025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490111959016441624404033 1117583969262331218303025)
                      ·
                        rfl

theorem cell23_2176487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2176487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176487 prefixEnd_2176487 := by exact prefixLift 2176487
  have htrace : WordTrace (prefixWord ++ tailWord_2176487) baseStart_2176487 baseEnd_2176487 := by
    simpa [prefixWord, tailWord_2176487, baseEnd_2176487] using wordTrace_append hprefix tailTrace_2176487
  have hstable : (prefixWord ++ tailWord_2176487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176487).length < 2 ^ (prefixWord ++ tailWord_2176487).sum := by decide
  have hdescent : baseEnd_2176487 < baseStart_2176487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176493 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2176493 : Nat := 118140960795 + 2176493 * 2 ^ 59
def prefixEnd_2176493 : Nat := 4983230072969 + 3 ^ 40 * 2176493 * 2
def baseEnd_2176493 : Nat := 124176338905139799425333

theorem tailTrace_2176493 : CollatzResearch.WordTrace tailWord_2176493 prefixEnd_2176493 124176338905139799425333 := by
  unfold tailWord_2176493
  simp only [CollatzResearch.WordTrace]
  refine ⟨79383221303945051255734133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52922147535963367503822755 79383221303945051255734133)
  ·
    refine ⟨7442176997244848555225075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79383221303945051255734133 7442176997244848555225075)
    ·
      refine ⟨11163265495867272832837613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7442176997244848555225075 11163265495867272832837613)
      ·
        refine ⟨4186224560950227312314105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11163265495867272832837613 4186224560950227312314105)
        ·
          refine ⟨3139668420712670484235579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4186224560950227312314105 3139668420712670484235579)
          ·
            refine ⟨4709502631069005726353369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139668420712670484235579 4709502631069005726353369)
            ·
              refine ⟨3532126973301754294765027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4709502631069005726353369 3532126973301754294765027)
              ·
                refine ⟨5298190459952631442147541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532126973301754294765027 5298190459952631442147541)
                ·
                  refine ⟨124176338905139799425333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5298190459952631442147541 124176338905139799425333)
                  ·
                    rfl

theorem cell23_2176493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2176493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176493 prefixEnd_2176493 := by exact prefixLift 2176493
  have htrace : WordTrace (prefixWord ++ tailWord_2176493) baseStart_2176493 baseEnd_2176493 := by
    simpa [prefixWord, tailWord_2176493, baseEnd_2176493] using wordTrace_append hprefix tailTrace_2176493
  have hstable : (prefixWord ++ tailWord_2176493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176493).length < 2 ^ (prefixWord ++ tailWord_2176493).sum := by decide
  have hdescent : baseEnd_2176493 < baseStart_2176493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176604 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2176604 : Nat := 118140960795 + 2176604 * 2 ^ 59
def prefixEnd_2176604 : Nat := 4983230072969 + 3 ^ 40 * 2176604 * 2
def baseEnd_2176604 : Nat := 372548015499635753513329

theorem tailTrace_2176604 : CollatzResearch.WordTrace tailWord_2176604 prefixEnd_2176604 372548015499635753513329 := by
  unfold tailWord_2176604
  simp only [CollatzResearch.WordTrace]
  refine ⟨39693634903271458606512433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52924846537695278142016577 39693634903271458606512433)
  ·
    refine ⟨29770226177453593954884325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39693634903271458606512433 29770226177453593954884325)
    ·
      refine ⟨5581917408272548866540811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29770226177453593954884325 5581917408272548866540811)
      ·
        refine ⟨8372876112408823299811217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581917408272548866540811 8372876112408823299811217)
        ·
          refine ⟨6279657084306617474858413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8372876112408823299811217 6279657084306617474858413)
          ·
            refine ⟨2354871406614981553071905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6279657084306617474858413 2354871406614981553071905)
            ·
              refine ⟨1766153554961236164803929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2354871406614981553071905 1766153554961236164803929)
              ·
                refine ⟨1324615166220927123602947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766153554961236164803929 1324615166220927123602947)
                ·
                  refine ⟨1986922749331390685404421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324615166220927123602947 1986922749331390685404421)
                  ·
                    refine ⟨372548015499635753513329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1986922749331390685404421 372548015499635753513329)
                    ·
                      rfl

theorem cell23_2176604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2176604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176604 prefixEnd_2176604 := by exact prefixLift 2176604
  have htrace : WordTrace (prefixWord ++ tailWord_2176604) baseStart_2176604 baseEnd_2176604 := by
    simpa [prefixWord, tailWord_2176604, baseEnd_2176604] using wordTrace_append hprefix tailTrace_2176604
  have hstable : (prefixWord ++ tailWord_2176604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176604).length < 2 ^ (prefixWord ++ tailWord_2176604).sum := by decide
  have hdescent : baseEnd_2176604 < baseStart_2176604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176633 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_2176633 : Nat := 118140960795 + 2176633 * 2 ^ 59
def prefixEnd_2176633 : Nat := 4983230072969 + 3 ^ 40 * 2176633 * 2
def baseEnd_2176633 : Nat := 1117658937437887647077353

theorem tailTrace_2176633 : CollatzResearch.WordTrace tailWord_2176633 prefixEnd_2176633 1117658937437887647077353 := by
  unfold tailWord_2176633
  simp only [CollatzResearch.WordTrace]
  refine ⟨79388327523437855165830553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52925551682291903443887035 79388327523437855165830553)
  ·
    refine ⟨59541245642578391374372915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79388327523437855165830553 59541245642578391374372915)
    ·
      refine ⟨89311868463867587061559373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59541245642578391374372915 89311868463867587061559373)
      ·
        refine ⟨33491950673950345148084765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89311868463867587061559373 33491950673950345148084765)
        ·
          refine ⟨12559481502731379430531787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33491950673950345148084765 12559481502731379430531787)
          ·
            refine ⟨18839222254097069145797681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12559481502731379430531787 18839222254097069145797681)
            ·
              refine ⟨14129416690572801859348261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18839222254097069145797681 14129416690572801859348261)
              ·
                refine ⟨2649265629482400348627799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14129416690572801859348261 2649265629482400348627799)
                ·
                  refine ⟨3973898444223600522941699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649265629482400348627799 3973898444223600522941699)
                  ·
                    refine ⟨5960847666335400784412549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973898444223600522941699 5960847666335400784412549)
                    ·
                      refine ⟨1117658937437887647077353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5960847666335400784412549 1117658937437887647077353)
                      ·
                        rfl

theorem cell23_2176633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_2176633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176633 prefixEnd_2176633 := by exact prefixLift 2176633
  have htrace : WordTrace (prefixWord ++ tailWord_2176633) baseStart_2176633 baseEnd_2176633 := by
    simpa [prefixWord, tailWord_2176633, baseEnd_2176633] using wordTrace_append hprefix tailTrace_2176633
  have hstable : (prefixWord ++ tailWord_2176633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176633).length < 2 ^ (prefixWord ++ tailWord_2176633).sum := by decide
  have hdescent : baseEnd_2176633 < baseStart_2176633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176637 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_2176637 : Nat := 118140960795 + 2176637 * 2 ^ 59
def prefixEnd_2176637 : Nat := 4983230072969 + 3 ^ 40 * 2176637 * 2
def baseEnd_2176637 : Nat := 1117660991360505631427335

theorem tailTrace_2176637 : CollatzResearch.WordTrace tailWord_2176637 prefixEnd_2176637 1117660991360505631427335 := by
  unfold tailWord_2176637
  simp only [CollatzResearch.WordTrace]
  refine ⟨79388473415423363848976165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52925648943615575899317443 79388473415423363848976165)
  ·
    refine ⟨14885338765391880721683031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79388473415423363848976165 14885338765391880721683031)
    ·
      refine ⟨22328008148087821082524547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14885338765391880721683031 22328008148087821082524547)
      ·
        refine ⟨33492012222131731623786821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22328008148087821082524547 33492012222131731623786821)
        ·
          refine ⟨6279752291649699679460029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33492012222131731623786821 6279752291649699679460029)
          ·
            refine ⟨2354907109368637379797511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6279752291649699679460029 2354907109368637379797511)
            ·
              refine ⟨3532360664052956069696267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354907109368637379797511 3532360664052956069696267)
              ·
                refine ⟨5298540996079434104544401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532360664052956069696267 5298540996079434104544401)
                ·
                  refine ⟨3973905747059575578408301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5298540996079434104544401 3973905747059575578408301)
                  ·
                    refine ⟨1490214655147340841903113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3973905747059575578408301 1490214655147340841903113)
                    ·
                      refine ⟨1117660991360505631427335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490214655147340841903113 1117660991360505631427335)
                      ·
                        rfl

theorem cell23_2176637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_2176637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176637 prefixEnd_2176637 := by exact prefixLift 2176637
  have htrace : WordTrace (prefixWord ++ tailWord_2176637) baseStart_2176637 baseEnd_2176637 := by
    simpa [prefixWord, tailWord_2176637, baseEnd_2176637] using wordTrace_append hprefix tailTrace_2176637
  have hstable : (prefixWord ++ tailWord_2176637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176637).length < 2 ^ (prefixWord ++ tailWord_2176637).sum := by decide
  have hdescent : baseEnd_2176637 < baseStart_2176637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176644 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_2176644 : Nat := 118140960795 + 2176644 * 2 ^ 59
def prefixEnd_2176644 : Nat := 4983230072969 + 3 ^ 40 * 2176644 * 2
def baseEnd_2176644 : Nat := 1117664585725087104039803

theorem tailTrace_2176644 : CollatzResearch.WordTrace tailWord_2176644 prefixEnd_2176644 1117664585725087104039803 := by
  unfold tailWord_2176644
  simp only [CollatzResearch.WordTrace]
  refine ⟨39694364363199002022240493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52925819150932002696320657 39694364363199002022240493)
  ·
    refine ⟨14885386636199625758340185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39694364363199002022240493 14885386636199625758340185)
    ·
      refine ⟨11164039977149719318755139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14885386636199625758340185 11164039977149719318755139)
      ·
        refine ⟨16746059965724578978132709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11164039977149719318755139 16746059965724578978132709)
        ·
          refine ⟨3139886243573358558399883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16746059965724578978132709 3139886243573358558399883)
          ·
            refine ⟨4709829365360037837599825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139886243573358558399883 4709829365360037837599825)
            ·
              refine ⟨3532372024020028378199869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4709829365360037837599825 3532372024020028378199869)
              ·
                refine ⟨1324639509007510641824951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3532372024020028378199869 1324639509007510641824951)
                ·
                  refine ⟨1986959263511265962737427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324639509007510641824951 1986959263511265962737427)
                  ·
                    refine ⟨2980438895266898944106141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1986959263511265962737427 2980438895266898944106141)
                    ·
                      refine ⟨1117664585725087104039803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980438895266898944106141 1117664585725087104039803)
                      ·
                        rfl

theorem cell23_2176644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_2176644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176644 prefixEnd_2176644 := by exact prefixLift 2176644
  have htrace : WordTrace (prefixWord ++ tailWord_2176644) baseStart_2176644 baseEnd_2176644 := by
    simpa [prefixWord, tailWord_2176644, baseEnd_2176644] using wordTrace_append hprefix tailTrace_2176644
  have hstable : (prefixWord ++ tailWord_2176644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176644).length < 2 ^ (prefixWord ++ tailWord_2176644).sum := by decide
  have hdescent : baseEnd_2176644 < baseStart_2176644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176650 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2176650 : Nat := 118140960795 + 2176650 * 2 ^ 59
def prefixEnd_2176650 : Nat := 4983230072969 + 3 ^ 40 * 2176650 * 2
def baseEnd_2176650 : Nat := 1117667666609014080564775

theorem tailTrace_2176650 : CollatzResearch.WordTrace tailWord_2176650 prefixEnd_2176650 1117667666609014080564775 := by
  unfold tailWord_2176650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19847236891094066767299851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52925965042917511379466269 19847236891094066767299851)
  ·
    refine ⟨29770855336641100150949777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19847236891094066767299851 29770855336641100150949777)
    ·
      refine ⟨22328141502480825113212333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29770855336641100150949777 22328141502480825113212333)
      ·
        refine ⟨8373053063430309417454625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22328141502480825113212333 8373053063430309417454625)
        ·
          refine ⟨6279789797572732063090969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8373053063430309417454625 6279789797572732063090969)
          ·
            refine ⟨4709842348179549047318227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6279789797572732063090969 4709842348179549047318227)
            ·
              refine ⟨7064763522269323570977341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709842348179549047318227 7064763522269323570977341)
              ·
                refine ⟨2649286320850996339116503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7064763522269323570977341 2649286320850996339116503)
                ·
                  refine ⟨3973929481276494508674755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649286320850996339116503 3973929481276494508674755)
                  ·
                    refine ⟨5960894221914741763012133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3973929481276494508674755 5960894221914741763012133)
                    ·
                      refine ⟨1117667666609014080564775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5960894221914741763012133 1117667666609014080564775)
                      ·
                        rfl

theorem cell23_2176650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2176650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176650 prefixEnd_2176650 := by exact prefixLift 2176650
  have htrace : WordTrace (prefixWord ++ tailWord_2176650) baseStart_2176650 baseEnd_2176650 := by
    simpa [prefixWord, tailWord_2176650, baseEnd_2176650] using wordTrace_append hprefix tailTrace_2176650
  have hstable : (prefixWord ++ tailWord_2176650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176650).length < 2 ^ (prefixWord ++ tailWord_2176650).sum := by decide
  have hdescent : baseEnd_2176650 < baseStart_2176650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176670 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2176670 : Nat := 118140960795 + 2176670 * 2 ^ 59
def prefixEnd_2176670 : Nat := 4983230072969 + 3 ^ 40 * 2176670 * 2
def baseEnd_2176670 : Nat := 1117677936222104002314683

theorem tailTrace_2176670 : CollatzResearch.WordTrace tailWord_2176670 prefixEnd_2176670 1117677936222104002314683 := by
  unfold tailWord_2176670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9923709628037976310615933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52926451349535873656618309 9923709628037976310615933)
  ·
    refine ⟨3721391110514241116480975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9923709628037976310615933 3721391110514241116480975)
    ·
      refine ⟨5582086665771361674721463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721391110514241116480975 5582086665771361674721463)
      ·
        refine ⟨8373129998657042512082195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5582086665771361674721463 8373129998657042512082195)
        ·
          refine ⟨12559694997985563768123293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8373129998657042512082195 12559694997985563768123293)
          ·
            refine ⟨4709885624244586413046235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12559694997985563768123293 4709885624244586413046235)
            ·
              refine ⟨7064828436366879619569353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709885624244586413046235 7064828436366879619569353)
              ·
                refine ⟨5298621327275159714677015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7064828436366879619569353 5298621327275159714677015)
                ·
                  refine ⟨7947931990912739572015523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298621327275159714677015 7947931990912739572015523)
                  ·
                    refine ⟨11921897986369109358023285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7947931990912739572015523 11921897986369109358023285)
                    ·
                      refine ⟨1117677936222104002314683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11921897986369109358023285 1117677936222104002314683)
                      ·
                        rfl

theorem cell23_2176670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2176670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176670 prefixEnd_2176670 := by exact prefixLift 2176670
  have htrace : WordTrace (prefixWord ++ tailWord_2176670) baseStart_2176670 baseEnd_2176670 := by
    simpa [prefixWord, tailWord_2176670, baseEnd_2176670] using wordTrace_append hprefix tailTrace_2176670
  have hstable : (prefixWord ++ tailWord_2176670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176670).length < 2 ^ (prefixWord ++ tailWord_2176670).sum := by decide
  have hdescent : baseEnd_2176670 < baseStart_2176670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176700 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2176700 : Nat := 118140960795 + 2176700 * 2 ^ 59
def prefixEnd_2176700 : Nat := 4983230072969 + 3 ^ 40 * 2176700 * 2
def baseEnd_2176700 : Nat := 1117693340641738884939545

theorem tailTrace_2176700 : CollatzResearch.WordTrace tailWord_2176700 prefixEnd_2176700 1117693340641738884939545 := by
  unfold tailWord_2176700
  simp only [CollatzResearch.WordTrace]
  refine ⟨39695385607097562804259777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52927180809463417072346369 39695385607097562804259777)
  ·
    refine ⟨29771539205323172103194833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39695385607097562804259777 29771539205323172103194833)
    ·
      refine ⟨22328654403992379077396125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29771539205323172103194833 22328654403992379077396125)
      ·
        refine ⟨8373245401497142154023547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22328654403992379077396125 8373245401497142154023547)
        ·
          refine ⟨12559868102245713231035321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8373245401497142154023547 12559868102245713231035321)
          ·
            refine ⟨9419901076684284923276491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12559868102245713231035321 9419901076684284923276491)
            ·
              refine ⟨14129851615026427384914737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9419901076684284923276491 14129851615026427384914737)
              ·
                refine ⟨10597388711269820538686053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14129851615026427384914737 10597388711269820538686053)
                ·
                  refine ⟨1987010383363091351003635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10597388711269820538686053 1987010383363091351003635)
                  ·
                    refine ⟨2980515575044637026505453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1987010383363091351003635 2980515575044637026505453)
                    ·
                      refine ⟨1117693340641738884939545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980515575044637026505453 1117693340641738884939545)
                      ·
                        rfl

theorem cell23_2176700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2176700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176700 prefixEnd_2176700 := by exact prefixLift 2176700
  have htrace : WordTrace (prefixWord ++ tailWord_2176700) baseStart_2176700 baseEnd_2176700 := by
    simpa [prefixWord, tailWord_2176700, baseEnd_2176700] using wordTrace_append hprefix tailTrace_2176700
  have hstable : (prefixWord ++ tailWord_2176700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176700).length < 2 ^ (prefixWord ++ tailWord_2176700).sum := by decide
  have hdescent : baseEnd_2176700 < baseStart_2176700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176740 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_2176740 : Nat := 118140960795 + 2176740 * 2 ^ 59
def prefixEnd_2176740 : Nat := 4983230072969 + 3 ^ 40 * 2176740 * 2
def baseEnd_2176740 : Nat := 1117713879867918728439361

theorem tailTrace_2176740 : CollatzResearch.WordTrace tailWord_2176740 prefixEnd_2176740 1117713879867918728439361 := by
  unfold tailWord_2176740
  simp only [CollatzResearch.WordTrace]
  refine ⟨39696115067025106219987837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52928153422700141626650449 39696115067025106219987837)
  ·
    refine ⟨14886043150134414832495439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39696115067025106219987837 14886043150134414832495439)
    ·
      refine ⟨22329064725201622248743159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14886043150134414832495439 22329064725201622248743159)
      ·
        refine ⟨33493597087802433373114739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22329064725201622248743159 33493597087802433373114739)
        ·
          refine ⟨50240395631703650059672109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33493597087802433373114739 50240395631703650059672109)
          ·
            refine ⟨18840148361888868772377041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50240395631703650059672109 18840148361888868772377041)
            ·
              refine ⟨14130111271416651579282781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18840148361888868772377041 14130111271416651579282781)
              ·
                refine ⟨5298791726781244342231043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14130111271416651579282781 5298791726781244342231043)
                ·
                  refine ⟨7948187590171866513346565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298791726781244342231043 7948187590171866513346565)
                  ·
                    refine ⟨1490285173157224971252481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7948187590171866513346565 1490285173157224971252481)
                    ·
                      refine ⟨1117713879867918728439361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490285173157224971252481 1117713879867918728439361)
                      ·
                        rfl

theorem cell23_2176740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_2176740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176740 prefixEnd_2176740 := by exact prefixLift 2176740
  have htrace : WordTrace (prefixWord ++ tailWord_2176740) baseStart_2176740 baseEnd_2176740 := by
    simpa [prefixWord, tailWord_2176740, baseEnd_2176740] using wordTrace_append hprefix tailTrace_2176740
  have hstable : (prefixWord ++ tailWord_2176740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176740).length < 2 ^ (prefixWord ++ tailWord_2176740).sum := by decide
  have hdescent : baseEnd_2176740 < baseStart_2176740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176744 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2176744 : Nat := 118140960795 + 2176744 * 2 ^ 59
def prefixEnd_2176744 : Nat := 4983230072969 + 3 ^ 40 * 2176744 * 2
def baseEnd_2176744 : Nat := 1117715933790536712789343

theorem tailTrace_2176744 : CollatzResearch.WordTrace tailWord_2176744 prefixEnd_2176744 1117715933790536712789343 := by
  unfold tailWord_2176744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39696188013017860561560643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52928250684023814082080857 39696188013017860561560643)
  ·
    refine ⟨59544282019526790842340965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39696188013017860561560643 59544282019526790842340965)
    ·
      refine ⟨11164552878661273282938931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59544282019526790842340965 11164552878661273282938931)
      ·
        refine ⟨16746829317991909924408397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11164552878661273282938931 16746829317991909924408397)
        ·
          refine ⟨6280060994246966221653149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16746829317991909924408397 6280060994246966221653149)
          ·
            refine ⟨2355022872842612333119931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6280060994246966221653149 2355022872842612333119931)
            ·
              refine ⟨3532534309263918499679897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355022872842612333119931 3532534309263918499679897)
              ·
                refine ⟨2649400731947938874759923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3532534309263918499679897 2649400731947938874759923)
                ·
                  refine ⟨3974101097921908312139885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649400731947938874759923 3974101097921908312139885)
                  ·
                    refine ⟨1490287911720715617052457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3974101097921908312139885 1490287911720715617052457)
                    ·
                      refine ⟨1117715933790536712789343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490287911720715617052457 1117715933790536712789343)
                      ·
                        rfl

theorem cell23_2176744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2176744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176744 prefixEnd_2176744 := by exact prefixLift 2176744
  have htrace : WordTrace (prefixWord ++ tailWord_2176744) baseStart_2176744 baseEnd_2176744 := by
    simpa [prefixWord, tailWord_2176744, baseEnd_2176744] using wordTrace_append hprefix tailTrace_2176744
  have hstable : (prefixWord ++ tailWord_2176744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176744).length < 2 ^ (prefixWord ++ tailWord_2176744).sum := by decide
  have hdescent : baseEnd_2176744 < baseStart_2176744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176770 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2176770 : Nat := 118140960795 + 2176770 * 2 ^ 59
def prefixEnd_2176770 : Nat := 4983230072969 + 3 ^ 40 * 2176770 * 2
def baseEnd_2176770 : Nat := 1117729284287553611064223

theorem tailTrace_2176770 : CollatzResearch.WordTrace tailWord_2176770 prefixEnd_2176770 1117729284287553611064223 := by
  unfold tailWord_2176770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19848331080985381890891941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52928882882627685042378509 19848331080985381890891941)
  ·
    refine ⟨3721562077684759104542239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19848331080985381890891941 3721562077684759104542239)
    ·
      refine ⟨5582343116527138656813359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721562077684759104542239 5582343116527138656813359)
      ·
        refine ⟨8373514674790707985220039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5582343116527138656813359 8373514674790707985220039)
        ·
          refine ⟨12560272012186061977830059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8373514674790707985220039 12560272012186061977830059)
          ·
            refine ⟨18840408018279092966745089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12560272012186061977830059 18840408018279092966745089)
            ·
              refine ⟨14130306013709319725058817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18840408018279092966745089 14130306013709319725058817)
              ·
                refine ⟨10597729510281989793794113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14130306013709319725058817 10597729510281989793794113)
                ·
                  refine ⟨7948297132711492345345585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10597729510281989793794113 7948297132711492345345585)
                  ·
                    refine ⟨5961222849533619259009189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7948297132711492345345585 5961222849533619259009189)
                    ·
                      refine ⟨1117729284287553611064223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5961222849533619259009189 1117729284287553611064223)
                      ·
                        rfl

theorem cell23_2176770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2176770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176770 prefixEnd_2176770 := by exact prefixLift 2176770
  have htrace : WordTrace (prefixWord ++ tailWord_2176770) baseStart_2176770 baseEnd_2176770 := by
    simpa [prefixWord, tailWord_2176770, baseEnd_2176770] using wordTrace_append hprefix tailTrace_2176770
  have hstable : (prefixWord ++ tailWord_2176770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176770).length < 2 ^ (prefixWord ++ tailWord_2176770).sum := by decide
  have hdescent : baseEnd_2176770 < baseStart_2176770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176800 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2176800 : Nat := 118140960795 + 2176800 * 2 ^ 59
def prefixEnd_2176800 : Nat := 4983230072969 + 3 ^ 40 * 2176800 * 2
def baseEnd_2176800 : Nat := 1117744688707188493689085

theorem tailTrace_2176800 : CollatzResearch.WordTrace tailWord_2176800 prefixEnd_2176800 1117744688707188493689085 := by
  unfold tailWord_2176800
  simp only [CollatzResearch.WordTrace]
  refine ⟨39697209256916421343579927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52929612342555228458106569 39697209256916421343579927)
  ·
    refine ⟨59545813885374632015369891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39697209256916421343579927 59545813885374632015369891)
    ·
      refine ⟨89318720828061948023054837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59545813885374632015369891 89318720828061948023054837)
      ·
        refine ⟨8373630077630807627161391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89318720828061948023054837 8373630077630807627161391)
        ·
          refine ⟨12560445116446211440742087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8373630077630807627161391 12560445116446211440742087)
          ·
            refine ⟨18840667674669317161113131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12560445116446211440742087 18840667674669317161113131)
            ·
              refine ⟨28261001512003975741669697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18840667674669317161113131 28261001512003975741669697)
              ·
                refine ⟨21195751134002981806252273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28261001512003975741669697 21195751134002981806252273)
                ·
                  refine ⟨15896813350502236354689205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21195751134002981806252273 15896813350502236354689205)
                  ·
                    refine ⟨1490326251609584658252113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15896813350502236354689205 1490326251609584658252113)
                    ·
                      refine ⟨1117744688707188493689085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490326251609584658252113 1117744688707188493689085)
                      ·
                        rfl

theorem cell23_2176800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2176800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176800 prefixEnd_2176800 := by exact prefixLift 2176800
  have htrace : WordTrace (prefixWord ++ tailWord_2176800) baseStart_2176800 baseEnd_2176800 := by
    simpa [prefixWord, tailWord_2176800, baseEnd_2176800] using wordTrace_append hprefix tailTrace_2176800
  have hstable : (prefixWord ++ tailWord_2176800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176800).length < 2 ^ (prefixWord ++ tailWord_2176800).sum := by decide
  have hdescent : baseEnd_2176800 < baseStart_2176800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176814 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_2176814 : Nat := 118140960795 + 2176814 * 2 ^ 59
def prefixEnd_2176814 : Nat := 4983230072969 + 3 ^ 40 * 2176814 * 2
def baseEnd_2176814 : Nat := 124194653048483493212669

theorem tailTrace_2176814 : CollatzResearch.WordTrace tailWord_2176814 prefixEnd_2176814 124194653048483493212669 := by
  unfold tailWord_2176814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924366141972765384771187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52929952757188082052112997 9924366141972765384771187)
  ·
    refine ⟨14886549212959148077156781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9924366141972765384771187 14886549212959148077156781)
    ·
      refine ⟨5582455954859680528933793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14886549212959148077156781 5582455954859680528933793)
      ·
        refine ⟨4186841966144760396700345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5582455954859680528933793 4186841966144760396700345)
        ·
          refine ⟨3140131474608570297525259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4186841966144760396700345 3140131474608570297525259)
          ·
            refine ⟨4710197211912855446287889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140131474608570297525259 4710197211912855446287889)
            ·
              refine ⟨3532647908934641584715917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4710197211912855446287889 3532647908934641584715917)
              ·
                refine ⟨1324742965850490594268469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3532647908934641584715917 1324742965850490594268469)
                ·
                  refine ⟨124194653048483493212669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1324742965850490594268469 124194653048483493212669)
                  ·
                    rfl

theorem cell23_2176814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_2176814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176814 prefixEnd_2176814 := by exact prefixLift 2176814
  have htrace : WordTrace (prefixWord ++ tailWord_2176814) baseStart_2176814 baseEnd_2176814 := by
    simpa [prefixWord, tailWord_2176814, baseEnd_2176814] using wordTrace_append hprefix tailTrace_2176814
  have hstable : (prefixWord ++ tailWord_2176814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176814).length < 2 ^ (prefixWord ++ tailWord_2176814).sum := by decide
  have hdescent : baseEnd_2176814 < baseStart_2176814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176840 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_2176840 : Nat := 118140960795 + 2176840 * 2 ^ 59
def prefixEnd_2176840 : Nat := 4983230072969 + 3 ^ 40 * 2176840 * 2
def baseEnd_2176840 : Nat := 372588409311122779062967

theorem tailTrace_2176840 : CollatzResearch.WordTrace tailWord_2176840 prefixEnd_2176840 372588409311122779062967 := by
  unfold tailWord_2176840
  simp only [CollatzResearch.WordTrace]
  refine ⟨39697938716843964759307987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52930584955791953012410649 39697938716843964759307987)
  ·
    refine ⟨59546908075265947138961981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39697938716843964759307987 59546908075265947138961981)
    ·
      refine ⟨22330090528224730177110743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59546908075265947138961981 22330090528224730177110743)
      ·
        refine ⟨33495135792337095265666115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22330090528224730177110743 33495135792337095265666115)
        ·
          refine ⟨50242703688505642898499173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33495135792337095265666115 50242703688505642898499173)
          ·
            refine ⟨9420506941594808043468595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50242703688505642898499173 9420506941594808043468595)
            ·
              refine ⟨14130760412392212065202893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420506941594808043468595 14130760412392212065202893)
              ·
                refine ⟨5299035154647079524451085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14130760412392212065202893 5299035154647079524451085)
                ·
                  refine ⟨1987138182992654821669157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5299035154647079524451085 1987138182992654821669157)
                  ·
                    refine ⟨372588409311122779062967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987138182992654821669157 372588409311122779062967)
                    ·
                      rfl

theorem cell23_2176840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_2176840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176840 prefixEnd_2176840 := by exact prefixLift 2176840
  have htrace : WordTrace (prefixWord ++ tailWord_2176840) baseStart_2176840 baseEnd_2176840 := by
    simpa [prefixWord, tailWord_2176840, baseEnd_2176840] using wordTrace_append hprefix tailTrace_2176840
  have hstable : (prefixWord ++ tailWord_2176840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176840).length < 2 ^ (prefixWord ++ tailWord_2176840).sum := by decide
  have hdescent : baseEnd_2176840 < baseStart_2176840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176850 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_2176850 : Nat := 118140960795 + 2176850 * 2 ^ 59
def prefixEnd_2176850 : Nat := 4983230072969 + 3 ^ 40 * 2176850 * 2
def baseEnd_2176850 : Nat := 1117770362739913298063855

theorem tailTrace_2176850 : CollatzResearch.WordTrace tailWord_2176850 prefixEnd_2176850 1117770362739913298063855 := by
  unfold tailWord_2176850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19849060540912925306620001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52930828109101134150986669 19849060540912925306620001)
  ·
    refine ⟨14886795405684693979965001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19849060540912925306620001 14886795405684693979965001)
    ·
      refine ⟨11165096554263520484973751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14886795405684693979965001 11165096554263520484973751)
      ·
        refine ⟨16747644831395280727460627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11165096554263520484973751 16747644831395280727460627)
        ·
          refine ⟨25121467247092921091190941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16747644831395280727460627 25121467247092921091190941)
          ·
            refine ⟨9420550217659845409196603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25121467247092921091190941 9420550217659845409196603)
            ·
              refine ⟨14130825326489768113794905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420550217659845409196603 14130825326489768113794905)
              ·
                refine ⟨10598118994867326085346179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14130825326489768113794905 10598118994867326085346179)
                ·
                  refine ⟨15897178492300989128019269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10598118994867326085346179 15897178492300989128019269)
                  ·
                    refine ⟨2980720967306435461503613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15897178492300989128019269 2980720967306435461503613)
                    ·
                      refine ⟨1117770362739913298063855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980720967306435461503613 1117770362739913298063855)
                      ·
                        rfl

theorem cell23_2176850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_2176850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176850 prefixEnd_2176850 := by exact prefixLift 2176850
  have htrace : WordTrace (prefixWord ++ tailWord_2176850) baseStart_2176850 baseEnd_2176850 := by
    simpa [prefixWord, tailWord_2176850, baseEnd_2176850] using wordTrace_append hprefix tailTrace_2176850
  have hstable : (prefixWord ++ tailWord_2176850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176850).length < 2 ^ (prefixWord ++ tailWord_2176850).sum := by decide
  have hdescent : baseEnd_2176850 < baseStart_2176850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176883 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 5, 5]
def baseStart_2176883 : Nat := 118140960795 + 2176883 * 2 ^ 59
def prefixEnd_2176883 : Nat := 4983230072969 + 3 ^ 40 * 2176883 * 2
def baseEnd_2176883 : Nat := 372595769200503889650401

theorem tailTrace_2176883 : CollatzResearch.WordTrace tailWord_2176883 prefixEnd_2176883 372595769200503889650401 := by
  unfold tailWord_2176883
  simp only [CollatzResearch.WordTrace]
  refine ⟨79397445772532147862431303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52931630515021431908287535 79397445772532147862431303)
  ·
    refine ⟨119096168658798221793646955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79397445772532147862431303 119096168658798221793646955)
    ·
      refine ⟨178644252988197332690470433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119096168658798221793646955 178644252988197332690470433)
      ·
        refine ⟨133983189741147999517852825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178644252988197332690470433 133983189741147999517852825)
        ·
          refine ⟨100487392305860999638389619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133983189741147999517852825 100487392305860999638389619)
          ·
            refine ⟨150731088458791499457584429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100487392305860999638389619 150731088458791499457584429)
            ·
              refine ⟨56524158172046812296594161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150731088458791499457584429 56524158172046812296594161)
              ·
                refine ⟨42393118629035109222445621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56524158172046812296594161 42393118629035109222445621)
                ·
                  refine ⟨3974354871472041489604277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42393118629035109222445621 3974354871472041489604277)
                  ·
                    refine ⟨372595769200503889650401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3974354871472041489604277 372595769200503889650401)
                    ·
                      rfl

theorem cell23_2176883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 5].length) (baseStart_2176883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176883 prefixEnd_2176883 := by exact prefixLift 2176883
  have htrace : WordTrace (prefixWord ++ tailWord_2176883) baseStart_2176883 baseEnd_2176883 := by
    simpa [prefixWord, tailWord_2176883, baseEnd_2176883] using wordTrace_append hprefix tailTrace_2176883
  have hstable : (prefixWord ++ tailWord_2176883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176883).length < 2 ^ (prefixWord ++ tailWord_2176883).sum := by decide
  have hdescent : baseEnd_2176883 < baseStart_2176883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176893 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2176893 : Nat := 118140960795 + 2176893 * 2 ^ 59
def prefixEnd_2176893 : Nat := 4983230072969 + 3 ^ 40 * 2176893 * 2
def baseEnd_2176893 : Nat := 1117792442408056629826157

theorem tailTrace_2176893 : CollatzResearch.WordTrace tailWord_2176893 prefixEnd_2176893 1117792442408056629826157 := by
  unfold tailWord_2176893
  simp only [CollatzResearch.WordTrace]
  refine ⟨79397810502495919570295333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52931873668330613046863555 79397810502495919570295333)
  ·
    refine ⟨14887089469217984919430375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79397810502495919570295333 14887089469217984919430375)
    ·
      refine ⟨22330634203826977379145563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14887089469217984919430375 22330634203826977379145563)
      ·
        refine ⟨33495951305740466068718345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22330634203826977379145563 33495951305740466068718345)
        ·
          refine ⟨25121963479305349551538759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33495951305740466068718345 25121963479305349551538759)
          ·
            refine ⟨37682945218958024327308139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25121963479305349551538759 37682945218958024327308139)
            ·
              refine ⟨56524417828437036490962209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37682945218958024327308139 56524417828437036490962209)
              ·
                refine ⟨42393313371327777368221657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56524417828437036490962209 42393313371327777368221657)
                ·
                  refine ⟨31794985028495833026166243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42393313371327777368221657 31794985028495833026166243)
                  ·
                    refine ⟨47692477542743749539249365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31794985028495833026166243 47692477542743749539249365)
                    ·
                      refine ⟨1117792442408056629826157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47692477542743749539249365 1117792442408056629826157)
                      ·
                        rfl

theorem cell23_2176893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2176893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176893 prefixEnd_2176893 := by exact prefixLift 2176893
  have htrace : WordTrace (prefixWord ++ tailWord_2176893) baseStart_2176893 baseEnd_2176893 := by
    simpa [prefixWord, tailWord_2176893, baseEnd_2176893] using wordTrace_append hprefix tailTrace_2176893
  have hstable : (prefixWord ++ tailWord_2176893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176893).length < 2 ^ (prefixWord ++ tailWord_2176893).sum := by decide
  have hdescent : baseEnd_2176893 < baseStart_2176893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176904 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 6]
def baseStart_2176904 : Nat := 118140960795 + 2176904 * 2 ^ 59
def prefixEnd_2176904 : Nat := 4983230072969 + 3 ^ 40 * 2176904 * 2
def baseEnd_2176904 : Nat := 124199787855028454087623

theorem tailTrace_2176904 : CollatzResearch.WordTrace tailWord_2176904 prefixEnd_2176904 124199787855028454087623 := by
  unfold tailWord_2176904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39699105852728034224472883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52932141136970712299297177 39699105852728034224472883)
  ·
    refine ⟨59548658779092051336709325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39699105852728034224472883 59548658779092051336709325)
    ·
      refine ⟨22330747042159519251265997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59548658779092051336709325 22330747042159519251265997)
      ·
        refine ⟨8374030140809819719224749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22330747042159519251265997 8374030140809819719224749)
        ·
          refine ⟨3140261302803682394709281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8374030140809819719224749 3140261302803682394709281)
          ·
            refine ⟨2355195977102761796031961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140261302803682394709281 2355195977102761796031961)
            ·
              refine ⟨1766396982827071347023971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355195977102761796031961 1766396982827071347023971)
              ·
                refine ⟨2649595474240607020535957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766396982827071347023971 2649595474240607020535957)
                ·
                  refine ⟨124199787855028454087623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2649595474240607020535957 124199787855028454087623)
                  ·
                    rfl

theorem cell23_2176904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 6].length) (baseStart_2176904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176904 prefixEnd_2176904 := by exact prefixLift 2176904
  have htrace : WordTrace (prefixWord ++ tailWord_2176904) baseStart_2176904 baseEnd_2176904 := by
    simpa [prefixWord, tailWord_2176904, baseEnd_2176904] using wordTrace_append hprefix tailTrace_2176904
  have hstable : (prefixWord ++ tailWord_2176904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176904).length < 2 ^ (prefixWord ++ tailWord_2176904).sum := by decide
  have hdescent : baseEnd_2176904 < baseStart_2176904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176918 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2176918 : Nat := 118140960795 + 2176918 * 2 ^ 59
def prefixEnd_2176918 : Nat := 4983230072969 + 3 ^ 40 * 2176918 * 2
def baseEnd_2176918 : Nat := 1117805279424419032013543

theorem tailTrace_2176918 : CollatzResearch.WordTrace tailWord_2176918 prefixEnd_2176918 1117805279424419032013543 := by
  unfold tailWord_2176918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962420145462834302497213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52932481551603565893303605 4962420145462834302497213)
  ·
    refine ⟨1860907554548562863436455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4962420145462834302497213 1860907554548562863436455)
    ·
      refine ⟨2791361331822844295154683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860907554548562863436455 2791361331822844295154683)
      ·
        refine ⟨4187041997734266442732025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791361331822844295154683 4187041997734266442732025)
        ·
          refine ⟨3140281498300699832049019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4187041997734266442732025 3140281498300699832049019)
          ·
            refine ⟨4710422247451049748073529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140281498300699832049019 4710422247451049748073529)
            ·
              refine ⟨3532816685588287311055147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4710422247451049748073529 3532816685588287311055147)
              ·
                refine ⟨5299225028382430966582721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3532816685588287311055147 5299225028382430966582721)
                ·
                  refine ⟨3974418771286823224937041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299225028382430966582721 3974418771286823224937041)
                  ·
                    refine ⟨2980814078465117418702781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974418771286823224937041 2980814078465117418702781)
                    ·
                      refine ⟨1117805279424419032013543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980814078465117418702781 1117805279424419032013543)
                      ·
                        rfl

theorem cell23_2176918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2176918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176918 prefixEnd_2176918 := by exact prefixLift 2176918
  have htrace : WordTrace (prefixWord ++ tailWord_2176918) baseStart_2176918 baseEnd_2176918 := by
    simpa [prefixWord, tailWord_2176918, baseEnd_2176918] using wordTrace_append hprefix tailTrace_2176918
  have hstable : (prefixWord ++ tailWord_2176918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176918).length < 2 ^ (prefixWord ++ tailWord_2176918).sum := by decide
  have hdescent : baseEnd_2176918 < baseStart_2176918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176924 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2176924 : Nat := 118140960795 + 2176924 * 2 ^ 59
def prefixEnd_2176924 : Nat := 4983230072969 + 3 ^ 40 * 2176924 * 2
def baseEnd_2176924 : Nat := 1117808360308346008538515

theorem tailTrace_2176924 : CollatzResearch.WordTrace tailWord_2176924 prefixEnd_2176924 1117808360308346008538515 := by
  unfold tailWord_2176924
  simp only [CollatzResearch.WordTrace]
  refine ⟨39699470582691805932336913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52932627443589074576449217 39699470582691805932336913)
  ·
    refine ⟨29774602937018854449252685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39699470582691805932336913 29774602937018854449252685)
    ·
      refine ⟨11165476101382070418469757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29774602937018854449252685 11165476101382070418469757)
      ·
        refine ⟨4187053538018276406926159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11165476101382070418469757 4187053538018276406926159)
        ·
          refine ⟨6280580307027414610389239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187053538018276406926159 6280580307027414610389239)
          ·
            refine ⟨9420870460541121915583859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280580307027414610389239 9420870460541121915583859)
            ·
              refine ⟨14131305690811682873375789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9420870460541121915583859 14131305690811682873375789)
              ·
                refine ⟨5299239634054381077515921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14131305690811682873375789 5299239634054381077515921)
                ·
                  refine ⟨3974429725540785808136941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299239634054381077515921 3974429725540785808136941)
                  ·
                    refine ⟨1490411147077794678051353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3974429725540785808136941 1490411147077794678051353)
                    ·
                      refine ⟨1117808360308346008538515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490411147077794678051353 1117808360308346008538515)
                      ·
                        rfl

theorem cell23_2176924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2176924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176924 prefixEnd_2176924 := by exact prefixLift 2176924
  have htrace : WordTrace (prefixWord ++ tailWord_2176924) baseStart_2176924 baseEnd_2176924 := by
    simpa [prefixWord, tailWord_2176924, baseEnd_2176924] using wordTrace_append hprefix tailTrace_2176924
  have hstable : (prefixWord ++ tailWord_2176924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176924).length < 2 ^ (prefixWord ++ tailWord_2176924).sum := by decide
  have hdescent : baseEnd_2176924 < baseStart_2176924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176937 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 7, 2, 2]
def baseStart_2176937 : Nat := 118140960795 + 2176937 * 2 ^ 59
def prefixEnd_2176937 : Nat := 4983230072969 + 3 ^ 40 * 2176937 * 2
def baseEnd_2176937 : Nat := 1117815035556854457675955

theorem tailTrace_2176937 : CollatzResearch.WordTrace tailWord_2176937 prefixEnd_2176937 1117815035556854457675955 := by
  unfold tailWord_2176937
  simp only [CollatzResearch.WordTrace]
  refine ⟨79399415314336515084897065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52932943542891010056598043 79399415314336515084897065)
  ·
    refine ⟨59549561485752386313672799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79399415314336515084897065 59549561485752386313672799)
    ·
      refine ⟨89324342228628579470509199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59549561485752386313672799 89324342228628579470509199)
      ·
        refine ⟨133986513342942869205763799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89324342228628579470509199 133986513342942869205763799)
        ·
          refine ⟨200979770014414303808645699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133986513342942869205763799 200979770014414303808645699)
          ·
            refine ⟨301469655021621455712968549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200979770014414303808645699 301469655021621455712968549)
            ·
              refine ⟨56525560316554022946181603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301469655021621455712968549 56525560316554022946181603)
              ·
                refine ⟨84788340474831034419272405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56525560316554022946181603 84788340474831034419272405)
                ·
                  refine ⟨1987226729878852369201697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 84788340474831034419272405 1987226729878852369201697)
                  ·
                    refine ⟨1490420047409139276901273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987226729878852369201697 1490420047409139276901273)
                    ·
                      refine ⟨1117815035556854457675955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490420047409139276901273 1117815035556854457675955)
                      ·
                        rfl

theorem cell23_2176937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2, 2].length) (baseStart_2176937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176937 prefixEnd_2176937 := by exact prefixLift 2176937
  have htrace : WordTrace (prefixWord ++ tailWord_2176937) baseStart_2176937 baseEnd_2176937 := by
    simpa [prefixWord, tailWord_2176937, baseEnd_2176937] using wordTrace_append hprefix tailTrace_2176937
  have hstable : (prefixWord ++ tailWord_2176937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176937).length < 2 ^ (prefixWord ++ tailWord_2176937).sum := by decide
  have hdescent : baseEnd_2176937 < baseStart_2176937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176940 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_2176940 : Nat := 118140960795 + 2176940 * 2 ^ 59
def prefixEnd_2176940 : Nat := 4983230072969 + 3 ^ 40 * 2176940 * 2
def baseEnd_2176940 : Nat := 1117816575998817945938441

theorem tailTrace_2176940 : CollatzResearch.WordTrace tailWord_2176940 prefixEnd_2176940 1117816575998817945938441 := by
  unfold tailWord_2176940
  simp only [CollatzResearch.WordTrace]
  refine ⟨39699762366662823298628137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52933016488883764398170849 39699762366662823298628137)
  ·
    refine ⟨29774821774997117473971103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39699762366662823298628137 29774821774997117473971103)
    ·
      refine ⟨44662232662495676210956655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29774821774997117473971103 44662232662495676210956655)
      ·
        refine ⟨66993348993743514316434983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44662232662495676210956655 66993348993743514316434983)
        ·
          refine ⟨100490023490615271474652475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66993348993743514316434983 100490023490615271474652475)
          ·
            refine ⟨150735035235922907211978713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100490023490615271474652475 150735035235922907211978713)
            ·
              refine ⟨113051276426942180408984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150735035235922907211978713 113051276426942180408984035)
              ·
                refine ⟨169576914640413270613476053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113051276426942180408984035 169576914640413270613476053)
                ·
                  refine ⟨3974458936884686030003345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169576914640413270613476053 3974458936884686030003345)
                  ·
                    refine ⟨2980844202663514522502509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974458936884686030003345 2980844202663514522502509)
                    ·
                      refine ⟨1117816575998817945938441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980844202663514522502509 1117816575998817945938441)
                      ·
                        rfl

theorem cell23_2176940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_2176940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176940 prefixEnd_2176940 := by exact prefixLift 2176940
  have htrace : WordTrace (prefixWord ++ tailWord_2176940) baseStart_2176940 baseEnd_2176940 := by
    simpa [prefixWord, tailWord_2176940, baseEnd_2176940] using wordTrace_append hprefix tailTrace_2176940
  have hstable : (prefixWord ++ tailWord_2176940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176940).length < 2 ^ (prefixWord ++ tailWord_2176940).sum := by decide
  have hdescent : baseEnd_2176940 < baseStart_2176940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176942 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2176942 : Nat := 118140960795 + 2176942 * 2 ^ 59
def prefixEnd_2176942 : Nat := 4983230072969 + 3 ^ 40 * 2176942 * 2
def baseEnd_2176942 : Nat := 372605867653375646037811

theorem tailTrace_2176942 : CollatzResearch.WordTrace tailWord_2176942 prefixEnd_2176942 372605867653375646037811 := by
  unfold tailWord_2176942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924949709914800117353635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52933065119545600625886053 9924949709914800117353635)
  ·
    refine ⟨14887424564872200176030453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9924949709914800117353635 14887424564872200176030453)
    ·
      refine ⟨1395696052956768766502855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14887424564872200176030453 1395696052956768766502855)
      ·
        refine ⟨2093544079435153149754283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395696052956768766502855 2093544079435153149754283)
        ·
          refine ⟨3140316119152729724631425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093544079435153149754283 3140316119152729724631425)
          ·
            refine ⟨2355237089364547293473569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140316119152729724631425 2355237089364547293473569)
            ·
              refine ⟨1766427817023410470105177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355237089364547293473569 1766427817023410470105177)
              ·
                refine ⟨1324820862767557852578883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766427817023410470105177 1324820862767557852578883)
                ·
                  refine ⟨1987231294151336778868325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324820862767557852578883 1987231294151336778868325)
                  ·
                    refine ⟨372605867653375646037811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987231294151336778868325 372605867653375646037811)
                    ·
                      rfl

theorem cell23_2176942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2176942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176942 prefixEnd_2176942 := by exact prefixLift 2176942
  have htrace : WordTrace (prefixWord ++ tailWord_2176942) baseStart_2176942 baseEnd_2176942 := by
    simpa [prefixWord, tailWord_2176942, baseEnd_2176942] using wordTrace_append hprefix tailTrace_2176942
  have hstable : (prefixWord ++ tailWord_2176942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176942).length < 2 ^ (prefixWord ++ tailWord_2176942).sum := by decide
  have hdescent : baseEnd_2176942 < baseStart_2176942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176947 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 2, 4]
def baseStart_2176947 : Nat := 118140960795 + 2176947 * 2 ^ 59
def prefixEnd_2176947 : Nat := 4983230072969 + 3 ^ 40 * 2176947 * 2
def baseEnd_2176947 : Nat := 372606723454466472850303

theorem tailTrace_2176947 : CollatzResearch.WordTrace tailWord_2176947 prefixEnd_2176947 372606723454466472850303 := by
  unfold tailWord_2176947
  simp only [CollatzResearch.WordTrace]
  refine ⟨79399780044300286792761095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52933186696200191195174063 79399780044300286792761095)
  ·
    refine ⟨119099670066450430189141643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79399780044300286792761095 119099670066450430189141643)
    ·
      refine ⟨178649505099675645283712465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119099670066450430189141643 178649505099675645283712465)
      ·
        refine ⟨133987128824756733962784349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178649505099675645283712465 133987128824756733962784349)
        ·
          refine ⟨50245173309283775236044131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133987128824756733962784349 50245173309283775236044131)
          ·
            refine ⟨75367759963925662854066197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50245173309283775236044131 75367759963925662854066197)
            ·
              refine ⟨3532863748309015446284353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75367759963925662854066197 3532863748309015446284353)
              ·
                refine ⟨2649647811231761584713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3532863748309015446284353 2649647811231761584713265)
                ·
                  refine ⟨1987235858423821188534949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649647811231761584713265 1987235858423821188534949)
                  ·
                    refine ⟨372606723454466472850303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987235858423821188534949 372606723454466472850303)
                    ·
                      rfl

theorem cell23_2176947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 4].length) (baseStart_2176947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176947 prefixEnd_2176947 := by exact prefixLift 2176947
  have htrace : WordTrace (prefixWord ++ tailWord_2176947) baseStart_2176947 baseEnd_2176947 := by
    simpa [prefixWord, tailWord_2176947, baseEnd_2176947] using wordTrace_append hprefix tailTrace_2176947
  have hstable : (prefixWord ++ tailWord_2176947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176947).length < 2 ^ (prefixWord ++ tailWord_2176947).sum := by decide
  have hdescent : baseEnd_2176947 < baseStart_2176947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176957 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2176957 : Nat := 118140960795 + 2176957 * 2 ^ 59
def prefixEnd_2176957 : Nat := 4983230072969 + 3 ^ 40 * 2176957 * 2
def baseEnd_2176957 : Nat := 1117825305169944379425863

theorem tailTrace_2176957 : CollatzResearch.WordTrace tailWord_2176957 prefixEnd_2176957 1117825305169944379425863 := by
  unfold tailWord_2176957
  simp only [CollatzResearch.WordTrace]
  refine ⟨79400144774264058500625125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52933429849509372333750083 79400144774264058500625125)
  ·
    refine ⟨14887527145174510968867211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79400144774264058500625125 14887527145174510968867211)
    ·
      refine ⟨22331290717761766453300817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14887527145174510968867211 22331290717761766453300817)
      ·
        refine ⟨16748468038321324839975613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22331290717761766453300817 16748468038321324839975613)
        ·
          refine ⟨6280675514370496814990855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16748468038321324839975613 6280675514370496814990855)
          ·
            refine ⟨9421013271555745222486283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280675514370496814990855 9421013271555745222486283)
            ·
              refine ⟨14131519907333617833729425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9421013271555745222486283 14131519907333617833729425)
              ·
                refine ⟨10598639930500213375297069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14131519907333617833729425 10598639930500213375297069)
                ·
                  refine ⟨3974489973937580015736401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10598639930500213375297069 3974489973937580015736401)
                  ·
                    refine ⟨2980867480453185011802301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974489973937580015736401 2980867480453185011802301)
                    ·
                      refine ⟨1117825305169944379425863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980867480453185011802301 1117825305169944379425863)
                      ·
                        rfl

theorem cell23_2176957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2176957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176957 prefixEnd_2176957 := by exact prefixLift 2176957
  have htrace : WordTrace (prefixWord ++ tailWord_2176957) baseStart_2176957 baseEnd_2176957 := by
    simpa [prefixWord, tailWord_2176957, baseEnd_2176957] using wordTrace_append hprefix tailTrace_2176957
  have hstable : (prefixWord ++ tailWord_2176957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176957).length < 2 ^ (prefixWord ++ tailWord_2176957).sum := by decide
  have hdescent : baseEnd_2176957 < baseStart_2176957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176988 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2176988 : Nat := 118140960795 + 2176988 * 2 ^ 59
def prefixEnd_2176988 : Nat := 4983230072969 + 3 ^ 40 * 2176988 * 2
def baseEnd_2176988 : Nat := 1117841223070233758138221

theorem tailTrace_2176988 : CollatzResearch.WordTrace tailWord_2176988 prefixEnd_2176988 1117841223070233758138221 := by
  unfold tailWord_2176988
  simp only [CollatzResearch.WordTrace]
  refine ⟨39700637718575875397501809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52934183624767833863335745 39700637718575875397501809)
  ·
    refine ⟨29775478288931906548126357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39700637718575875397501809 29775478288931906548126357)
    ·
      refine ⟨1395725544793683119443423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29775478288931906548126357 1395725544793683119443423)
      ·
        refine ⟨2093588317190524679165135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395725544793683119443423 2093588317190524679165135)
        ·
          refine ⟨3140382475785787018747703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093588317190524679165135 3140382475785787018747703)
          ·
            refine ⟨4710573713678680528121555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140382475785787018747703 4710573713678680528121555)
            ·
              refine ⟨7065860570518020792182333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4710573713678680528121555 7065860570518020792182333)
              ·
                refine ⟨2649697713944257797068375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7065860570518020792182333 2649697713944257797068375)
                ·
                  refine ⟨3974546570916386695602563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649697713944257797068375 3974546570916386695602563)
                  ·
                    refine ⟨5961819856374580043403845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3974546570916386695602563 5961819856374580043403845)
                    ·
                      refine ⟨1117841223070233758138221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5961819856374580043403845 1117841223070233758138221)
                      ·
                        rfl

theorem cell23_2176988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2176988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176988 prefixEnd_2176988 := by exact prefixLift 2176988
  have htrace : WordTrace (prefixWord ++ tailWord_2176988) baseStart_2176988 baseEnd_2176988 := by
    simpa [prefixWord, tailWord_2176988, baseEnd_2176988] using wordTrace_append hprefix tailTrace_2176988
  have hstable : (prefixWord ++ tailWord_2176988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176988).length < 2 ^ (prefixWord ++ tailWord_2176988).sum := by decide
  have hdescent : baseEnd_2176988 < baseStart_2176988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176991 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 1, 2, 3]
def baseStart_2176991 : Nat := 118140960795 + 2176991 * 2 ^ 59
def prefixEnd_2176991 : Nat := 4983230072969 + 3 ^ 40 * 2176991 * 2
def baseEnd_2176991 : Nat := 1117842763512197246400707

theorem tailTrace_2176991 : CollatzResearch.WordTrace tailWord_2176991 prefixEnd_2176991 1117842763512197246400707 := by
  unfold tailWord_2176991
  simp only [CollatzResearch.WordTrace]
  refine ⟨79401384856140882307362827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52934256570760588204908551 79401384856140882307362827)
  ·
    refine ⟨119102077284211323461044241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79401384856140882307362827 119102077284211323461044241)
    ·
      refine ⟨89326557963158492595783181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119102077284211323461044241 89326557963158492595783181)
      ·
        refine ⟨33497459236184434723418693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89326557963158492595783181 33497459236184434723418693)
        ·
          refine ⟨6280773606784581510641005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33497459236184434723418693 6280773606784581510641005)
          ·
            refine ⟨2355290102544218066490377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6280773606784581510641005 2355290102544218066490377)
            ·
              refine ⟨1766467576908163549867783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355290102544218066490377 1766467576908163549867783)
              ·
                refine ⟨2649701365362245324801675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766467576908163549867783 2649701365362245324801675)
                ·
                  refine ⟨3974552048043367987202513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649701365362245324801675 3974552048043367987202513)
                  ·
                    refine ⟨2980914036032525990401885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3974552048043367987202513 2980914036032525990401885)
                    ·
                      refine ⟨1117842763512197246400707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2980914036032525990401885 1117842763512197246400707)
                      ·
                        rfl

theorem cell23_2176991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_2176991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2176991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2176991 prefixEnd_2176991 := by exact prefixLift 2176991
  have htrace : WordTrace (prefixWord ++ tailWord_2176991) baseStart_2176991 baseEnd_2176991 := by
    simpa [prefixWord, tailWord_2176991, baseEnd_2176991] using wordTrace_append hprefix tailTrace_2176991
  have hstable : (prefixWord ++ tailWord_2176991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176991).length < 2 ^ (prefixWord ++ tailWord_2176991).sum := by decide
  have hdescent : baseEnd_2176991 < baseStart_2176991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177020 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_2177020 : Nat := 118140960795 + 2177020 * 2 ^ 59
def prefixEnd_2177020 : Nat := 4983230072969 + 3 ^ 40 * 2177020 * 2
def baseEnd_2177020 : Nat := 372619218150392544312691

theorem tailTrace_2177020 : CollatzResearch.WordTrace tailWord_2177020 prefixEnd_2177020 372619218150392544312691 := by
  unfold tailWord_2177020
  simp only [CollatzResearch.WordTrace]
  refine ⟨39701221286517910130084257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52934961715357213506779009 39701221286517910130084257)
  ·
    refine ⟨29775915964888432597563193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39701221286517910130084257 29775915964888432597563193)
    ·
      refine ⟨22331936973666324448172395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29775915964888432597563193 22331936973666324448172395)
      ·
        refine ⟨33497905460499486672258593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22331936973666324448172395 33497905460499486672258593)
        ·
          refine ⟨25123429095374615004193945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33497905460499486672258593 25123429095374615004193945)
          ·
            refine ⟨18842571821530961253145459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25123429095374615004193945 18842571821530961253145459)
            ·
              refine ⟨28263857732296441879718189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18842571821530961253145459 28263857732296441879718189)
              ·
                refine ⟨10598946649611165704894321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28263857732296441879718189 10598946649611165704894321)
                ·
                  refine ⟨7949209987208374278670741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10598946649611165704894321 7949209987208374278670741)
                  ·
                    refine ⟨372619218150392544312691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7949209987208374278670741 372619218150392544312691)
                    ·
                      rfl

theorem cell23_2177020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_2177020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177020 prefixEnd_2177020 := by exact prefixLift 2177020
  have htrace : WordTrace (prefixWord ++ tailWord_2177020) baseStart_2177020 baseEnd_2177020 := by
    simpa [prefixWord, tailWord_2177020, baseEnd_2177020] using wordTrace_append hprefix tailTrace_2177020
  have hstable : (prefixWord ++ tailWord_2177020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177020).length < 2 ^ (prefixWord ++ tailWord_2177020).sum := by decide
  have hdescent : baseEnd_2177020 < baseStart_2177020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177031 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2177031 : Nat := 118140960795 + 2177031 * 2 ^ 59
def prefixEnd_2177031 : Nat := 4983230072969 + 3 ^ 40 * 2177031 * 2
def baseEnd_2177031 : Nat := 1117863302738377089900523

theorem tailTrace_2177031 : CollatzResearch.WordTrace tailWord_2177031 prefixEnd_2177031 1117863302738377089900523 := by
  unfold tailWord_2177031
  simp only [CollatzResearch.WordTrace]
  refine ⟨79402843775995969138818947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52935229183997312759212631 79402843775995969138818947)
  ·
    refine ⟨119104265663993953708228421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79402843775995969138818947 119104265663993953708228421)
    ·
      refine ⟨22332049811998866320292829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119104265663993953708228421 22332049811998866320292829)
      ·
        refine ⟨8374518679499574870109811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22332049811998866320292829 8374518679499574870109811)
        ·
          refine ⟨12561778019249362305164717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374518679499574870109811 12561778019249362305164717)
          ·
            refine ⟨4710666757218510864436769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12561778019249362305164717 4710666757218510864436769)
            ·
              refine ⟨3533000067913883148327577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4710666757218510864436769 3533000067913883148327577)
              ·
                refine ⟨2649750050935412361245683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3533000067913883148327577 2649750050935412361245683)
                ·
                  refine ⟨3974625076403118541868525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649750050935412361245683 3974625076403118541868525)
                  ·
                    refine ⟨1490484403651169453200697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3974625076403118541868525 1490484403651169453200697)
                    ·
                      refine ⟨1117863302738377089900523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490484403651169453200697 1117863302738377089900523)
                      ·
                        rfl

theorem cell23_2177031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2177031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177031 prefixEnd_2177031 := by exact prefixLift 2177031
  have htrace : WordTrace (prefixWord ++ tailWord_2177031) baseStart_2177031 baseEnd_2177031 := by
    simpa [prefixWord, tailWord_2177031, baseEnd_2177031] using wordTrace_append hprefix tailTrace_2177031
  have hstable : (prefixWord ++ tailWord_2177031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177031).length < 2 ^ (prefixWord ++ tailWord_2177031).sum := by decide
  have hdescent : baseEnd_2177031 < baseStart_2177031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177077 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2177077 : Nat := 118140960795 + 2177077 * 2 ^ 59
def prefixEnd_2177077 : Nat := 4983230072969 + 3 ^ 40 * 2177077 * 2
def baseEnd_2177077 : Nat := 1117886922848483909925311

theorem tailTrace_2177077 : CollatzResearch.WordTrace tailWord_2177077 prefixEnd_2177077 1117886922848483909925311 := by
  unfold tailWord_2177077
  simp only [CollatzResearch.WordTrace]
  refine ⟨79404521533829318994993485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52936347689219545996662323 79404521533829318994993485)
  ·
    refine ⟨29776695575185994623122557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79404521533829318994993485 29776695575185994623122557)
    ·
      refine ⟨11166260840694747983670959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29776695575185994623122557 11166260840694747983670959)
      ·
        refine ⟨16749391261042121975506439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11166260840694747983670959 16749391261042121975506439)
        ·
          refine ⟨25124086891563182963259659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16749391261042121975506439 25124086891563182963259659)
          ·
            refine ⟨37686130337344774444889489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25124086891563182963259659 37686130337344774444889489)
            ·
              refine ⟨28264597753008580833667117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37686130337344774444889489 28264597753008580833667117)
              ·
                refine ⟨10599224157378217812625169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28264597753008580833667117 10599224157378217812625169)
                ·
                  refine ⟨7949418118033663359468877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10599224157378217812625169 7949418118033663359468877)
                  ·
                    refine ⟨2981031794262623759800829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7949418118033663359468877 2981031794262623759800829)
                    ·
                      refine ⟨1117886922848483909925311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981031794262623759800829 1117886922848483909925311)
                      ·
                        rfl

theorem cell23_2177077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2177077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177077 prefixEnd_2177077 := by exact prefixLift 2177077
  have htrace : WordTrace (prefixWord ++ tailWord_2177077) baseStart_2177077 baseEnd_2177077 := by
    simpa [prefixWord, tailWord_2177077, baseEnd_2177077] using wordTrace_append hprefix tailTrace_2177077
  have hstable : (prefixWord ++ tailWord_2177077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177077).length < 2 ^ (prefixWord ++ tailWord_2177077).sum := by decide
  have hdescent : baseEnd_2177077 < baseStart_2177077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177078 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2177078 : Nat := 118140960795 + 2177078 * 2 ^ 59
def prefixEnd_2177078 : Nat := 4983230072969 + 3 ^ 40 * 2177078 * 2
def baseEnd_2177078 : Nat := 1117887436329138406012807

theorem tailTrace_2177078 : CollatzResearch.WordTrace tailWord_2177078 prefixEnd_2177078 1117887436329138406012807 := by
  unfold tailWord_2177078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962784875426606010361243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52936372004550464110519925 4962784875426606010361243)
  ·
    refine ⟨7444177313139909015541865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962784875426606010361243 7444177313139909015541865)
    ·
      refine ⟨5583132984854931761656399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7444177313139909015541865 5583132984854931761656399)
      ·
        refine ⟨8374699477282397642484599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5583132984854931761656399 8374699477282397642484599)
        ·
          refine ⟨12562049215923596463726899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374699477282397642484599 12562049215923596463726899)
          ·
            refine ⟨18843073823885394695590349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12562049215923596463726899 18843073823885394695590349)
            ·
              refine ⟨7066152683957023010846381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18843073823885394695590349 7066152683957023010846381)
              ·
                refine ⟨2649807256483883629067393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7066152683957023010846381 2649807256483883629067393)
                ·
                  refine ⟨1987355442362912721800545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649807256483883629067393 1987355442362912721800545)
                  ·
                    refine ⟨1490516581772184541350409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987355442362912721800545 1490516581772184541350409)
                    ·
                      refine ⟨1117887436329138406012807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490516581772184541350409 1117887436329138406012807)
                      ·
                        rfl

theorem cell23_2177078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2177078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177078 prefixEnd_2177078 := by exact prefixLift 2177078
  have htrace : WordTrace (prefixWord ++ tailWord_2177078) baseStart_2177078 baseEnd_2177078 := by
    simpa [prefixWord, tailWord_2177078, baseEnd_2177078] using wordTrace_append hprefix tailTrace_2177078
  have hstable : (prefixWord ++ tailWord_2177078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177078).length < 2 ^ (prefixWord ++ tailWord_2177078).sum := by decide
  have hdescent : baseEnd_2177078 < baseStart_2177078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177097 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_2177097 : Nat := 118140960795 + 2177097 * 2 ^ 59
def prefixEnd_2177097 : Nat := 4983230072969 + 3 ^ 40 * 2177097 * 2
def baseEnd_2177097 : Nat := 372632397487191277225073

theorem tailTrace_2177097 : CollatzResearch.WordTrace tailWord_2177097 prefixEnd_2177097 372632397487191277225073 := by
  unfold tailWord_2177097
  simp only [CollatzResearch.WordTrace]
  refine ⟨79405250993756862410721545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52936833995837908273814363 79405250993756862410721545)
  ·
    refine ⟨59553938245317646808041159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79405250993756862410721545 59553938245317646808041159)
    ·
      refine ⟨89330907367976470212061739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59553938245317646808041159 89330907367976470212061739)
      ·
        refine ⟨133996361051964705318092609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89330907367976470212061739 133996361051964705318092609)
        ·
          refine ⟨100497270788973528988569457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133996361051964705318092609 100497270788973528988569457)
          ·
            refine ⟨75372953091730146741427093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100497270788973528988569457 75372953091730146741427093)
            ·
              refine ⟨3533107176174850628504395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75372953091730146741427093 3533107176174850628504395)
              ·
                refine ⟨5299660764262275942756593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533107176174850628504395 5299660764262275942756593)
                ·
                  refine ⟨3974745573196706957067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299660764262275942756593 3974745573196706957067445)
                  ·
                    refine ⟨372632397487191277225073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3974745573196706957067445 372632397487191277225073)
                    ·
                      rfl

theorem cell23_2177097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_2177097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177097 prefixEnd_2177097 := by exact prefixLift 2177097
  have htrace : WordTrace (prefixWord ++ tailWord_2177097) baseStart_2177097 baseEnd_2177097 := by
    simpa [prefixWord, tailWord_2177097, baseEnd_2177097] using wordTrace_append hprefix tailTrace_2177097
  have hstable : (prefixWord ++ tailWord_2177097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177097).length < 2 ^ (prefixWord ++ tailWord_2177097).sum := by decide
  have hdescent : baseEnd_2177097 < baseStart_2177097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177137 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_2177137 : Nat := 118140960795 + 2177137 * 2 ^ 59
def prefixEnd_2177137 : Nat := 4983230072969 + 3 ^ 40 * 2177137 * 2
def baseEnd_2177137 : Nat := 1117917731687753675175035

theorem tailTrace_2177137 : CollatzResearch.WordTrace tailWord_2177137 prefixEnd_2177137 1117917731687753675175035 := by
  unfold tailWord_2177137
  simp only [CollatzResearch.WordTrace]
  refine ⟨79406709913611949242177665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52937806609074632828118443 79406709913611949242177665)
  ·
    refine ⟨59555032435208961931633249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79406709913611949242177665 59555032435208961931633249)
    ·
      refine ⟨44666274326406721448724937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59555032435208961931633249 44666274326406721448724937)
      ·
        refine ⟨33499705744805041086543703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44666274326406721448724937 33499705744805041086543703)
        ·
          refine ⟨50249558617207561629815555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33499705744805041086543703 50249558617207561629815555)
          ·
            refine ⟨75374337925811342444723333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50249558617207561629815555 75374337925811342444723333)
            ·
              refine ⟨14132688361089626708385625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75374337925811342444723333 14132688361089626708385625)
              ·
                refine ⟨10599516270817220031289219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14132688361089626708385625 10599516270817220031289219)
                ·
                  refine ⟨15899274406225830046933829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10599516270817220031289219 15899274406225830046933829)
                  ·
                    refine ⟨2981113951167343133800093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15899274406225830046933829 2981113951167343133800093)
                    ·
                      refine ⟨1117917731687753675175035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981113951167343133800093 1117917731687753675175035)
                      ·
                        rfl

theorem cell23_2177137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_2177137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177137 prefixEnd_2177137 := by exact prefixLift 2177137
  have htrace : WordTrace (prefixWord ++ tailWord_2177137) baseStart_2177137 baseEnd_2177137 := by
    simpa [prefixWord, tailWord_2177137, baseEnd_2177137] using wordTrace_append hprefix tailTrace_2177137
  have hstable : (prefixWord ++ tailWord_2177137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177137).length < 2 ^ (prefixWord ++ tailWord_2177137).sum := by decide
  have hdescent : baseEnd_2177137 < baseStart_2177137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177161 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 1, 4]
def baseStart_2177161 : Nat := 118140960795 + 2177161 * 2 ^ 59
def prefixEnd_2177161 : Nat := 4983230072969 + 3 ^ 40 * 2177161 * 2
def baseEnd_2177161 : Nat := 372643351741153860424975

theorem tailTrace_2177161 : CollatzResearch.WordTrace tailWord_2177161 prefixEnd_2177161 372643351741153860424975 := by
  unfold tailWord_2177161
  simp only [CollatzResearch.WordTrace]
  refine ⟨79407585265525001341051337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52938390177016667560700891 79407585265525001341051337)
  ·
    refine ⟨59555688949143751005788503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79407585265525001341051337 59555688949143751005788503)
    ·
      refine ⟨89333533423715626508682755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59555688949143751005788503 89333533423715626508682755)
      ·
        refine ⟨134000300135573439763024133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89333533423715626508682755 134000300135573439763024133)
        ·
          refine ⟨25125056275420019955567025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134000300135573439763024133 25125056275420019955567025)
          ·
            refine ⟨18843792206565014966675269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25125056275420019955567025 18843792206565014966675269)
            ·
              refine ⟨3533211038730940306251613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18843792206565014966675269 3533211038730940306251613)
              ·
                refine ⟨1324954139524102614844355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3533211038730940306251613 1324954139524102614844355)
                ·
                  refine ⟨1987431209286153922266533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324954139524102614844355 1987431209286153922266533)
                  ·
                    refine ⟨372643351741153860424975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987431209286153922266533 372643351741153860424975)
                    ·
                      rfl

theorem cell23_2177161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 4].length) (baseStart_2177161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177161 prefixEnd_2177161 := by exact prefixLift 2177161
  have htrace : WordTrace (prefixWord ++ tailWord_2177161) baseStart_2177161 baseEnd_2177161 := by
    simpa [prefixWord, tailWord_2177161, baseEnd_2177161] using wordTrace_append hprefix tailTrace_2177161
  have hstable : (prefixWord ++ tailWord_2177161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177161).length < 2 ^ (prefixWord ++ tailWord_2177161).sum := by decide
  have hdescent : baseEnd_2177161 < baseStart_2177161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177274 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_2177274 : Nat := 118140960795 + 2177274 * 2 ^ 59
def prefixEnd_2177274 : Nat := 4983230072969 + 3 ^ 40 * 2177274 * 2
def baseEnd_2177274 : Nat := 1117988078537419639161905

theorem tailTrace_2177274 : CollatzResearch.WordTrace tailWord_2177274 prefixEnd_2177274 1117988078537419639161905 := by
  unfold tailWord_2177274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19852926678528905409978719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52941137809410414426609917 19852926678528905409978719)
  ·
    refine ⟨29779390017793358114968079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19852926678528905409978719 29779390017793358114968079)
    ·
      refine ⟨44669085026690037172452119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29779390017793358114968079 44669085026690037172452119)
      ·
        refine ⟨67003627540035055758678179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44669085026690037172452119 67003627540035055758678179)
        ·
          refine ⟨100505441310052583638017269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67003627540035055758678179 100505441310052583638017269)
          ·
            refine ⟨9422385122817429716064119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100505441310052583638017269 9422385122817429716064119)
            ·
              refine ⟨14133577684226144574096179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9422385122817429716064119 14133577684226144574096179)
              ·
                refine ⟨21200366526339216861144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14133577684226144574096179 21200366526339216861144269)
                ·
                  refine ⟨7950137447377206322929101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21200366526339216861144269 7950137447377206322929101)
                  ·
                    refine ⟨2981301542766452371098413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7950137447377206322929101 2981301542766452371098413)
                    ·
                      refine ⟨1117988078537419639161905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981301542766452371098413 1117988078537419639161905)
                      ·
                        rfl

theorem cell23_2177274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_2177274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177274 prefixEnd_2177274 := by exact prefixLift 2177274
  have htrace : WordTrace (prefixWord ++ tailWord_2177274) baseStart_2177274 baseEnd_2177274 := by
    simpa [prefixWord, tailWord_2177274, baseEnd_2177274] using wordTrace_append hprefix tailTrace_2177274
  have hstable : (prefixWord ++ tailWord_2177274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177274).length < 2 ^ (prefixWord ++ tailWord_2177274).sum := by decide
  have hdescent : baseEnd_2177274 < baseStart_2177274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177277 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2177277 : Nat := 118140960795 + 2177277 * 2 ^ 59
def prefixEnd_2177277 : Nat := 4983230072969 + 3 ^ 40 * 2177277 * 2
def baseEnd_2177277 : Nat := 372663206326461042474797

theorem tailTrace_2177277 : CollatzResearch.WordTrace tailWord_2177277 prefixEnd_2177277 372663206326461042474797 := by
  unfold tailWord_2177277
  simp only [CollatzResearch.WordTrace]
  refine ⟨79411816133104753152274085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52941210755403168768182723 79411816133104753152274085)
  ·
    refine ⟨14889715524957141216051391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79411816133104753152274085 14889715524957141216051391)
    ·
      refine ⟨22334573287435711824077087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14889715524957141216051391 22334573287435711824077087)
      ·
        refine ⟨33501859931153567736115631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22334573287435711824077087 33501859931153567736115631)
        ·
          refine ⟨50252789896730351604173447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33501859931153567736115631 50252789896730351604173447)
          ·
            refine ⟨75379184845095527406260171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50252789896730351604173447 75379184845095527406260171)
            ·
              refine ⟨113068777267643291109390257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75379184845095527406260171 113068777267643291109390257)
              ·
                refine ⟨84801582950732468332042693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113068777267643291109390257 84801582950732468332042693)
                ·
                  refine ⟨15900296803262337812258005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84801582950732468332042693 15900296803262337812258005)
                  ·
                    refine ⟨372663206326461042474797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15900296803262337812258005 372663206326461042474797)
                    ·
                      rfl

theorem cell23_2177277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2177277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177277 prefixEnd_2177277 := by exact prefixLift 2177277
  have htrace : WordTrace (prefixWord ++ tailWord_2177277) baseStart_2177277 baseEnd_2177277 := by
    simpa [prefixWord, tailWord_2177277, baseEnd_2177277] using wordTrace_append hprefix tailTrace_2177277
  have hstable : (prefixWord ++ tailWord_2177277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177277).length < 2 ^ (prefixWord ++ tailWord_2177277).sum := by decide
  have hdescent : baseEnd_2177277 < baseStart_2177277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177301 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_2177301 : Nat := 118140960795 + 2177301 * 2 ^ 59
def prefixEnd_2177301 : Nat := 4983230072969 + 3 ^ 40 * 2177301 * 2
def baseEnd_2177301 : Nat := 1118001942515091033524281

theorem tailTrace_2177301 : CollatzResearch.WordTrace tailWord_2177301 prefixEnd_2177301 1118001942515091033524281 := by
  unfold tailWord_2177301
  simp only [CollatzResearch.WordTrace]
  refine ⟨79412691485017805251147757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52941794323345203500765171 79412691485017805251147757)
  ·
    refine ⟨29779759306881676969180409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79412691485017805251147757 29779759306881676969180409)
    ·
      refine ⟨22334819480161257726885307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29779759306881676969180409 22334819480161257726885307)
      ·
        refine ⟨33502229220241886590327961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22334819480161257726885307 33502229220241886590327961)
        ·
          refine ⟨25126671915181414942745971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33502229220241886590327961 25126671915181414942745971)
          ·
            refine ⟨37690007872772122414118957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25126671915181414942745971 37690007872772122414118957)
            ·
              refine ⟨14133752952289545905294609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37690007872772122414118957 14133752952289545905294609)
              ·
                refine ⟨10600314714217159428970957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14133752952289545905294609 10600314714217159428970957)
                ·
                  refine ⟨3975118017831434785864109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10600314714217159428970957 3975118017831434785864109)
                  ·
                    refine ⟨1490669256686788044699041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3975118017831434785864109 1490669256686788044699041)
                    ·
                      refine ⟨1118001942515091033524281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490669256686788044699041 1118001942515091033524281)
                      ·
                        rfl

theorem cell23_2177301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_2177301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177301 prefixEnd_2177301 := by exact prefixLift 2177301
  have htrace : WordTrace (prefixWord ++ tailWord_2177301) baseStart_2177301 baseEnd_2177301 := by
    simpa [prefixWord, tailWord_2177301, baseEnd_2177301] using wordTrace_append hprefix tailTrace_2177301
  have hstable : (prefixWord ++ tailWord_2177301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177301).length < 2 ^ (prefixWord ++ tailWord_2177301).sum := by decide
  have hdescent : baseEnd_2177301 < baseStart_2177301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177307 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 8]
def baseStart_2177307 : Nat := 118140960795 + 2177307 * 2 ^ 59
def prefixEnd_2177307 : Nat := 4983230072969 + 3 ^ 40 * 2177307 * 2
def baseEnd_2177307 : Nat := 372668341133006003349751

theorem tailTrace_2177307 : CollatzResearch.WordTrace tailWord_2177307 prefixEnd_2177307 372668341133006003349751 := by
  unfold tailWord_2177307
  simp only [CollatzResearch.WordTrace]
  refine ⟨79412910322996068275866175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52941940215330712183910783 79412910322996068275866175)
  ·
    refine ⟨119119365484494102413799263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79412910322996068275866175 119119365484494102413799263)
    ·
      refine ⟨178679048226741153620698895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119119365484494102413799263 178679048226741153620698895)
      ·
        refine ⟨268018572340111730431048343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178679048226741153620698895 268018572340111730431048343)
        ·
          refine ⟨402027858510167595646572515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268018572340111730431048343 402027858510167595646572515)
          ·
            refine ⟨603041787765251393469858773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402027858510167595646572515 603041787765251393469858773)
            ·
              refine ⟨14133791900748079534449815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 603041787765251393469858773 14133791900748079534449815)
              ·
                refine ⟨21200687851122119301674723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14133791900748079534449815 21200687851122119301674723)
                ·
                  refine ⟨31801031776683178952512085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21200687851122119301674723 31801031776683178952512085)
                  ·
                    refine ⟨372668341133006003349751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31801031776683178952512085 372668341133006003349751)
                    ·
                      rfl

theorem cell23_2177307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_2177307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177307 prefixEnd_2177307 := by exact prefixLift 2177307
  have htrace : WordTrace (prefixWord ++ tailWord_2177307) baseStart_2177307 baseEnd_2177307 := by
    simpa [prefixWord, tailWord_2177307, baseEnd_2177307] using wordTrace_append hprefix tailTrace_2177307
  have hstable : (prefixWord ++ tailWord_2177307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177307).length < 2 ^ (prefixWord ++ tailWord_2177307).sum := by decide
  have hdescent : baseEnd_2177307 < baseStart_2177307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177331 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 1, 4, 2]
def baseStart_2177331 : Nat := 118140960795 + 2177331 * 2 ^ 59
def prefixEnd_2177331 : Nat := 4983230072969 + 3 ^ 40 * 2177331 * 2
def baseEnd_2177331 : Nat := 1118017346934725916149143

theorem tailTrace_2177331 : CollatzResearch.WordTrace tailWord_2177331 prefixEnd_2177331 1118017346934725916149143 := by
  unfold tailWord_2177331
  simp only [CollatzResearch.WordTrace]
  refine ⟨79413785674909120374739847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52942523783272746916493231 79413785674909120374739847)
  ·
    refine ⟨119120678512363680562109771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79413785674909120374739847 119120678512363680562109771)
    ·
      refine ⟨178681017768545520843164657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119120678512363680562109771 178681017768545520843164657)
      ·
        refine ⟨134010763326409140632373493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178681017768545520843164657 134010763326409140632373493)
        ·
          refine ⟨12563509061850856934285015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134010763326409140632373493 12563509061850856934285015)
          ·
            refine ⟨18845263592776285401427523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12563509061850856934285015 18845263592776285401427523)
            ·
              refine ⟨28267895389164428102141285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18845263592776285401427523 28267895389164428102141285)
              ·
                refine ⟨5300230385468330269151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28267895389164428102141285 5300230385468330269151491)
                ·
                  refine ⟨7950345578202495403727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300230385468330269151491 7950345578202495403727237)
                  ·
                    refine ⟨1490689795912967888198857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7950345578202495403727237 1490689795912967888198857)
                    ·
                      refine ⟨1118017346934725916149143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490689795912967888198857 1118017346934725916149143)
                      ·
                        rfl

theorem cell23_2177331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4, 2].length) (baseStart_2177331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177331 prefixEnd_2177331 := by exact prefixLift 2177331
  have htrace : WordTrace (prefixWord ++ tailWord_2177331) baseStart_2177331 baseEnd_2177331 := by
    simpa [prefixWord, tailWord_2177331, baseEnd_2177331] using wordTrace_append hprefix tailTrace_2177331
  have hstable : (prefixWord ++ tailWord_2177331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177331).length < 2 ^ (prefixWord ++ tailWord_2177331).sum := by decide
  have hdescent : baseEnd_2177331 < baseStart_2177331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177365 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2177365 : Nat := 118140960795 + 2177365 * 2 ^ 59
def prefixEnd_2177365 : Nat := 4983230072969 + 3 ^ 40 * 2177365 * 2
def baseEnd_2177365 : Nat := 1118034805276978783123987

theorem tailTrace_2177365 : CollatzResearch.WordTrace tailWord_2177365 prefixEnd_2177365 1118034805276978783123987 := by
  unfold tailWord_2177365
  simp only [CollatzResearch.WordTrace]
  refine ⟨79415025756785944181477549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52943350504523962787651699 79415025756785944181477549)
  ·
    refine ⟨29780634658794729068054081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79415025756785944181477549 29780634658794729068054081)
    ·
      refine ⟨22335475994096046801040561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29780634658794729068054081 22335475994096046801040561)
      ·
        refine ⟨16751606995572035100780421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22335475994096046801040561 16751606995572035100780421)
        ·
          refine ⟨3140926311669756581396329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16751606995572035100780421 3140926311669756581396329)
          ·
            refine ⟨2355694733752317436047247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3140926311669756581396329 2355694733752317436047247)
            ·
              refine ⟨3533542100628476154070871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355694733752317436047247 3533542100628476154070871)
              ·
                refine ⟨5300313150942714231106307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533542100628476154070871 5300313150942714231106307)
                ·
                  refine ⟨7950469726414071346659461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300313150942714231106307 7950469726414071346659461)
                  ·
                    refine ⟨1490713073702638377498649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7950469726414071346659461 1490713073702638377498649)
                    ·
                      refine ⟨1118034805276978783123987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490713073702638377498649 1118034805276978783123987)
                      ·
                        rfl

theorem cell23_2177365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2177365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177365 prefixEnd_2177365 := by exact prefixLift 2177365
  have htrace : WordTrace (prefixWord ++ tailWord_2177365) baseStart_2177365 baseEnd_2177365 := by
    simpa [prefixWord, tailWord_2177365, baseEnd_2177365] using wordTrace_append hprefix tailTrace_2177365
  have hstable : (prefixWord ++ tailWord_2177365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177365).length < 2 ^ (prefixWord ++ tailWord_2177365).sum := by decide
  have hdescent : baseEnd_2177365 < baseStart_2177365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177404 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2177404 : Nat := 118140960795 + 2177404 * 2 ^ 59
def prefixEnd_2177404 : Nat := 4983230072969 + 3 ^ 40 * 2177404 * 2
def baseEnd_2177404 : Nat := 1118054831022504130536307

theorem tailTrace_2177404 : CollatzResearch.WordTrace tailWord_2177404 prefixEnd_2177404 1118054831022504130536307 := by
  unfold tailWord_2177404
  simp only [CollatzResearch.WordTrace]
  refine ⟨39708224101822326921073633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52944298802429769228098177 39708224101822326921073633)
  ·
    refine ⟨29781168076366745190805225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39708224101822326921073633 29781168076366745190805225)
    ·
      refine ⟨22335876057275058893103919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29781168076366745190805225 22335876057275058893103919)
      ·
        refine ⟨33503814085912588339655879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22335876057275058893103919 33503814085912588339655879)
        ·
          refine ⟨50255721128868882509483819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33503814085912588339655879 50255721128868882509483819)
          ·
            refine ⟨75383581693303323764225729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50255721128868882509483819 75383581693303323764225729)
            ·
              refine ⟨56537686269977492823169297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75383581693303323764225729 56537686269977492823169297)
              ·
                refine ⟨42403264702483119617376973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56537686269977492823169297 42403264702483119617376973)
                ·
                  refine ⟨15901224263431169856516365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42403264702483119617376973 15901224263431169856516365)
                  ·
                    refine ⟨5962959098786688696193637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15901224263431169856516365 5962959098786688696193637)
                    ·
                      refine ⟨1118054831022504130536307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5962959098786688696193637 1118054831022504130536307)
                      ·
                        rfl

theorem cell23_2177404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2177404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177404 prefixEnd_2177404 := by exact prefixLift 2177404
  have htrace : WordTrace (prefixWord ++ tailWord_2177404) baseStart_2177404 baseEnd_2177404 := by
    simpa [prefixWord, tailWord_2177404, baseEnd_2177404] using wordTrace_append hprefix tailTrace_2177404
  have hstable : (prefixWord ++ tailWord_2177404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177404).length < 2 ^ (prefixWord ++ tailWord_2177404).sum := by decide
  have hdescent : baseEnd_2177404 < baseStart_2177404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177411 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5]
def baseStart_2177411 : Nat := 118140960795 + 2177411 * 2 ^ 59
def prefixEnd_2177411 : Nat := 4983230072969 + 3 ^ 40 * 2177411 * 2
def baseEnd_2177411 : Nat := 1118058425387085603148775

theorem tailTrace_2177411 : CollatzResearch.WordTrace tailWord_2177411 prefixEnd_2177411 1118058425387085603148775 := by
  unfold tailWord_2177411
  simp only [CollatzResearch.WordTrace]
  refine ⟨79416703514619294037652087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52944469009746196025101391 79416703514619294037652087)
  ·
    refine ⟨119125055271928941056478131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79416703514619294037652087 119125055271928941056478131)
    ·
      refine ⟨178687582907893411584717197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119125055271928941056478131 178687582907893411584717197)
      ·
        refine ⟨67007843590460029344268949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178687582907893411584717197 67007843590460029344268949)
        ·
          refine ⟨3140992668302813875512607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67007843590460029344268949 3140992668302813875512607)
          ·
            refine ⟨4711489002454220813268911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140992668302813875512607 4711489002454220813268911)
            ·
              refine ⟨7067233503681331219903367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711489002454220813268911 7067233503681331219903367)
              ·
                refine ⟨10600850255521996829855051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067233503681331219903367 10600850255521996829855051)
                ·
                  refine ⟨15901275383282995244782577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10600850255521996829855051 15901275383282995244782577)
                  ·
                    refine ⟨11925956537462246433586933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15901275383282995244782577 11925956537462246433586933)
                    ·
                      refine ⟨1118058425387085603148775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11925956537462246433586933 1118058425387085603148775)
                      ·
                        rfl

theorem cell23_2177411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_2177411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177411 prefixEnd_2177411 := by exact prefixLift 2177411
  have htrace : WordTrace (prefixWord ++ tailWord_2177411) baseStart_2177411 baseEnd_2177411 := by
    simpa [prefixWord, tailWord_2177411, baseEnd_2177411] using wordTrace_append hprefix tailTrace_2177411
  have hstable : (prefixWord ++ tailWord_2177411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177411).length < 2 ^ (prefixWord ++ tailWord_2177411).sum := by decide
  have hdescent : baseEnd_2177411 < baseStart_2177411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177431 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 3, 4]
def baseStart_2177431 : Nat := 118140960795 + 2177431 * 2 ^ 59
def prefixEnd_2177431 : Nat := 4983230072969 + 3 ^ 40 * 2177431 * 2
def baseEnd_2177431 : Nat := 372689565000058508299561

theorem tailTrace_2177431 : CollatzResearch.WordTrace tailWord_2177431 prefixEnd_2177431 372689565000058508299561 := by
  unfold tailWord_2177431
  simp only [CollatzResearch.WordTrace]
  refine ⟨79417432974546837453380147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52944955316364558302253431 79417432974546837453380147)
  ·
    refine ⟨119126149461820256180070221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79417432974546837453380147 119126149461820256180070221)
    ·
      refine ⟨44672306048182596067526333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119126149461820256180070221 44672306048182596067526333)
      ·
        refine ⟨16752114768068473525322375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44672306048182596067526333 16752114768068473525322375)
        ·
          refine ⟨25128172152102710287983563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16752114768068473525322375 25128172152102710287983563)
          ·
            refine ⟨37692258228154065431975345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25128172152102710287983563 37692258228154065431975345)
            ·
              refine ⟨28269193671115549073981509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37692258228154065431975345 28269193671115549073981509)
              ·
                refine ⟨5300473813334165451371533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28269193671115549073981509 5300473813334165451371533)
                ·
                  refine ⟨1987677680000312044264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5300473813334165451371533 1987677680000312044264325)
                  ·
                    refine ⟨372689565000058508299561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987677680000312044264325 372689565000058508299561)
                    ·
                      rfl

theorem cell23_2177431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_2177431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177431 prefixEnd_2177431 := by exact prefixLift 2177431
  have htrace : WordTrace (prefixWord ++ tailWord_2177431) baseStart_2177431 baseEnd_2177431 := by
    simpa [prefixWord, tailWord_2177431, baseEnd_2177431] using wordTrace_append hprefix tailTrace_2177431
  have hstable : (prefixWord ++ tailWord_2177431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177431).length < 2 ^ (prefixWord ++ tailWord_2177431).sum := by decide
  have hdescent : baseEnd_2177431 < baseStart_2177431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177444 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 10]
def baseStart_2177444 : Nat := 118140960795 + 2177444 * 2 ^ 59
def prefixEnd_2177444 : Nat := 4983230072969 + 3 ^ 40 * 2177444 * 2
def baseEnd_2177444 : Nat := 124230596694298219337347

theorem tailTrace_2177444 : CollatzResearch.WordTrace tailWord_2177444 prefixEnd_2177444 124230596694298219337347 := by
  unfold tailWord_2177444
  simp only [CollatzResearch.WordTrace]
  refine ⟨39708953561749870336801693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52945271415666493782402257 39708953561749870336801693)
  ·
    refine ⟨14890857585656201376300635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39708953561749870336801693 14890857585656201376300635)
    ·
      refine ⟨22336286378484302064450953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14890857585656201376300635 22336286378484302064450953)
      ·
        refine ⟨16752214783863226548338215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22336286378484302064450953 16752214783863226548338215)
        ·
          refine ⟨25128322175794839822507323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16752214783863226548338215 25128322175794839822507323)
          ·
            refine ⟨37692483263692259733760985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25128322175794839822507323 37692483263692259733760985)
            ·
              refine ⟨28269362447769194800320739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37692483263692259733760985 28269362447769194800320739)
              ·
                refine ⟨42404043671653792200481109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28269362447769194800320739 42404043671653792200481109)
                ·
                  refine ⟨124230596694298219337347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42404043671653792200481109 124230596694298219337347)
                  ·
                    rfl

theorem cell23_2177444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_2177444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177444 prefixEnd_2177444 := by exact prefixLift 2177444
  have htrace : WordTrace (prefixWord ++ tailWord_2177444) baseStart_2177444 baseEnd_2177444 := by
    simpa [prefixWord, tailWord_2177444, baseEnd_2177444] using wordTrace_append hprefix tailTrace_2177444
  have hstable : (prefixWord ++ tailWord_2177444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177444).length < 2 ^ (prefixWord ++ tailWord_2177444).sum := by decide
  have hdescent : baseEnd_2177444 < baseStart_2177444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177464 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2177464 : Nat := 118140960795 + 2177464 * 2 ^ 59
def prefixEnd_2177464 : Nat := 4983230072969 + 3 ^ 40 * 2177464 * 2
def baseEnd_2177464 : Nat := 1118085639861773895786031

theorem tailTrace_2177464 : CollatzResearch.WordTrace tailWord_2177464 prefixEnd_2177464 1118085639861773895786031 := by
  unfold tailWord_2177464
  simp only [CollatzResearch.WordTrace]
  refine ⟨39709318291713642044665723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52945757722284856059554297 39709318291713642044665723)
  ·
    refine ⟨59563977437570463066998585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39709318291713642044665723 59563977437570463066998585)
    ·
      refine ⟨44672983078177847300248939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59563977437570463066998585 44672983078177847300248939)
      ·
        refine ⟨67009474617266770950373409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44672983078177847300248939 67009474617266770950373409)
        ·
          refine ⟨50257105962950078212780057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67009474617266770950373409 50257105962950078212780057)
          ·
            refine ⟨37692829472212558659585043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50257105962950078212780057 37692829472212558659585043)
            ·
              refine ⟨56539244208318837989377565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37692829472212558659585043 56539244208318837989377565)
              ·
                refine ⟨21202216578119564246016587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56539244208318837989377565 21202216578119564246016587)
                ·
                  refine ⟨31803324867179346369024881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21202216578119564246016587 31803324867179346369024881)
                  ·
                    refine ⟨23852493650384509776768661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31803324867179346369024881 23852493650384509776768661)
                    ·
                      refine ⟨1118085639861773895786031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23852493650384509776768661 1118085639861773895786031)
                      ·
                        rfl

theorem cell23_2177464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2177464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177464 prefixEnd_2177464 := by exact prefixLift 2177464
  have htrace : WordTrace (prefixWord ++ tailWord_2177464) baseStart_2177464 baseEnd_2177464 := by
    simpa [prefixWord, tailWord_2177464, baseEnd_2177464] using wordTrace_append hprefix tailTrace_2177464
  have hstable : (prefixWord ++ tailWord_2177464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177464).length < 2 ^ (prefixWord ++ tailWord_2177464).sum := by decide
  have hdescent : baseEnd_2177464 < baseStart_2177464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177465 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 1, 4]
def baseStart_2177465 : Nat := 118140960795 + 2177465 * 2 ^ 59
def prefixEnd_2177465 : Nat := 4983230072969 + 3 ^ 40 * 2177465 * 2
def baseEnd_2177465 : Nat := 372695384447476130624509

theorem tailTrace_2177465 : CollatzResearch.WordTrace tailWord_2177465 prefixEnd_2177465 372695384447476130624509 := by
  unfold tailWord_2177465
  simp only [CollatzResearch.WordTrace]
  refine ⟨79418673056423661260117849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52945782037615774173411899 79418673056423661260117849)
  ·
    refine ⟨59564004792317745945088387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79418673056423661260117849 59564004792317745945088387)
    ·
      refine ⟨89346007188476618917632581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59564004792317745945088387 89346007188476618917632581)
      ·
        refine ⟨16752376347839366047056109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89346007188476618917632581 16752376347839366047056109)
        ·
          refine ⟨6282141130439762267646041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16752376347839366047056109 6282141130439762267646041)
          ·
            refine ⟨4711605847829821700734531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6282141130439762267646041 4711605847829821700734531)
            ·
              refine ⟨7067408771744732551101797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711605847829821700734531 7067408771744732551101797)
              ·
                refine ⟨1325139144702137353331587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7067408771744732551101797 1325139144702137353331587)
                ·
                  refine ⟨1987708717053206029997381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325139144702137353331587 1987708717053206029997381)
                  ·
                    refine ⟨372695384447476130624509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987708717053206029997381 372695384447476130624509)
                    ·
                      rfl

theorem cell23_2177465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 4].length) (baseStart_2177465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177465 prefixEnd_2177465 := by exact prefixLift 2177465
  have htrace : WordTrace (prefixWord ++ tailWord_2177465) baseStart_2177465 baseEnd_2177465 := by
    simpa [prefixWord, tailWord_2177465, baseEnd_2177465] using wordTrace_append hprefix tailTrace_2177465
  have hstable : (prefixWord ++ tailWord_2177465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177465).length < 2 ^ (prefixWord ++ tailWord_2177465).sum := by decide
  have hdescent : baseEnd_2177465 < baseStart_2177465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177498 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_2177498 : Nat := 118140960795 + 2177498 * 2 ^ 59
def prefixEnd_2177498 : Nat := 4983230072969 + 3 ^ 40 * 2177498 * 2
def baseEnd_2177498 : Nat := 1118103098204026762760875

theorem tailTrace_2177498 : CollatzResearch.WordTrace tailWord_2177498 prefixEnd_2177498 1118103098204026762760875 := by
  unfold tailWord_2177498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19854969166326026974017287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52946584443536071930712765 19854969166326026974017287)
  ·
    refine ⟨29782453749489040461025931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19854969166326026974017287 29782453749489040461025931)
    ·
      refine ⟨44673680624233560691538897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29782453749489040461025931 44673680624233560691538897)
      ·
        refine ⟨33505260468175170518654173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44673680624233560691538897 33505260468175170518654173)
        ·
          refine ⟨12564472675565688944495315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33505260468175170518654173 12564472675565688944495315)
          ·
            refine ⟨18846709013348533416742973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12564472675565688944495315 18846709013348533416742973)
            ·
              refine ⟨7067515880005700031278615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18846709013348533416742973 7067515880005700031278615)
              ·
                refine ⟨10601273820008550046917923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067515880005700031278615 10601273820008550046917923)
                ·
                  refine ⟨15901910730012825070376885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10601273820008550046917923 15901910730012825070376885)
                  ·
                    refine ⟨1490804130938702350347833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15901910730012825070376885 1490804130938702350347833)
                    ·
                      refine ⟨1118103098204026762760875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490804130938702350347833 1118103098204026762760875)
                      ·
                        rfl

theorem cell23_2177498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_2177498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177498 prefixEnd_2177498 := by exact prefixLift 2177498
  have htrace : WordTrace (prefixWord ++ tailWord_2177498) baseStart_2177498 baseEnd_2177498 := by
    simpa [prefixWord, tailWord_2177498, baseEnd_2177498] using wordTrace_append hprefix tailTrace_2177498
  have hstable : (prefixWord ++ tailWord_2177498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177498).length < 2 ^ (prefixWord ++ tailWord_2177498).sum := by decide
  have hdescent : baseEnd_2177498 < baseStart_2177498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177522 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2177522 : Nat := 118140960795 + 2177522 * 2 ^ 59
def prefixEnd_2177522 : Nat := 4983230072969 + 3 ^ 40 * 2177522 * 2
def baseEnd_2177522 : Nat := 1118115421739734668860765

theorem tailTrace_2177522 : CollatzResearch.WordTrace tailWord_2177522 prefixEnd_2177522 1118115421739734668860765 := by
  unfold tailWord_2177522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19855188004304289998735705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52947168011478106663295213 19855188004304289998735705)
  ·
    refine ⟨14891391003228217499051779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19855188004304289998735705 14891391003228217499051779)
    ·
      refine ⟨22337086504842326248577669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14891391003228217499051779 22337086504842326248577669)
      ·
        refine ⟨4188203719657936171608313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22337086504842326248577669 4188203719657936171608313)
        ·
          refine ⟨3141152789743452128706235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188203719657936171608313 3141152789743452128706235)
          ·
            refine ⟨4711729184615178193059353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141152789743452128706235 4711729184615178193059353)
            ·
              refine ⟨3533796888461383644794515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4711729184615178193059353 3533796888461383644794515)
              ·
                refine ⟨5300695332692075467191773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533796888461383644794515 5300695332692075467191773)
                ·
                  refine ⟨1987760749759528300196915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5300695332692075467191773 1987760749759528300196915)
                  ·
                    refine ⟨2981641124639292450295373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1987760749759528300196915 2981641124639292450295373)
                    ·
                      refine ⟨1118115421739734668860765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981641124639292450295373 1118115421739734668860765)
                      ·
                        rfl

theorem cell23_2177522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2177522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177522 prefixEnd_2177522 := by exact prefixLift 2177522
  have htrace : WordTrace (prefixWord ++ tailWord_2177522) baseStart_2177522 baseEnd_2177522 := by
    simpa [prefixWord, tailWord_2177522, baseEnd_2177522] using wordTrace_append hprefix tailTrace_2177522
  have hstable : (prefixWord ++ tailWord_2177522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177522).length < 2 ^ (prefixWord ++ tailWord_2177522).sum := by decide
  have hdescent : baseEnd_2177522 < baseStart_2177522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177556 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2177556 : Nat := 118140960795 + 2177556 * 2 ^ 59
def prefixEnd_2177556 : Nat := 4983230072969 + 3 ^ 40 * 2177556 * 2
def baseEnd_2177556 : Nat := 1118132880081987535835609

theorem tailTrace_2177556 : CollatzResearch.WordTrace tailWord_2177556 prefixEnd_2177556 1118132880081987535835609 := by
  unfold tailWord_2177556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39710996049546991900840261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52947994732729322534453681 39710996049546991900840261)
  ·
    refine ⟨7445811759290060981407549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39710996049546991900840261 7445811759290060981407549)
    ·
      refine ⟨2792179409733772868027831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7445811759290060981407549 2792179409733772868027831)
      ·
        refine ⟨4188269114600659302041747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792179409733772868027831 4188269114600659302041747)
        ·
          refine ⟨6282403671900988953062621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188269114600659302041747 6282403671900988953062621)
          ·
            refine ⟨2355901376962870857398483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6282403671900988953062621 2355901376962870857398483)
            ·
              refine ⟨3533852065444306286097725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355901376962870857398483 3533852065444306286097725)
              ·
                refine ⟨1325194524541614857286647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3533852065444306286097725 1325194524541614857286647)
                ·
                  refine ⟨1987791786812422285929971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325194524541614857286647 1987791786812422285929971)
                  ·
                    refine ⟨2981687680218633428894957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1987791786812422285929971 2981687680218633428894957)
                    ·
                      refine ⟨1118132880081987535835609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981687680218633428894957 1118132880081987535835609)
                      ·
                        rfl

theorem cell23_2177556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2177556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177556 prefixEnd_2177556 := by exact prefixLift 2177556
  have htrace : WordTrace (prefixWord ++ tailWord_2177556) baseStart_2177556 baseEnd_2177556 := by
    simpa [prefixWord, tailWord_2177556, baseEnd_2177556] using wordTrace_append hprefix tailTrace_2177556
  have hstable : (prefixWord ++ tailWord_2177556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177556).length < 2 ^ (prefixWord ++ tailWord_2177556).sum := by decide
  have hdescent : baseEnd_2177556 < baseStart_2177556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177565 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2177565 : Nat := 118140960795 + 2177565 * 2 ^ 59
def prefixEnd_2177565 : Nat := 4983230072969 + 3 ^ 40 * 2177565 * 2
def baseEnd_2177565 : Nat := 1118137501407878000623067

theorem tailTrace_2177565 : CollatzResearch.WordTrace tailWord_2177565 prefixEnd_2177565 1118137501407878000623067 := by
  unfold tailWord_2177565
  simp only [CollatzResearch.WordTrace]
  refine ⟨79422320356061378338758149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52948213570707585559172099 79422320356061378338758149)
  ·
    refine ⟨14891685066761508438517153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79422320356061378338758149 14891685066761508438517153)
    ·
      refine ⟨11168763800071131328887865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14891685066761508438517153 11168763800071131328887865)
      ·
        refine ⟨8376572850053348496665899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11168763800071131328887865 8376572850053348496665899)
        ·
          refine ⟨12564859275080022744998849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376572850053348496665899 12564859275080022744998849)
          ·
            refine ⟨9423644456310017058749137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12564859275080022744998849 9423644456310017058749137)
            ·
              refine ⟨7067733342232512794061853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9423644456310017058749137 7067733342232512794061853)
              ·
                refine ⟨2650400003337192297773195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7067733342232512794061853 2650400003337192297773195)
                ·
                  refine ⟨3975600005005788446659793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650400003337192297773195 3975600005005788446659793)
                  ·
                    refine ⟨2981700003754341334994845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3975600005005788446659793 2981700003754341334994845)
                    ·
                      refine ⟨1118137501407878000623067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981700003754341334994845 1118137501407878000623067)
                      ·
                        rfl

theorem cell23_2177565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2177565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177565 prefixEnd_2177565 := by exact prefixLift 2177565
  have htrace : WordTrace (prefixWord ++ tailWord_2177565) baseStart_2177565 baseEnd_2177565 := by
    simpa [prefixWord, tailWord_2177565, baseEnd_2177565] using wordTrace_append hprefix tailTrace_2177565
  have hstable : (prefixWord ++ tailWord_2177565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177565).length < 2 ^ (prefixWord ++ tailWord_2177565).sum := by decide
  have hdescent : baseEnd_2177565 < baseStart_2177565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177568 : List Nat := [2, 1, 1, 6, 2, 2, 9]
def baseStart_2177568 : Nat := 118140960795 + 2177568 * 2 ^ 59
def prefixEnd_2177568 : Nat := 4983230072969 + 3 ^ 40 * 2177568 * 2
def baseEnd_2177568 : Nat := 13804185701849894924513

theorem tailTrace_2177568 : CollatzResearch.WordTrace tailWord_2177568 prefixEnd_2177568 13804185701849894924513 := by
  unfold tailWord_2177568
  simp only [CollatzResearch.WordTrace]
  refine ⟨39711214887525254925558679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52948286516700339900744905 39711214887525254925558679)
  ·
    refine ⟨59566822331287882388338019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39711214887525254925558679 59566822331287882388338019)
    ·
      refine ⟨89350233496931823582507029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59566822331287882388338019 89350233496931823582507029)
      ·
        refine ⟨4188292195168679230430017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89350233496931823582507029 4188292195168679230430017)
        ·
          refine ⟨3141219146376509422822513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188292195168679230430017 3141219146376509422822513)
          ·
            refine ⟨2355914359782382067116885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3141219146376509422822513 2355914359782382067116885)
            ·
              refine ⟨13804185701849894924513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2355914359782382067116885 13804185701849894924513)
              ·
                rfl

theorem cell23_2177568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 9].length) (baseStart_2177568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177568 prefixEnd_2177568 := by exact prefixLift 2177568
  have htrace : WordTrace (prefixWord ++ tailWord_2177568) baseStart_2177568 baseEnd_2177568 := by
    simpa [prefixWord, tailWord_2177568, baseEnd_2177568] using wordTrace_append hprefix tailTrace_2177568
  have hstable : (prefixWord ++ tailWord_2177568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177568).length < 2 ^ (prefixWord ++ tailWord_2177568).sum := by decide
  have hdescent : baseEnd_2177568 < baseStart_2177568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177605 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_2177605 : Nat := 118140960795 + 2177605 * 2 ^ 59
def prefixEnd_2177605 : Nat := 4983230072969 + 3 ^ 40 * 2177605 * 2
def baseEnd_2177605 : Nat := 1118158040634057844122883

theorem tailTrace_2177605 : CollatzResearch.WordTrace tailWord_2177605 prefixEnd_2177605 1118158040634057844122883 := by
  unfold tailWord_2177605
  simp only [CollatzResearch.WordTrace]
  refine ⟨79423779275916465170214269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52949186183944310113476179 79423779275916465170214269)
  ·
    refine ⟨29783917228468674438830351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79423779275916465170214269 29783917228468674438830351)
    ·
      refine ⟨44675875842703011658245527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29783917228468674438830351 44675875842703011658245527)
      ·
        refine ⟨67013813764054517487368291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44675875842703011658245527 67013813764054517487368291)
        ·
          refine ⟨100520720646081776231052437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67013813764054517487368291 100520720646081776231052437)
          ·
            refine ⟨4711908780285083260830583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100520720646081776231052437 4711908780285083260830583)
            ·
              refine ⟨7067863170427624891245875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711908780285083260830583 7067863170427624891245875)
              ·
                refine ⟨10601794755641437336868813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067863170427624891245875 10601794755641437336868813)
                ·
                  refine ⟨3975673033365539001325805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10601794755641437336868813 3975673033365539001325805)
                  ·
                    refine ⟨1490877387512077125497177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3975673033365539001325805 1490877387512077125497177)
                    ·
                      refine ⟨1118158040634057844122883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490877387512077125497177 1118158040634057844122883)
                      ·
                        rfl

theorem cell23_2177605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_2177605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177605 prefixEnd_2177605 := by exact prefixLift 2177605
  have htrace : WordTrace (prefixWord ++ tailWord_2177605) baseStart_2177605 baseEnd_2177605 := by
    simpa [prefixWord, tailWord_2177605, baseEnd_2177605] using wordTrace_append hprefix tailTrace_2177605
  have hstable : (prefixWord ++ tailWord_2177605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177605).length < 2 ^ (prefixWord ++ tailWord_2177605).sum := by decide
  have hdescent : baseEnd_2177605 < baseStart_2177605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177630 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2177630 : Nat := 118140960795 + 2177630 * 2 ^ 59
def prefixEnd_2177630 : Nat := 4983230072969 + 3 ^ 40 * 2177630 * 2
def baseEnd_2177630 : Nat := 1118170877650420246310269

theorem tailTrace_2177630 : CollatzResearch.WordTrace tailWord_2177630 prefixEnd_2177630 1118170877650420246310269 := by
  unfold tailWord_2177630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928086387603236804984293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52949794067217262959916229 9928086387603236804984293)
  ·
    refine ⟨1861516197675606900934555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9928086387603236804984293 1861516197675606900934555)
    ·
      refine ⟨2792274296513410351401833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1861516197675606900934555 2792274296513410351401833)
      ·
        refine ⟨2094205722385057763551375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2792274296513410351401833 2094205722385057763551375)
        ·
          refine ⟨3141308583577586645327063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094205722385057763551375 3141308583577586645327063)
          ·
            refine ⟨4711962875366379967990595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141308583577586645327063 4711962875366379967990595)
            ·
              refine ⟨7067944313049569951985893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711962875366379967990595 7067944313049569951985893)
              ·
                refine ⟨1325239558696794365997355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7067944313049569951985893 1325239558696794365997355)
                ·
                  refine ⟨1987859338045191548996033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325239558696794365997355 1987859338045191548996033)
                  ·
                    refine ⟨1490894503533893661747025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987859338045191548996033 1490894503533893661747025)
                    ·
                      refine ⟨1118170877650420246310269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490894503533893661747025 1118170877650420246310269)
                      ·
                        rfl

theorem cell23_2177630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2177630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177630 prefixEnd_2177630 := by exact prefixLift 2177630
  have htrace : WordTrace (prefixWord ++ tailWord_2177630) baseStart_2177630 baseEnd_2177630 := by
    simpa [prefixWord, tailWord_2177630, baseEnd_2177630] using wordTrace_append hprefix tailTrace_2177630
  have hstable : (prefixWord ++ tailWord_2177630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177630).length < 2 ^ (prefixWord ++ tailWord_2177630).sum := by decide
  have hdescent : baseEnd_2177630 < baseStart_2177630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177631 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2177631 : Nat := 118140960795 + 2177631 * 2 ^ 59
def prefixEnd_2177631 : Nat := 4983230072969 + 3 ^ 40 * 2177631 * 2
def baseEnd_2177631 : Nat := 1118171391131074742397763

theorem tailTrace_2177631 : CollatzResearch.WordTrace tailWord_2177631 prefixEnd_2177631 1118171391131074742397763 := by
  unfold tailWord_2177631
  simp only [CollatzResearch.WordTrace]
  refine ⟨79424727573822271610660747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52949818382548181073773831 79424727573822271610660747)
  ·
    refine ⟨119137091360733407415991121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79424727573822271610660747 119137091360733407415991121)
    ·
      refine ⟨89352818520550055561993341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119137091360733407415991121 89352818520550055561993341)
      ·
        refine ⟨33507306945206270835747503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89352818520550055561993341 33507306945206270835747503)
        ·
          refine ⟨50260960417809406253621255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33507306945206270835747503 50260960417809406253621255)
          ·
            refine ⟨75391440626714109380431883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50260960417809406253621255 75391440626714109380431883)
            ·
              refine ⟨113087160940071164070647825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75391440626714109380431883 113087160940071164070647825)
              ·
                refine ⟨84815370705053373052985869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113087160940071164070647825 84815370705053373052985869)
                ·
                  refine ⟨31805764014395014894869701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84815370705053373052985869 31805764014395014894869701)
                  ·
                    refine ⟨5963580752699065292788069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31805764014395014894869701 5963580752699065292788069)
                    ·
                      refine ⟨1118171391131074742397763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5963580752699065292788069 1118171391131074742397763)
                      ·
                        rfl

theorem cell23_2177631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2177631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177631 prefixEnd_2177631 := by exact prefixLift 2177631
  have htrace : WordTrace (prefixWord ++ tailWord_2177631) baseStart_2177631 baseEnd_2177631 := by
    simpa [prefixWord, tailWord_2177631, baseEnd_2177631] using wordTrace_append hprefix tailTrace_2177631
  have hstable : (prefixWord ++ tailWord_2177631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177631).length < 2 ^ (prefixWord ++ tailWord_2177631).sum := by decide
  have hdescent : baseEnd_2177631 < baseStart_2177631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177641 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 7]
def baseStart_2177641 : Nat := 118140960795 + 2177641 * 2 ^ 59
def prefixEnd_2177641 : Nat := 4983230072969 + 3 ^ 40 * 2177641 * 2
def baseEnd_2177641 : Nat := 124241836215291078141413

theorem tailTrace_2177641 : CollatzResearch.WordTrace tailWord_2177641 prefixEnd_2177641 124241836215291078141413 := by
  unfold tailWord_2177641
  simp only [CollatzResearch.WordTrace]
  refine ⟨79425092303786043318524777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52950061535857362212349851 79425092303786043318524777)
  ·
    refine ⟨59568819227839532488893583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79425092303786043318524777 59568819227839532488893583)
    ·
      refine ⟨89353228841759298733340375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59568819227839532488893583 89353228841759298733340375)
      ·
        refine ⟨134029843262638948100010563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89353228841759298733340375 134029843262638948100010563)
        ·
          refine ⟨201044764893958422150015845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134029843262638948100010563 201044764893958422150015845)
          ·
            refine ⟨37695893417617204153127971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201044764893958422150015845 37695893417617204153127971)
            ·
              refine ⟨56543840126425806229691957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37695893417617204153127971 56543840126425806229691957)
              ·
                refine ⟨5300985011852419334033621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56543840126425806229691957 5300985011852419334033621)
                ·
                  refine ⟨124241836215291078141413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5300985011852419334033621 124241836215291078141413)
                  ·
                    rfl

theorem cell23_2177641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_2177641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177641 prefixEnd_2177641 := by exact prefixLift 2177641
  have htrace : WordTrace (prefixWord ++ tailWord_2177641) baseStart_2177641 baseEnd_2177641 := by
    simpa [prefixWord, tailWord_2177641, baseEnd_2177641] using wordTrace_append hprefix tailTrace_2177641
  have hstable : (prefixWord ++ tailWord_2177641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177641).length < 2 ^ (prefixWord ++ tailWord_2177641).sum := by decide
  have hdescent : baseEnd_2177641 < baseStart_2177641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177688 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_2177688 : Nat := 118140960795 + 2177688 * 2 ^ 59
def prefixEnd_2177688 : Nat := 4983230072969 + 3 ^ 40 * 2177688 * 2
def baseEnd_2177688 : Nat := 372733553176127006461667

theorem tailTrace_2177688 : CollatzResearch.WordTrace tailWord_2177688 prefixEnd_2177688 372733553176127006461667 := by
  unfold tailWord_2177688
  simp only [CollatzResearch.WordTrace]
  refine ⟨39713403267307885172742859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52951204356410513563657145 39713403267307885172742859)
  ·
    refine ⟨59570104900961827759114289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39713403267307885172742859 59570104900961827759114289)
    ·
      refine ⟨44677578675721370819335717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59570104900961827759114289 44677578675721370819335717)
      ·
        refine ⟨8377046001697757028625447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44677578675721370819335717 8377046001697757028625447)
        ·
          refine ⟨12565569002546635542938171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8377046001697757028625447 12565569002546635542938171)
          ·
            refine ⟨18848353503819953314407257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12565569002546635542938171 18848353503819953314407257)
            ·
              refine ⟨14136265127864964985805443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18848353503819953314407257 14136265127864964985805443)
              ·
                refine ⟨21204397691797447478708165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14136265127864964985805443 21204397691797447478708165)
                ·
                  refine ⟨3975824567212021402257781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21204397691797447478708165 3975824567212021402257781)
                  ·
                    refine ⟨372733553176127006461667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3975824567212021402257781 372733553176127006461667)
                    ·
                      rfl

theorem cell23_2177688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_2177688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177688 prefixEnd_2177688 := by exact prefixLift 2177688
  have htrace : WordTrace (prefixWord ++ tailWord_2177688) baseStart_2177688 baseEnd_2177688 := by
    simpa [prefixWord, tailWord_2177688, baseEnd_2177688] using wordTrace_append hprefix tailTrace_2177688
  have hstable : (prefixWord ++ tailWord_2177688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177688).length < 2 ^ (prefixWord ++ tailWord_2177688).sum := by decide
  have hdescent : baseEnd_2177688 < baseStart_2177688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177703 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2177703 : Nat := 118140960795 + 2177703 * 2 ^ 59
def prefixEnd_2177703 : Nat := 4983230072969 + 3 ^ 40 * 2177703 * 2
def baseEnd_2177703 : Nat := 1118208361738198460697433

theorem tailTrace_2177703 : CollatzResearch.WordTrace tailWord_2177703 prefixEnd_2177703 1118208361738198460697433 := by
  unfold tailWord_2177703
  simp only [CollatzResearch.WordTrace]
  refine ⟨79427353629561427907281763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52951569086374285271521175 79427353629561427907281763)
  ·
    refine ⟨119141030444342141860922645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79427353629561427907281763 119141030444342141860922645)
    ·
      refine ⟨5584735802078537899730749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119141030444342141860922645 5584735802078537899730749)
      ·
        refine ⟨2094275925779451712399031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5584735802078537899730749 2094275925779451712399031)
        ·
          refine ⟨3141413888669177568598547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094275925779451712399031 3141413888669177568598547)
          ·
            refine ⟨4712120833003766352897821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141413888669177568598547 4712120833003766352897821)
            ·
              refine ⟨1767045312376412382336683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712120833003766352897821 1767045312376412382336683)
              ·
                refine ⟨2650567968564618573505025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767045312376412382336683 2650567968564618573505025)
                ·
                  refine ⟨1987925976423463930128769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650567968564618573505025 1987925976423463930128769)
                  ·
                    refine ⟨1490944482317597947596577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987925976423463930128769 1490944482317597947596577)
                    ·
                      refine ⟨1118208361738198460697433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1490944482317597947596577 1118208361738198460697433)
                      ·
                        rfl

theorem cell23_2177703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2177703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177703 prefixEnd_2177703 := by exact prefixLift 2177703
  have htrace : WordTrace (prefixWord ++ tailWord_2177703) baseStart_2177703 baseEnd_2177703 := by
    simpa [prefixWord, tailWord_2177703, baseEnd_2177703] using wordTrace_append hprefix tailTrace_2177703
  have hstable : (prefixWord ++ tailWord_2177703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177703).length < 2 ^ (prefixWord ++ tailWord_2177703).sum := by decide
  have hdescent : baseEnd_2177703 < baseStart_2177703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177745 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_2177745 : Nat := 118140960795 + 2177745 * 2 ^ 59
def prefixEnd_2177745 : Nat := 4983230072969 + 3 ^ 40 * 2177745 * 2
def baseEnd_2177745 : Nat := 1118229927925687296372239

theorem tailTrace_2177745 : CollatzResearch.WordTrace tailWord_2177745 prefixEnd_2177745 1118229927925687296372239 := by
  unfold tailWord_2177745
  simp only [CollatzResearch.WordTrace]
  refine ⟨79428885495409269080310689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52952590330272846053540459 79428885495409269080310689)
  ·
    refine ⟨59571664121556951810233017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79428885495409269080310689 59571664121556951810233017)
    ·
      refine ⟨44678748091167713857674763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59571664121556951810233017 44678748091167713857674763)
      ·
        refine ⟨67018122136751570786512145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44678748091167713857674763 67018122136751570786512145)
        ·
          refine ⟨50263591602563678089884109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67018122136751570786512145 50263591602563678089884109)
          ·
            refine ⟨18848846850961379283706541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50263591602563678089884109 18848846850961379283706541)
            ·
              refine ⟨7068317569110517231389953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18848846850961379283706541 7068317569110517231389953)
              ·
                refine ⟨5301238176832887923542465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7068317569110517231389953 5301238176832887923542465)
                ·
                  refine ⟨3975928632624665942656849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5301238176832887923542465 3975928632624665942656849)
                  ·
                    refine ⟨2981946474468499456992637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3975928632624665942656849 2981946474468499456992637)
                    ·
                      refine ⟨1118229927925687296372239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2981946474468499456992637 1118229927925687296372239)
                      ·
                        rfl

theorem cell23_2177745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_2177745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177745 prefixEnd_2177745 := by exact prefixLift 2177745
  have htrace : WordTrace (prefixWord ++ tailWord_2177745) baseStart_2177745 baseEnd_2177745 := by
    simpa [prefixWord, tailWord_2177745, baseEnd_2177745] using wordTrace_append hprefix tailTrace_2177745
  have hstable : (prefixWord ++ tailWord_2177745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177745).length < 2 ^ (prefixWord ++ tailWord_2177745).sum := by decide
  have hdescent : baseEnd_2177745 < baseStart_2177745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177752 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_2177752 : Nat := 118140960795 + 2177752 * 2 ^ 59
def prefixEnd_2177752 : Nat := 4983230072969 + 3 ^ 40 * 2177752 * 2
def baseEnd_2177752 : Nat := 372744507430089589661569

theorem tailTrace_2177752 : CollatzResearch.WordTrace tailWord_2177752 prefixEnd_2177752 372744507430089589661569 := by
  unfold tailWord_2177752
  simp only [CollatzResearch.WordTrace]
  refine ⟨39714570403191954637907755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52952760537589272850543673 39714570403191954637907755)
  ·
    refine ⟨59571855604787931956861633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39714570403191954637907755 59571855604787931956861633)
    ·
      refine ⟨44678891703590948967646225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59571855604787931956861633 44678891703590948967646225)
      ·
        refine ⟨33509168777693211725734669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44678891703590948967646225 33509168777693211725734669)
        ·
          refine ⟨12565938291634954397150501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33509168777693211725734669 12565938291634954397150501)
          ·
            refine ⟨2356113429681553949465719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12565938291634954397150501 2356113429681553949465719)
            ·
              refine ⟨3534170144522330924198579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356113429681553949465719 3534170144522330924198579)
              ·
                refine ⟨5301255216783496386297869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534170144522330924198579 5301255216783496386297869)
                ·
                  refine ⟨1987970706293811144861701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5301255216783496386297869 1987970706293811144861701)
                  ·
                    refine ⟨372744507430089589661569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1987970706293811144861701 372744507430089589661569)
                    ·
                      rfl

theorem cell23_2177752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_2177752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177752 prefixEnd_2177752 := by exact prefixLift 2177752
  have htrace : WordTrace (prefixWord ++ tailWord_2177752) baseStart_2177752 baseEnd_2177752 := by
    simpa [prefixWord, tailWord_2177752, baseEnd_2177752] using wordTrace_append hprefix tailTrace_2177752
  have hstable : (prefixWord ++ tailWord_2177752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177752).length < 2 ^ (prefixWord ++ tailWord_2177752).sum := by decide
  have hdescent : baseEnd_2177752 < baseStart_2177752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177765 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 6]
def baseStart_2177765 : Nat := 118140960795 + 2177765 * 2 ^ 59
def prefixEnd_2177765 : Nat := 4983230072969 + 3 ^ 40 * 2177765 * 2
def baseEnd_2177765 : Nat := 124248910837641913124683

theorem tailTrace_2177765 : CollatzResearch.WordTrace tailWord_2177765 prefixEnd_2177765 124248910837641913124683 := by
  unfold tailWord_2177765
  simp only [CollatzResearch.WordTrace]
  refine ⟨79429614955336812496038749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52953076636891208330692499 79429614955336812496038749)
  ·
    refine ⟨29786105608251304686014531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79429614955336812496038749 29786105608251304686014531)
    ·
      refine ⟨44679158412376957029021797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29786105608251304686014531 44679158412376957029021797)
      ·
        refine ⟨8377342202320679442941587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44679158412376957029021797 8377342202320679442941587)
        ·
          refine ⟨12566013303481019164412381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8377342202320679442941587 12566013303481019164412381)
          ·
            refine ⟨4712254988805382186654643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12566013303481019164412381 4712254988805382186654643)
            ·
              refine ⟨7068382483208073279981965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712254988805382186654643 7068382483208073279981965)
              ·
                refine ⟨2650643431203027479993237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7068382483208073279981965 2650643431203027479993237)
                ·
                  refine ⟨124248910837641913124683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2650643431203027479993237 124248910837641913124683)
                  ·
                    rfl

theorem cell23_2177765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_2177765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177765 prefixEnd_2177765 := by exact prefixLift 2177765
  have htrace : WordTrace (prefixWord ++ tailWord_2177765) baseStart_2177765 baseEnd_2177765 := by
    simpa [prefixWord, tailWord_2177765, baseEnd_2177765] using wordTrace_append hprefix tailTrace_2177765
  have hstable : (prefixWord ++ tailWord_2177765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177765).length < 2 ^ (prefixWord ++ tailWord_2177765).sum := by decide
  have hdescent : baseEnd_2177765 < baseStart_2177765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177785 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 5, 2]
def baseStart_2177785 : Nat := 118140960795 + 2177785 * 2 ^ 59
def prefixEnd_2177785 : Nat := 4983230072969 + 3 ^ 40 * 2177785 * 2
def baseEnd_2177785 : Nat := 1118250467151867139872055

theorem tailTrace_2177785 : CollatzResearch.WordTrace tailWord_2177785 prefixEnd_2177785 1118250467151867139872055 := by
  unfold tailWord_2177785
  simp only [CollatzResearch.WordTrace]
  refine ⟨79430344415264355911766809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52953562943509570607844539 79430344415264355911766809)
  ·
    refine ⟨59572758311448266933825107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79430344415264355911766809 59572758311448266933825107)
    ·
      refine ⟨89359137467172400400737661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59572758311448266933825107 89359137467172400400737661)
      ·
        refine ⟨33509676550189650150276623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89359137467172400400737661 33509676550189650150276623)
        ·
          refine ⟨50264514825284475225414935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33509676550189650150276623 50264514825284475225414935)
          ·
            refine ⟨75396772237926712838122403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50264514825284475225414935 75396772237926712838122403)
            ·
              refine ⟨113095158356890069257183605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75396772237926712838122403 113095158356890069257183605)
              ·
                refine ⟨10602671095958443992860963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113095158356890069257183605 10602671095958443992860963)
                ·
                  refine ⟨15904006643937665989291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10602671095958443992860963 15904006643937665989291445)
                  ·
                    refine ⟨1491000622869156186496073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15904006643937665989291445 1491000622869156186496073)
                    ·
                      refine ⟨1118250467151867139872055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491000622869156186496073 1118250467151867139872055)
                      ·
                        rfl

theorem cell23_2177785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_2177785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177785 prefixEnd_2177785 := by exact prefixLift 2177785
  have htrace : WordTrace (prefixWord ++ tailWord_2177785) baseStart_2177785 baseEnd_2177785 := by
    simpa [prefixWord, tailWord_2177785, baseEnd_2177785] using wordTrace_append hprefix tailTrace_2177785
  have hstable : (prefixWord ++ tailWord_2177785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177785).length < 2 ^ (prefixWord ++ tailWord_2177785).sum := by decide
  have hdescent : baseEnd_2177785 < baseStart_2177785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177802 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_2177802 : Nat := 118140960795 + 2177802 * 2 ^ 59
def prefixEnd_2177802 : Nat := 4983230072969 + 3 ^ 40 * 2177802 * 2
def baseEnd_2177802 : Nat := 1118259196322993573359477

theorem tailTrace_2177802 : CollatzResearch.WordTrace tailWord_2177802 prefixEnd_2177802 1118259196322993573359477 := by
  unfold tailWord_2177802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19857741114050691953783915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52953976304135178543423773 19857741114050691953783915)
  ·
    refine ⟨29786611671076037930675873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19857741114050691953783915 29786611671076037930675873)
    ·
      refine ⟨22339958753307028448006905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29786611671076037930675873 22339958753307028448006905)
      ·
        refine ⟨16754969064980271336005179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22339958753307028448006905 16754969064980271336005179)
        ·
          refine ⟨25132453597470407004007769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16754969064980271336005179 25132453597470407004007769)
          ·
            refine ⟨18849340198102805253005827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25132453597470407004007769 18849340198102805253005827)
            ·
              refine ⟨28274010297154207879508741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18849340198102805253005827 28274010297154207879508741)
              ·
                refine ⟨5301376930716413977407889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28274010297154207879508741 5301376930716413977407889)
                ·
                  refine ⟨3976032698037310483055917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5301376930716413977407889 3976032698037310483055917)
                  ·
                    refine ⟨1491012261763991431145969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3976032698037310483055917 1491012261763991431145969)
                    ·
                      refine ⟨1118259196322993573359477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491012261763991431145969 1118259196322993573359477)
                      ·
                        rfl

theorem cell23_2177802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_2177802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177802 prefixEnd_2177802 := by exact prefixLift 2177802
  have htrace : WordTrace (prefixWord ++ tailWord_2177802) baseStart_2177802 baseEnd_2177802 := by
    simpa [prefixWord, tailWord_2177802, baseEnd_2177802] using wordTrace_append hprefix tailTrace_2177802
  have hstable : (prefixWord ++ tailWord_2177802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177802).length < 2 ^ (prefixWord ++ tailWord_2177802).sum := by decide
  have hdescent : baseEnd_2177802 < baseStart_2177802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177825 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2177825 : Nat := 118140960795 + 2177825 * 2 ^ 59
def prefixEnd_2177825 : Nat := 4983230072969 + 3 ^ 40 * 2177825 * 2
def baseEnd_2177825 : Nat := 372757002126015661123957

theorem tailTrace_2177825 : CollatzResearch.WordTrace tailWord_2177825 prefixEnd_2177825 372757002126015661123957 := by
  unfold tailWord_2177825
  simp only [CollatzResearch.WordTrace]
  refine ⟨79431803335119442743222929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52954535556746295162148619 79431803335119442743222929)
  ·
    refine ⟨59573852501339582057417197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79431803335119442743222929 59573852501339582057417197)
    ·
      refine ⟨22340194688002343271531449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59573852501339582057417197 22340194688002343271531449)
      ·
        refine ⟨16755146016001757453648587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22340194688002343271531449 16755146016001757453648587)
        ·
          refine ⟨25132719024002636180472881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16755146016001757453648587 25132719024002636180472881)
          ·
            refine ⟨18849539268001977135354661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25132719024002636180472881 18849539268001977135354661)
            ·
              refine ⟨3534288612750370712878999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18849539268001977135354661 3534288612750370712878999)
              ·
                refine ⟨5301432919125556069318499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534288612750370712878999 5301432919125556069318499)
                ·
                  refine ⟨7952149378688334103977749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301432919125556069318499 7952149378688334103977749)
                  ·
                    refine ⟨372757002126015661123957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7952149378688334103977749 372757002126015661123957)
                    ·
                      rfl

theorem cell23_2177825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2177825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177825 prefixEnd_2177825 := by exact prefixLift 2177825
  have htrace : WordTrace (prefixWord ++ tailWord_2177825) baseStart_2177825 baseEnd_2177825 := by
    simpa [prefixWord, tailWord_2177825, baseEnd_2177825] using wordTrace_append hprefix tailTrace_2177825
  have hstable : (prefixWord ++ tailWord_2177825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177825).length < 2 ^ (prefixWord ++ tailWord_2177825).sum := by decide
  have hdescent : baseEnd_2177825 < baseStart_2177825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177832 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2177832 : Nat := 118140960795 + 2177832 * 2 ^ 59
def prefixEnd_2177832 : Nat := 4983230072969 + 3 ^ 40 * 2177832 * 2
def baseEnd_2177832 : Nat := 1118274600742628455984339

theorem tailTrace_2177832 : CollatzResearch.WordTrace tailWord_2177832 prefixEnd_2177832 1118274600742628455984339 := by
  unfold tailWord_2177832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39716029323047041469363875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52954705764062721959151833 39716029323047041469363875)
  ·
    refine ⟨59574043984570562204045813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39716029323047041469363875 59574043984570562204045813)
    ·
      refine ⟨5585066623553490206629295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59574043984570562204045813 5585066623553490206629295)
      ·
        refine ⟨8377599935330235309943943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5585066623553490206629295 8377599935330235309943943)
        ·
          refine ⟨12566399902995352964915915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8377599935330235309943943 12566399902995352964915915)
          ·
            refine ⟨18849599854493029447373873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12566399902995352964915915 18849599854493029447373873)
            ·
              refine ⟨14137199890869772085530405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18849599854493029447373873 14137199890869772085530405)
              ·
                refine ⟨2650724979538082266036951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14137199890869772085530405 2650724979538082266036951)
                ·
                  refine ⟨3976087469307123399055427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650724979538082266036951 3976087469307123399055427)
                  ·
                    refine ⟨5964131203960685098583141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976087469307123399055427 5964131203960685098583141)
                    ·
                      refine ⟨1118274600742628455984339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5964131203960685098583141 1118274600742628455984339)
                      ·
                        rfl

theorem cell23_2177832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2177832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177832 prefixEnd_2177832 := by exact prefixLift 2177832
  have htrace : WordTrace (prefixWord ++ tailWord_2177832) baseStart_2177832 baseEnd_2177832 := by
    simpa [prefixWord, tailWord_2177832, baseEnd_2177832] using wordTrace_append hprefix tailTrace_2177832
  have hstable : (prefixWord ++ tailWord_2177832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177832).length < 2 ^ (prefixWord ++ tailWord_2177832).sum := by decide
  have hdescent : baseEnd_2177832 < baseStart_2177832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177869 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2177869 : Nat := 118140960795 + 2177869 * 2 ^ 59
def prefixEnd_2177869 : Nat := 4983230072969 + 3 ^ 40 * 2177869 * 2
def baseEnd_2177869 : Nat := 1118293599526844811221669

theorem tailTrace_2177869 : CollatzResearch.WordTrace tailWord_2177869 prefixEnd_2177869 1118293599526844811221669 := by
  unfold tailWord_2177869
  simp only [CollatzResearch.WordTrace]
  refine ⟨79433408146960038257824661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52955605431306692171883107 79433408146960038257824661)
  ·
    refine ⟨3723441006888751793335531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79433408146960038257824661 3723441006888751793335531)
    ·
      refine ⟨5585161510333127690003297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723441006888751793335531 5585161510333127690003297)
      ·
        refine ⟨4188871132749845767502473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5585161510333127690003297 4188871132749845767502473)
        ·
          refine ⟨3141653349562384325626855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188871132749845767502473 3141653349562384325626855)
          ·
            refine ⟨4712480024343576488440283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141653349562384325626855 4712480024343576488440283)
            ·
              refine ⟨7068720036515364732660425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712480024343576488440283 7068720036515364732660425)
              ·
                refine ⟨5301540027386523549495319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7068720036515364732660425 5301540027386523549495319)
                ·
                  refine ⟨7952310041079785324242979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301540027386523549495319 7952310041079785324242979)
                  ·
                    refine ⟨11928465061619677986364469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7952310041079785324242979 11928465061619677986364469)
                    ·
                      refine ⟨1118293599526844811221669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11928465061619677986364469 1118293599526844811221669)
                      ·
                        rfl

theorem cell23_2177869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2177869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177869 prefixEnd_2177869 := by exact prefixLift 2177869
  have htrace : WordTrace (prefixWord ++ tailWord_2177869) baseStart_2177869 baseEnd_2177869 := by
    simpa [prefixWord, tailWord_2177869, baseEnd_2177869] using wordTrace_append hprefix tailTrace_2177869
  have hstable : (prefixWord ++ tailWord_2177869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177869).length < 2 ^ (prefixWord ++ tailWord_2177869).sum := by decide
  have hdescent : baseEnd_2177869 < baseStart_2177869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177876 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2177876 : Nat := 118140960795 + 2177876 * 2 ^ 59
def prefixEnd_2177876 : Nat := 4983230072969 + 3 ^ 40 * 2177876 * 2
def baseEnd_2177876 : Nat := 372765731297142094611379

theorem tailTrace_2177876 : CollatzResearch.WordTrace tailWord_2177876 prefixEnd_2177876 372765731297142094611379 := by
  unfold tailWord_2177876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39716831728967339226664741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52955775638623118968886321 39716831728967339226664741)
  ·
    refine ⟨7446905949181376104999639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39716831728967339226664741 7446905949181376104999639)
    ·
      refine ⟨11170358923772064157499459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446905949181376104999639 11170358923772064157499459)
      ·
        refine ⟨16755538385658096236249189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11170358923772064157499459 16755538385658096236249189)
        ·
          refine ⟨3141663447310893044296723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16755538385658096236249189 3141663447310893044296723)
          ·
            refine ⟨4712495170966339566445085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141663447310893044296723 4712495170966339566445085)
            ·
              refine ⟨1767185689112377337416907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712495170966339566445085 1767185689112377337416907)
              ·
                refine ⟨2650778533668566006125361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767185689112377337416907 2650778533668566006125361)
                ·
                  refine ⟨1988083900251424504594021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650778533668566006125361 1988083900251424504594021)
                  ·
                    refine ⟨372765731297142094611379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988083900251424504594021 372765731297142094611379)
                    ·
                      rfl

theorem cell23_2177876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2177876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177876 prefixEnd_2177876 := by exact prefixLift 2177876
  have htrace : WordTrace (prefixWord ++ tailWord_2177876) baseStart_2177876 baseEnd_2177876 := by
    simpa [prefixWord, tailWord_2177876, baseEnd_2177876] using wordTrace_append hprefix tailTrace_2177876
  have hstable : (prefixWord ++ tailWord_2177876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177876).length < 2 ^ (prefixWord ++ tailWord_2177876).sum := by decide
  have hdescent : baseEnd_2177876 < baseStart_2177876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177882 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_2177882 : Nat := 118140960795 + 2177882 * 2 ^ 59
def prefixEnd_2177882 : Nat := 4983230072969 + 3 ^ 40 * 2177882 * 2
def baseEnd_2177882 : Nat := 1118300274775353260359109

theorem tailTrace_2177882 : CollatzResearch.WordTrace tailWord_2177882 prefixEnd_2177882 1118300274775353260359109 := by
  unfold tailWord_2177882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19858470573978235369511975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52955921530608627652031933 19858470573978235369511975)
  ·
    refine ⟨29787705860967353054267963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19858470573978235369511975 29787705860967353054267963)
    ·
      refine ⟨44681558791451029581401945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29787705860967353054267963 44681558791451029581401945)
      ·
        refine ⟨33511169093588272186051459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44681558791451029581401945 33511169093588272186051459)
        ·
          refine ⟨50266753640382408279077189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33511169093588272186051459 50266753640382408279077189)
          ·
            refine ⟨9425016307571701552326973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50266753640382408279077189 9425016307571701552326973)
            ·
              refine ⟨3534381115339388082122615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9425016307571701552326973 3534381115339388082122615)
              ·
                refine ⟨5301571673009082123183923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534381115339388082122615 5301571673009082123183923)
                ·
                  refine ⟨7952357509513623184775885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5301571673009082123183923 7952357509513623184775885)
                  ·
                    refine ⟨2982134066067608694290957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7952357509513623184775885 2982134066067608694290957)
                    ·
                      refine ⟨1118300274775353260359109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982134066067608694290957 1118300274775353260359109)
                      ·
                        rfl

theorem cell23_2177882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_2177882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177882 prefixEnd_2177882 := by exact prefixLift 2177882
  have htrace : WordTrace (prefixWord ++ tailWord_2177882) baseStart_2177882 baseEnd_2177882 := by
    simpa [prefixWord, tailWord_2177882, baseEnd_2177882] using wordTrace_append hprefix tailTrace_2177882
  have hstable : (prefixWord ++ tailWord_2177882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177882).length < 2 ^ (prefixWord ++ tailWord_2177882).sum := by decide
  have hdescent : baseEnd_2177882 < baseStart_2177882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177895 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2177895 : Nat := 118140960795 + 2177895 * 2 ^ 59
def prefixEnd_2177895 : Nat := 4983230072969 + 3 ^ 40 * 2177895 * 2
def baseEnd_2177895 : Nat := 1118306950023861709496549

theorem tailTrace_2177895 : CollatzResearch.WordTrace tailWord_2177895 prefixEnd_2177895 1118306950023861709496549 := by
  unfold tailWord_2177895
  simp only [CollatzResearch.WordTrace]
  refine ⟨79434356444865844698271139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52956237629910563132180759 79434356444865844698271139)
  ·
    refine ⟨119151534667298767047406709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79434356444865844698271139 119151534667298767047406709)
    ·
      refine ⟨11170456375059259410694379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119151534667298767047406709 11170456375059259410694379)
      ·
        refine ⟨16755684562588889116041569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11170456375059259410694379 16755684562588889116041569)
        ·
          refine ⟨12566763421941666837031177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16755684562588889116041569 12566763421941666837031177)
          ·
            refine ⟨9425072566456250127773383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12566763421941666837031177 9425072566456250127773383)
            ·
              refine ⟨14137608849684375191660075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9425072566456250127773383 14137608849684375191660075)
              ·
                refine ⟨21206413274526562787490113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14137608849684375191660075 21206413274526562787490113)
                ·
                  refine ⟨15904809955894922090617585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21206413274526562787490113 15904809955894922090617585)
                  ·
                    refine ⟨11928607466921191567963189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15904809955894922090617585 11928607466921191567963189)
                    ·
                      refine ⟨1118306950023861709496549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11928607466921191567963189 1118306950023861709496549)
                      ·
                        rfl

theorem cell23_2177895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2177895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2177895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2177895 prefixEnd_2177895 := by exact prefixLift 2177895
  have htrace : WordTrace (prefixWord ++ tailWord_2177895) baseStart_2177895 baseEnd_2177895 := by
    simpa [prefixWord, tailWord_2177895, baseEnd_2177895] using wordTrace_append hprefix tailTrace_2177895
  have hstable : (prefixWord ++ tailWord_2177895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177895).length < 2 ^ (prefixWord ++ tailWord_2177895).sum := by decide
  have hdescent : baseEnd_2177895 < baseStart_2177895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178009 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_2178009 : Nat := 118140960795 + 2178009 * 2 ^ 59
def prefixEnd_2178009 : Nat := 4983230072969 + 3 ^ 40 * 2178009 * 2
def baseEnd_2178009 : Nat := 372788495606158087823675

theorem tailTrace_2178009 : CollatzResearch.WordTrace tailWord_2178009 prefixEnd_2178009 372788495606158087823675 := by
  unfold tailWord_2178009
  simp only [CollatzResearch.WordTrace]
  refine ⟨79438514366452842167921081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52959009577635228111947387 79438514366452842167921081)
  ·
    refine ⟨59578885774839631625940811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79438514366452842167921081 59578885774839631625940811)
    ·
      refine ⟨89368328662259447438911217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59578885774839631625940811 89368328662259447438911217)
      ·
        refine ⟨67026246496694585579183413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89368328662259447438911217 67026246496694585579183413)
        ·
          refine ⟨6283710609065117398048445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67026246496694585579183413 6283710609065117398048445)
          ·
            refine ⟨2356391478399419024268167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6283710609065117398048445 2356391478399419024268167)
            ·
              refine ⟨3534587217599128536402251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356391478399419024268167 3534587217599128536402251)
              ·
                refine ⟨5301880826398692804603377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534587217599128536402251 5301880826398692804603377)
                ·
                  refine ⟨3976410619799019603452533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5301880826398692804603377 3976410619799019603452533)
                  ·
                    refine ⟨372788495606158087823675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3976410619799019603452533 372788495606158087823675)
                    ·
                      rfl

theorem cell23_2178009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_2178009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178009 prefixEnd_2178009 := by exact prefixLift 2178009
  have htrace : WordTrace (prefixWord ++ tailWord_2178009) baseStart_2178009 baseEnd_2178009 := by
    simpa [prefixWord, tailWord_2178009, baseEnd_2178009] using wordTrace_append hprefix tailTrace_2178009
  have hstable : (prefixWord ++ tailWord_2178009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178009).length < 2 ^ (prefixWord ++ tailWord_2178009).sum := by decide
  have hdescent : baseEnd_2178009 < baseStart_2178009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178025 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_2178025 : Nat := 118140960795 + 2178025 * 2 ^ 59
def prefixEnd_2178025 : Nat := 4983230072969 + 3 ^ 40 * 2178025 * 2
def baseEnd_2178025 : Nat := 1118373702508946200870951

theorem tailTrace_2178025 : CollatzResearch.WordTrace tailWord_2178025 prefixEnd_2178025 1118373702508946200870951 := by
  unfold tailWord_2178025
  simp only [CollatzResearch.WordTrace]
  refine ⟨79439097934394876900503529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52959398622929917933669019 79439097934394876900503529)
  ·
    refine ⟨59579323450796157675377647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79439097934394876900503529 59579323450796157675377647)
    ·
      refine ⟨89368985176194236513066471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59579323450796157675377647 89368985176194236513066471)
      ·
        refine ⟨134053477764291354769599707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89368985176194236513066471 134053477764291354769599707)
        ·
          refine ⟨201080216646437032154399561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134053477764291354769599707 201080216646437032154399561)
          ·
            refine ⟨150810162484827774115799671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201080216646437032154399561 150810162484827774115799671)
            ·
              refine ⟨226215243727241661173699507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150810162484827774115799671 226215243727241661173699507)
              ·
                refine ⟨339322865590862491760549261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226215243727241661173699507 339322865590862491760549261)
                ·
                  refine ⟨127246074596573434410205973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339322865590862491760549261 127246074596573434410205973)
                  ·
                    refine ⟨5964659746714379737978405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 127246074596573434410205973 5964659746714379737978405)
                    ·
                      refine ⟨1118373702508946200870951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5964659746714379737978405 1118373702508946200870951)
                      ·
                        rfl

theorem cell23_2178025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_2178025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178025 prefixEnd_2178025 := by exact prefixLift 2178025
  have htrace : WordTrace (prefixWord ++ tailWord_2178025) baseStart_2178025 baseEnd_2178025 := by
    simpa [prefixWord, tailWord_2178025, baseEnd_2178025] using wordTrace_append hprefix tailTrace_2178025
  have hstable : (prefixWord ++ tailWord_2178025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178025).length < 2 ^ (prefixWord ++ tailWord_2178025).sum := by decide
  have hdescent : baseEnd_2178025 < baseStart_2178025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178032 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_2178032 : Nat := 118140960795 + 2178032 * 2 ^ 59
def prefixEnd_2178032 : Nat := 4983230072969 + 3 ^ 40 * 2178032 * 2
def baseEnd_2178032 : Nat := 1118377296873527673483419

theorem tailTrace_2178032 : CollatzResearch.WordTrace tailWord_2178032 prefixEnd_2178032 1118377296873527673483419 := by
  unfold tailWord_2178032
  simp only [CollatzResearch.WordTrace]
  refine ⟨39719676622684758548004175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52959568830246344730672233 39719676622684758548004175)
  ·
    refine ⟨59579514934027137822006263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39719676622684758548004175 59579514934027137822006263)
    ·
      refine ⟨89369272401040706733009395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59579514934027137822006263 89369272401040706733009395)
      ·
        refine ⟨134053908601561060099514093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89369272401040706733009395 134053908601561060099514093)
        ·
          refine ⟨50270215725585397537317785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134053908601561060099514093 50270215725585397537317785)
          ·
            refine ⟨37702661794189048152988339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50270215725585397537317785 37702661794189048152988339)
            ·
              refine ⟨56553992691283572229482509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37702661794189048152988339 56553992691283572229482509)
              ·
                refine ⟨21207747259231339586055941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56553992691283572229482509 21207747259231339586055941)
                ·
                  refine ⟨3976452611105876172385489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21207747259231339586055941 3976452611105876172385489)
                  ·
                    refine ⟨2982339458329407129289117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3976452611105876172385489 2982339458329407129289117)
                    ·
                      refine ⟨1118377296873527673483419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982339458329407129289117 1118377296873527673483419)
                      ·
                        rfl

theorem cell23_2178032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_2178032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178032 prefixEnd_2178032 := by exact prefixLift 2178032
  have htrace : WordTrace (prefixWord ++ tailWord_2178032) baseStart_2178032 baseEnd_2178032 := by
    simpa [prefixWord, tailWord_2178032, baseEnd_2178032] using wordTrace_append hprefix tailTrace_2178032
  have hstable : (prefixWord ++ tailWord_2178032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178032).length < 2 ^ (prefixWord ++ tailWord_2178032).sum := by decide
  have hdescent : baseEnd_2178032 < baseStart_2178032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178065 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2178065 : Nat := 118140960795 + 2178065 * 2 ^ 59
def prefixEnd_2178065 : Nat := 4983230072969 + 3 ^ 40 * 2178065 * 2
def baseEnd_2178065 : Nat := 372798080578375348123589

theorem tailTrace_2178065 : CollatzResearch.WordTrace tailWord_2178065 prefixEnd_2178065 372798080578375348123589 := by
  unfold tailWord_2178065
  simp only [CollatzResearch.WordTrace]
  refine ⟨79440556854249963731959649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52960371236166642487973099 79440556854249963731959649)
  ·
    refine ⟨59580417640687472798969737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79440556854249963731959649 59580417640687472798969737)
    ·
      refine ⟨44685313230515604599227303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59580417640687472798969737 44685313230515604599227303)
      ·
        refine ⟨67027969845773406898840955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44685313230515604599227303 67027969845773406898840955)
        ·
          refine ⟨100541954768660110348261433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67027969845773406898840955 100541954768660110348261433)
          ·
            refine ⟨75406466076495082761196075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100541954768660110348261433 75406466076495082761196075)
            ·
              refine ⟨113109699114742624141794113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75406466076495082761196075 113109699114742624141794113)
              ·
                refine ⟨84832274336056968106345585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113109699114742624141794113 84832274336056968106345585)
                ·
                  refine ⟨63624205752042726079759189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84832274336056968106345585 63624205752042726079759189)
                  ·
                    refine ⟨372798080578375348123589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63624205752042726079759189 372798080578375348123589)
                    ·
                      rfl

theorem cell23_2178065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2178065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178065 prefixEnd_2178065 := by exact prefixLift 2178065
  have htrace : WordTrace (prefixWord ++ tailWord_2178065) baseStart_2178065 baseEnd_2178065 := by
    simpa [prefixWord, tailWord_2178065, baseEnd_2178065] using wordTrace_append hprefix tailTrace_2178065
  have hstable : (prefixWord ++ tailWord_2178065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178065).length < 2 ^ (prefixWord ++ tailWord_2178065).sum := by decide
  have hdescent : baseEnd_2178065 < baseStart_2178065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178075 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_2178075 : Nat := 118140960795 + 2178075 * 2 ^ 59
def prefixEnd_2178075 : Nat := 4983230072969 + 3 ^ 40 * 2178075 * 2
def baseEnd_2178075 : Nat := 1118399376541671005245721

theorem tailTrace_2178075 : CollatzResearch.WordTrace tailWord_2178075 prefixEnd_2178075 1118399376541671005245721 := by
  unfold tailWord_2178075
  simp only [CollatzResearch.WordTrace]
  refine ⟨79440921584213735439823679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52960614389475823626549119 79440921584213735439823679)
  ·
    refine ⟨119161382376320603159735519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79440921584213735439823679 119161382376320603159735519)
    ·
      refine ⟨178742073564480904739603279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119161382376320603159735519 178742073564480904739603279)
      ·
        refine ⟨268113110346721357109404919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178742073564480904739603279 268113110346721357109404919)
        ·
          refine ⟨402169665520082035664107379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268113110346721357109404919 402169665520082035664107379)
          ·
            refine ⟨603254498280123053496161069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402169665520082035664107379 603254498280123053496161069)
            ·
              refine ⟨226220436855046145061060401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 603254498280123053496161069 226220436855046145061060401)
              ·
                refine ⟨169665327641284608795795301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226220436855046145061060401 169665327641284608795795301)
                ·
                  refine ⟨31812248932740864149211619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169665327641284608795795301 31812248932740864149211619)
                  ·
                    refine ⟨47718373399111296223817429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31812248932740864149211619 47718373399111296223817429)
                    ·
                      refine ⟨1118399376541671005245721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47718373399111296223817429 1118399376541671005245721)
                      ·
                        rfl

theorem cell23_2178075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_2178075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178075 prefixEnd_2178075 := by exact prefixLift 2178075
  have htrace : WordTrace (prefixWord ++ tailWord_2178075) baseStart_2178075 baseEnd_2178075 := by
    simpa [prefixWord, tailWord_2178075, baseEnd_2178075] using wordTrace_append hprefix tailTrace_2178075
  have hstable : (prefixWord ++ tailWord_2178075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178075).length < 2 ^ (prefixWord ++ tailWord_2178075).sum := by decide
  have hdescent : baseEnd_2178075 < baseStart_2178075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178090 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2178090 : Nat := 118140960795 + 2178090 * 2 ^ 59
def prefixEnd_2178090 : Nat := 4983230072969 + 3 ^ 40 * 2178090 * 2
def baseEnd_2178090 : Nat := 372802359583829482186051

theorem tailTrace_2178090 : CollatzResearch.WordTrace tailWord_2178090 prefixEnd_2178090 372802359583829482186051 := by
  unfold tailWord_2178090
  simp only [CollatzResearch.WordTrace]
  refine ⟨19860367169789848250404931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52960979119439595334413149 19860367169789848250404931)
  ·
    refine ⟨29790550754684772375607397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19860367169789848250404931 29790550754684772375607397)
    ·
      refine ⟨5585728266503394820426387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29790550754684772375607397 5585728266503394820426387)
      ·
        refine ⟨8378592399755092230639581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5585728266503394820426387 8378592399755092230639581)
        ·
          refine ⟨3141972149908159586489843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8378592399755092230639581 3141972149908159586489843)
          ·
            refine ⟨4712958224862239379734765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141972149908159586489843 4712958224862239379734765)
            ·
              refine ⟨1767359334323339767400537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712958224862239379734765 1767359334323339767400537)
              ·
                refine ⟨1325519500742504825550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767359334323339767400537 1325519500742504825550403)
                ·
                  refine ⟨1988279251113757238325605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325519500742504825550403 1988279251113757238325605)
                  ·
                    refine ⟨372802359583829482186051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988279251113757238325605 372802359583829482186051)
                    ·
                      rfl

theorem cell23_2178090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2178090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178090 prefixEnd_2178090 := by exact prefixLift 2178090
  have htrace : WordTrace (prefixWord ++ tailWord_2178090) baseStart_2178090 baseEnd_2178090 := by
    simpa [prefixWord, tailWord_2178090, baseEnd_2178090] using wordTrace_append hprefix tailTrace_2178090
  have hstable : (prefixWord ++ tailWord_2178090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178090).length < 2 ^ (prefixWord ++ tailWord_2178090).sum := by decide
  have hdescent : baseEnd_2178090 < baseStart_2178090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178112 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_2178112 : Nat := 118140960795 + 2178112 * 2 ^ 59
def prefixEnd_2178112 : Nat := 4983230072969 + 3 ^ 40 * 2178112 * 2
def baseEnd_2178112 : Nat := 372806125108629120161017

theorem tailTrace_2178112 : CollatzResearch.WordTrace tailWord_2178112 prefixEnd_2178112 372806125108629120161017 := by
  unfold tailWord_2178112
  simp only [CollatzResearch.WordTrace]
  refine ⟨39721135542539845379460295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52961514056719793839280393 39721135542539845379460295)
  ·
    refine ⟨59581703313809768069190443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39721135542539845379460295 59581703313809768069190443)
    ·
      refine ⟨89372554970714652103785665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59581703313809768069190443 89372554970714652103785665)
      ·
        refine ⟨67029416228035989077839249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89372554970714652103785665 67029416228035989077839249)
        ·
          refine ⟨50272062171026991808379437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67029416228035989077839249 50272062171026991808379437)
          ·
            refine ⟨18852023314135121928142289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50272062171026991808379437 18852023314135121928142289)
            ·
              refine ⟨14139017485601341446106717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18852023314135121928142289 14139017485601341446106717)
              ·
                refine ⟨5302131557100503042290019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14139017485601341446106717 5302131557100503042290019)
                ·
                  refine ⟨7953197335650754563435029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5302131557100503042290019 7953197335650754563435029)
                  ·
                    refine ⟨372806125108629120161017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7953197335650754563435029 372806125108629120161017)
                    ·
                      rfl

theorem cell23_2178112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_2178112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178112 prefixEnd_2178112 := by exact prefixLift 2178112
  have htrace : WordTrace (prefixWord ++ tailWord_2178112) baseStart_2178112 baseEnd_2178112 := by
    simpa [prefixWord, tailWord_2178112, baseEnd_2178112] using wordTrace_append hprefix tailTrace_2178112
  have hstable : (prefixWord ++ tailWord_2178112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178112).length < 2 ^ (prefixWord ++ tailWord_2178112).sum := by decide
  have hdescent : baseEnd_2178112 < baseStart_2178112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178119 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_2178119 : Nat := 118140960795 + 2178119 * 2 ^ 59
def prefixEnd_2178119 : Nat := 4983230072969 + 3 ^ 40 * 2178119 * 2
def baseEnd_2178119 : Nat := 1118421969690468833095519

theorem tailTrace_2178119 : CollatzResearch.WordTrace tailWord_2178119 prefixEnd_2178119 1118421969690468833095519 := by
  unfold tailWord_2178119
  simp only [CollatzResearch.WordTrace]
  refine ⟨79442526396054330954425411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52961684264036220636283607 79442526396054330954425411)
  ·
    refine ⟨119163789594081496431638117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79442526396054330954425411 119163789594081496431638117)
    ·
      refine ⟨22343210548890280580932147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119163789594081496431638117 22343210548890280580932147)
      ·
        refine ⟨33514815823335420871398221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343210548890280580932147 33514815823335420871398221)
        ·
          refine ⟨12568055933750782826774333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33514815823335420871398221 12568055933750782826774333)
          ·
            refine ⟨4713020975156543560040375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12568055933750782826774333 4713020975156543560040375)
            ·
              refine ⟨7069531462734815340060563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713020975156543560040375 7069531462734815340060563)
              ·
                refine ⟨10604297194102223010090845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7069531462734815340060563 10604297194102223010090845)
                ·
                  refine ⟨3976611447788333628784067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10604297194102223010090845 3976611447788333628784067)
                  ·
                    refine ⟨5964917171682500443176101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976611447788333628784067 5964917171682500443176101)
                    ·
                      refine ⟨1118421969690468833095519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5964917171682500443176101 1118421969690468833095519)
                      ·
                        rfl

theorem cell23_2178119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_2178119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178119 prefixEnd_2178119 := by exact prefixLift 2178119
  have htrace : WordTrace (prefixWord ++ tailWord_2178119) baseStart_2178119 baseEnd_2178119 := by
    simpa [prefixWord, tailWord_2178119, baseEnd_2178119] using wordTrace_append hprefix tailTrace_2178119
  have hstable : (prefixWord ++ tailWord_2178119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178119).length < 2 ^ (prefixWord ++ tailWord_2178119).sum := by decide
  have hdescent : baseEnd_2178119 < baseStart_2178119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178122 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2178122 : Nat := 118140960795 + 2178122 * 2 ^ 59
def prefixEnd_2178122 : Nat := 4983230072969 + 3 ^ 40 * 2178122 * 2
def baseEnd_2178122 : Nat := 1118423510132432321358005

theorem tailTrace_2178122 : CollatzResearch.WordTrace tailWord_2178122 prefixEnd_2178122 1118423510132432321358005 := by
  unfold tailWord_2178122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19860658953760865616696155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52961757210028974977856413 19860658953760865616696155)
  ·
    refine ⟨29790988430641298425044233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19860658953760865616696155 29790988430641298425044233)
    ·
      refine ⟨22343241322980973818783175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29790988430641298425044233 22343241322980973818783175)
      ·
        refine ⟨33514861984471460728174763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343241322980973818783175 33514861984471460728174763)
        ·
          refine ⟨50272292976707191092262145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33514861984471460728174763 50272292976707191092262145)
          ·
            refine ⟨37704219732530393319196609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50272292976707191092262145 37704219732530393319196609)
            ·
              refine ⟨28278164799397794989397457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37704219732530393319196609 28278164799397794989397457)
              ·
                refine ⟨21208623599548346242048093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28278164799397794989397457 21208623599548346242048093)
                ·
                  refine ⟨7953233849830629840768035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21208623599548346242048093 7953233849830629840768035)
                  ·
                    refine ⟨11929850774745944761152053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7953233849830629840768035 11929850774745944761152053)
                    ·
                      refine ⟨1118423510132432321358005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11929850774745944761152053 1118423510132432321358005)
                      ·
                        rfl

theorem cell23_2178122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2178122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178122 prefixEnd_2178122 := by exact prefixLift 2178122
  have htrace : WordTrace (prefixWord ++ tailWord_2178122) baseStart_2178122 baseEnd_2178122 := by
    simpa [prefixWord, tailWord_2178122, baseEnd_2178122] using wordTrace_append hprefix tailTrace_2178122
  have hstable : (prefixWord ++ tailWord_2178122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178122).length < 2 ^ (prefixWord ++ tailWord_2178122).sum := by decide
  have hdescent : baseEnd_2178122 < baseStart_2178122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178136 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_2178136 : Nat := 118140960795 + 2178136 * 2 ^ 59
def prefixEnd_2178136 : Nat := 4983230072969 + 3 ^ 40 * 2178136 * 2
def baseEnd_2178136 : Nat := 1118430698861595266582941

theorem tailTrace_2178136 : CollatzResearch.WordTrace tailWord_2178136 prefixEnd_2178136 1118430698861595266582941 := by
  unfold tailWord_2178136
  simp only [CollatzResearch.WordTrace]
  refine ⟨39721573218496371428897131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52962097624661828571862841 39721573218496371428897131)
  ·
    refine ⟨59582359827744557143345697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39721573218496371428897131 59582359827744557143345697)
    ·
      refine ⟨44686769870808417857509273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59582359827744557143345697 44686769870808417857509273)
      ·
        refine ⟨33515077403106313393131955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44686769870808417857509273 33515077403106313393131955)
        ·
          refine ⟨50272616104659470089697933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33515077403106313393131955 50272616104659470089697933)
          ·
            refine ⟨18852231039247301283636725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50272616104659470089697933 18852231039247301283636725)
            ·
              refine ⟨1767396659929434495340943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18852231039247301283636725 1767396659929434495340943)
              ·
                refine ⟨2651094989894151743011415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767396659929434495340943 2651094989894151743011415)
                ·
                  refine ⟨3976642484841227614517123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651094989894151743011415 3976642484841227614517123)
                  ·
                    refine ⟨5964963727261841421775685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976642484841227614517123 5964963727261841421775685)
                    ·
                      refine ⟨1118430698861595266582941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5964963727261841421775685 1118430698861595266582941)
                      ·
                        rfl

theorem cell23_2178136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_2178136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178136 prefixEnd_2178136 := by exact prefixLift 2178136
  have htrace : WordTrace (prefixWord ++ tailWord_2178136) baseStart_2178136 baseEnd_2178136 := by
    simpa [prefixWord, tailWord_2178136, baseEnd_2178136] using wordTrace_append hprefix tailTrace_2178136
  have hstable : (prefixWord ++ tailWord_2178136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178136).length < 2 ^ (prefixWord ++ tailWord_2178136).sum := by decide
  have hdescent : baseEnd_2178136 < baseStart_2178136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178166 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2178166 : Nat := 118140960795 + 2178166 * 2 ^ 59
def prefixEnd_2178166 : Nat := 4983230072969 + 3 ^ 40 * 2178166 * 2
def baseEnd_2178166 : Nat := 1118446103281230149207803

theorem tailTrace_2178166 : CollatzResearch.WordTrace tailWord_2178166 prefixEnd_2178166 1118446103281230149207803 := by
  unfold tailWord_2178166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965265039180253623836647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52962827084589371987590901 4965265039180253623836647)
  ·
    refine ⟨7447897558770380435754971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4965265039180253623836647 7447897558770380435754971)
    ·
      refine ⟨11171846338155570653632457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7447897558770380435754971 11171846338155570653632457)
      ·
        refine ⟨8378884753616677990224343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11171846338155570653632457 8378884753616677990224343)
        ·
          refine ⟨12568327130425016985336515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378884753616677990224343 12568327130425016985336515)
          ·
            refine ⟨18852490695637525478004773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568327130425016985336515 18852490695637525478004773)
            ·
              refine ⟨3534842005432036027125895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18852490695637525478004773 3534842005432036027125895)
              ·
                refine ⟨5302263008148054040688843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534842005432036027125895 5302263008148054040688843)
                ·
                  refine ⟨7953394512222081061033265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5302263008148054040688843 7953394512222081061033265)
                  ·
                    refine ⟨5965045884166560795774949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7953394512222081061033265 5965045884166560795774949)
                    ·
                      refine ⟨1118446103281230149207803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5965045884166560795774949 1118446103281230149207803)
                      ·
                        rfl

theorem cell23_2178166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2178166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178166 prefixEnd_2178166 := by exact prefixLift 2178166
  have htrace : WordTrace (prefixWord ++ tailWord_2178166) baseStart_2178166 baseEnd_2178166 := by
    simpa [prefixWord, tailWord_2178166, baseEnd_2178166] using wordTrace_append hprefix tailTrace_2178166
  have hstable : (prefixWord ++ tailWord_2178166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178166).length < 2 ^ (prefixWord ++ tailWord_2178166).sum := by decide
  have hdescent : baseEnd_2178166 < baseStart_2178166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178172 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_2178172 : Nat := 118140960795 + 2178172 * 2 ^ 59
def prefixEnd_2178172 : Nat := 4983230072969 + 3 ^ 40 * 2178172 * 2
def baseEnd_2178172 : Nat := 372816394721719041910925

theorem tailTrace_2178172 : CollatzResearch.WordTrace tailWord_2178172 prefixEnd_2178172 372816394721719041910925 := by
  unfold tailWord_2178172
  simp only [CollatzResearch.WordTrace]
  refine ⟨39722229732431160503052385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52962972976574880670736513 39722229732431160503052385)
  ·
    refine ⟨29791672299323370377289289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39722229732431160503052385 29791672299323370377289289)
    ·
      refine ⟨22343754224492527782966967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29791672299323370377289289 22343754224492527782966967)
      ·
        refine ⟨33515631336738791674450451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343754224492527782966967 33515631336738791674450451)
        ·
          refine ⟨50273447005108187511675677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33515631336738791674450451 50273447005108187511675677)
          ·
            refine ⟨18852542626915570316878379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50273447005108187511675677 18852542626915570316878379)
            ·
              refine ⟨28278813940373355475317569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18852542626915570316878379 28278813940373355475317569)
              ·
                refine ⟨21209110455280016606488177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28278813940373355475317569 21209110455280016606488177)
                ·
                  refine ⟨15906832841460012454866133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21209110455280016606488177 15906832841460012454866133)
                  ·
                    refine ⟨372816394721719041910925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15906832841460012454866133 372816394721719041910925)
                    ·
                      rfl

theorem cell23_2178172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_2178172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178172 prefixEnd_2178172 := by exact prefixLift 2178172
  have htrace : WordTrace (prefixWord ++ tailWord_2178172) baseStart_2178172 baseEnd_2178172 := by
    simpa [prefixWord, tailWord_2178172, baseEnd_2178172] using wordTrace_append hprefix tailTrace_2178172
  have hstable : (prefixWord ++ tailWord_2178172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178172).length < 2 ^ (prefixWord ++ tailWord_2178172).sum := by decide
  have hdescent : baseEnd_2178172 < baseStart_2178172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178174 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2178174 : Nat := 118140960795 + 2178174 * 2 ^ 59
def prefixEnd_2178174 : Nat := 4983230072969 + 3 ^ 40 * 2178174 * 2
def baseEnd_2178174 : Nat := 1118450211126466117907767

theorem tailTrace_2178174 : CollatzResearch.WordTrace tailWord_2178174 prefixEnd_2178174 1118450211126466117907767 := by
  unfold tailWord_2178174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930566551356884418459697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52963021607236716898451717 9930566551356884418459697)
  ·
    refine ⟨7447924913517663313844773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9930566551356884418459697 7447924913517663313844773)
    ·
      refine ⟨1396485921284561871345895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7447924913517663313844773 1396485921284561871345895)
      ·
        refine ⟨2094728881926842807018843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396485921284561871345895 2094728881926842807018843)
        ·
          refine ⟨3142093322890264210528265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094728881926842807018843 3142093322890264210528265)
          ·
            refine ⟨2356569992167698157896199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3142093322890264210528265 2356569992167698157896199)
            ·
              refine ⟨3534854988251547236844299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356569992167698157896199 3534854988251547236844299)
              ·
                refine ⟨5302282482377320855266449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534854988251547236844299 5302282482377320855266449)
                ·
                  refine ⟨3976711861782990641449837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302282482377320855266449 3976711861782990641449837)
                  ·
                    refine ⟨1491266948168621490543689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3976711861782990641449837 1491266948168621490543689)
                    ·
                      refine ⟨1118450211126466117907767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491266948168621490543689 1118450211126466117907767)
                      ·
                        rfl

theorem cell23_2178174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2178174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178174 prefixEnd_2178174 := by exact prefixLift 2178174
  have htrace : WordTrace (prefixWord ++ tailWord_2178174) baseStart_2178174 baseEnd_2178174 := by
    simpa [prefixWord, tailWord_2178174, baseEnd_2178174] using wordTrace_append hprefix tailTrace_2178174
  have hstable : (prefixWord ++ tailWord_2178174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178174).length < 2 ^ (prefixWord ++ tailWord_2178174).sum := by decide
  have hdescent : baseEnd_2178174 < baseStart_2178174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178186 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2178186 : Nat := 118140960795 + 2178186 * 2 ^ 59
def prefixEnd_2178186 : Nat := 4983230072969 + 3 ^ 40 * 2178186 * 2
def baseEnd_2178186 : Nat := 1118456372894320070957711

theorem tailTrace_2178186 : CollatzResearch.WordTrace tailWord_2178186 prefixEnd_2178186 1118456372894320070957711 := by
  unfold tailWord_2178186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19861242521702900349278603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52963313391207734264742941 19861242521702900349278603)
  ·
    refine ⟨29791863782554350523917905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19861242521702900349278603 29791863782554350523917905)
    ·
      refine ⟨22343897836915762892938429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29791863782554350523917905 22343897836915762892938429)
      ·
        refine ⟨8378961688843411084851911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22343897836915762892938429 8378961688843411084851911)
        ·
          refine ⟨12568442533265116627277867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378961688843411084851911 12568442533265116627277867)
          ·
            refine ⟨18852663799897674940916801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568442533265116627277867 18852663799897674940916801)
            ·
              refine ⟨14139497849923256205687601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18852663799897674940916801 14139497849923256205687601)
              ·
                refine ⟨10604623387442442154265701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14139497849923256205687601 10604623387442442154265701)
                ·
                  refine ⟨1988366885145457903924819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10604623387442442154265701 1988366885145457903924819)
                  ·
                    refine ⟨2982550327718186855887229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988366885145457903924819 2982550327718186855887229)
                    ·
                      refine ⟨1118456372894320070957711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982550327718186855887229 1118456372894320070957711)
                      ·
                        rfl

theorem cell23_2178186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2178186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178186 prefixEnd_2178186 := by exact prefixLift 2178186
  have htrace : WordTrace (prefixWord ++ tailWord_2178186) baseStart_2178186 baseEnd_2178186 := by
    simpa [prefixWord, tailWord_2178186, baseEnd_2178186] using wordTrace_append hprefix tailTrace_2178186
  have hstable : (prefixWord ++ tailWord_2178186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178186).length < 2 ^ (prefixWord ++ tailWord_2178186).sum := by decide
  have hdescent : baseEnd_2178186 < baseStart_2178186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178190 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2178190 : Nat := 118140960795 + 2178190 * 2 ^ 59
def prefixEnd_2178190 : Nat := 4983230072969 + 3 ^ 40 * 2178190 * 2
def baseEnd_2178190 : Nat := 1118458426816938055307693

theorem tailTrace_2178190 : CollatzResearch.WordTrace tailWord_2178190 prefixEnd_2178190 1118458426816938055307693 := by
  unfold tailWord_2178190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930639497349638760032503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52963410652531406720173349 9930639497349638760032503)
  ·
    refine ⟨14895959246024458140048755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9930639497349638760032503 14895959246024458140048755)
    ·
      refine ⟨22343938869036687210073133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14895959246024458140048755 22343938869036687210073133)
      ·
        refine ⟨8378977075888757703777425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22343938869036687210073133 8378977075888757703777425)
        ·
          refine ⟨6284232806916568277833069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8378977075888757703777425 6284232806916568277833069)
          ·
            refine ⟨2356587302593713104187401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6284232806916568277833069 2356587302593713104187401)
            ·
              refine ⟨1767440476945284828140551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2356587302593713104187401 1767440476945284828140551)
              ·
                refine ⟨2651160715417927242210827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767440476945284828140551 2651160715417927242210827)
                ·
                  refine ⟨3976741073126890863316241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651160715417927242210827 3976741073126890863316241)
                  ·
                    refine ⟨2982555804845168147487181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3976741073126890863316241 2982555804845168147487181)
                    ·
                      refine ⟨1118458426816938055307693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982555804845168147487181 1118458426816938055307693)
                      ·
                        rfl

theorem cell23_2178190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2178190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178190 prefixEnd_2178190 := by exact prefixLift 2178190
  have htrace : WordTrace (prefixWord ++ tailWord_2178190) baseStart_2178190 baseEnd_2178190 := by
    simpa [prefixWord, tailWord_2178190, baseEnd_2178190] using wordTrace_append hprefix tailTrace_2178190
  have hstable : (prefixWord ++ tailWord_2178190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178190).length < 2 ^ (prefixWord ++ tailWord_2178190).sum := by decide
  have hdescent : baseEnd_2178190 < baseStart_2178190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178192 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_2178192 : Nat := 118140960795 + 2178192 * 2 ^ 59
def prefixEnd_2178192 : Nat := 4983230072969 + 3 ^ 40 * 2178192 * 2
def baseEnd_2178192 : Nat := 1118459453778247047482683

theorem tailTrace_2178192 : CollatzResearch.WordTrace tailWord_2178192 prefixEnd_2178192 1118459453778247047482683 := by
  unfold tailWord_2178192
  simp only [CollatzResearch.WordTrace]
  refine ⟨39722594462394932210916415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52963459283193242947888553 39722594462394932210916415)
  ·
    refine ⟨59583891693592398316374623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39722594462394932210916415 59583891693592398316374623)
    ·
      refine ⟨89375837540388597474561935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59583891693592398316374623 89375837540388597474561935)
      ·
        refine ⟨134063756310582896211842903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89375837540388597474561935 134063756310582896211842903)
        ·
          refine ⟨201095634465874344317764355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134063756310582896211842903 201095634465874344317764355)
          ·
            refine ⟨301643451698811516476646533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201095634465874344317764355 301643451698811516476646533)
            ·
              refine ⟨56558147193527159339371225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301643451698811516476646533 56558147193527159339371225)
              ·
                refine ⟨42418610395145369504528419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56558147193527159339371225 42418610395145369504528419)
                ·
                  refine ⟨63627915592718054256792629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42418610395145369504528419 63627915592718054256792629)
                  ·
                    refine ⟨5965117086817317586574309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63627915592718054256792629 5965117086817317586574309)
                    ·
                      refine ⟨1118459453778247047482683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5965117086817317586574309 1118459453778247047482683)
                      ·
                        rfl

theorem cell23_2178192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_2178192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178192 prefixEnd_2178192 := by exact prefixLift 2178192
  have htrace : WordTrace (prefixWord ++ tailWord_2178192) baseStart_2178192 baseEnd_2178192 := by
    simpa [prefixWord, tailWord_2178192, baseEnd_2178192] using wordTrace_append hprefix tailTrace_2178192
  have hstable : (prefixWord ++ tailWord_2178192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178192).length < 2 ^ (prefixWord ++ tailWord_2178192).sum := by decide
  have hdescent : baseEnd_2178192 < baseStart_2178192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178232 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 9]
def baseStart_2178232 : Nat := 118140960795 + 2178232 * 2 ^ 59
def prefixEnd_2178232 : Nat := 4983230072969 + 3 ^ 40 * 2178232 * 2
def baseEnd_2178232 : Nat := 124275554778269654553611

theorem tailTrace_2178232 : CollatzResearch.WordTrace tailWord_2178232 prefixEnd_2178232 124275554778269654553611 := by
  unfold tailWord_2178232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39723323922322475626644475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52964431896429967502192633 39723323922322475626644475)
  ·
    refine ⟨59584985883483713439966713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39723323922322475626644475 59584985883483713439966713)
    ·
      refine ⟨44688739412612785079975035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59584985883483713439966713 44688739412612785079975035)
      ·
        refine ⟨67033109118919177619962553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44688739412612785079975035 67033109118919177619962553)
        ·
          refine ⟨50274831839189383214971915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67033109118919177619962553 50274831839189383214971915)
          ·
            refine ⟨75412247758784074822457873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50274831839189383214971915 75412247758784074822457873)
            ·
              refine ⟨56559185819088056116843405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75412247758784074822457873 56559185819088056116843405)
              ·
                refine ⟨21209694682158021043816277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56559185819088056116843405 21209694682158021043816277)
                ·
                  refine ⟨124275554778269654553611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21209694682158021043816277 124275554778269654553611)
                  ·
                    rfl

theorem cell23_2178232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_2178232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178232 prefixEnd_2178232 := by exact prefixLift 2178232
  have htrace : WordTrace (prefixWord ++ tailWord_2178232) baseStart_2178232 baseEnd_2178232 := by
    simpa [prefixWord, tailWord_2178232, baseEnd_2178232] using wordTrace_append hprefix tailTrace_2178232
  have hstable : (prefixWord ++ tailWord_2178232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178232).length < 2 ^ (prefixWord ++ tailWord_2178232).sum := by decide
  have hdescent : baseEnd_2178232 < baseStart_2178232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178316 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2178316 : Nat := 118140960795 + 2178316 * 2 ^ 59
def prefixEnd_2178316 : Nat := 4983230072969 + 3 ^ 40 * 2178316 * 2
def baseEnd_2178316 : Nat := 1118523125379404562332113

theorem tailTrace_2178316 : CollatzResearch.WordTrace tailWord_2178316 prefixEnd_2178316 1118523125379404562332113 := by
  unfold tailWord_2178316
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724855788170316799673401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52966474384227089066231201 39724855788170316799673401)
  ·
    refine ⟨29793641841127737599755051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39724855788170316799673401 29793641841127737599755051)
    ·
      refine ⟨44690462761691606399632577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29793641841127737599755051 44690462761691606399632577)
      ·
        refine ⟨33517847071268704799724433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44690462761691606399632577 33517847071268704799724433)
        ·
          refine ⟨25138385303451528599793325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33517847071268704799724433 25138385303451528599793325)
          ·
            refine ⟨9426894488794323224922497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25138385303451528599793325 9426894488794323224922497)
            ·
              refine ⟨7070170866595742418691873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9426894488794323224922497 7070170866595742418691873)
              ·
                refine ⟨5302628149946806814018905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070170866595742418691873 5302628149946806814018905)
                ·
                  refine ⟨3976971112460105110514179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302628149946806814018905 3976971112460105110514179)
                  ·
                    refine ⟨5965456668690157665771269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3976971112460105110514179 5965456668690157665771269)
                    ·
                      refine ⟨1118523125379404562332113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5965456668690157665771269 1118523125379404562332113)
                      ·
                        rfl

theorem cell23_2178316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2178316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178316 prefixEnd_2178316 := by exact prefixLift 2178316
  have htrace : WordTrace (prefixWord ++ tailWord_2178316) baseStart_2178316 baseEnd_2178316 := by
    simpa [prefixWord, tailWord_2178316, baseEnd_2178316] using wordTrace_append hprefix tailTrace_2178316
  have hstable : (prefixWord ++ tailWord_2178316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178316).length < 2 ^ (prefixWord ++ tailWord_2178316).sum := by decide
  have hdescent : baseEnd_2178316 < baseStart_2178316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178319 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_2178319 : Nat := 118140960795 + 2178319 * 2 ^ 59
def prefixEnd_2178319 : Nat := 4983230072969 + 3 ^ 40 * 2178319 * 2
def baseEnd_2178319 : Nat := 1118524665821368050594599

theorem tailTrace_2178319 : CollatzResearch.WordTrace tailWord_2178319 prefixEnd_2178319 1118524665821368050594599 := by
  unfold tailWord_2178319
  simp only [CollatzResearch.WordTrace]
  refine ⟨79449820995329765111706011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52966547330219843407804007 79449820995329765111706011)
  ·
    refine ⟨119174731492994647667559017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79449820995329765111706011 119174731492994647667559017)
    ·
      refine ⟨89381048619745985750669263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119174731492994647667559017 89381048619745985750669263)
      ·
        refine ⟨134071572929618978626003895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89381048619745985750669263 134071572929618978626003895)
        ·
          refine ⟨201107359394428467939005843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134071572929618978626003895 201107359394428467939005843)
          ·
            refine ⟨301661039091642701908508765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201107359394428467939005843 301661039091642701908508765)
            ·
              refine ⟨113122889659366013215690787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301661039091642701908508765 113122889659366013215690787)
              ·
                refine ⟨169684334489049019823536181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113122889659366013215690787 169684334489049019823536181)
                ·
                  refine ⟨15907906358348345608456517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169684334489049019823536181 15907906358348345608456517)
                  ·
                    refine ⟨2982732442190314801585597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15907906358348345608456517 2982732442190314801585597)
                    ·
                      refine ⟨1118524665821368050594599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982732442190314801585597 1118524665821368050594599)
                      ·
                        rfl

theorem cell23_2178319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_2178319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178319 prefixEnd_2178319 := by exact prefixLift 2178319
  have htrace : WordTrace (prefixWord ++ tailWord_2178319) baseStart_2178319 baseEnd_2178319 := by
    simpa [prefixWord, tailWord_2178319, baseEnd_2178319] using wordTrace_append hprefix tailTrace_2178319
  have hstable : (prefixWord ++ tailWord_2178319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178319).length < 2 ^ (prefixWord ++ tailWord_2178319).sum := by decide
  have hdescent : baseEnd_2178319 < baseStart_2178319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178333 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2178333 : Nat := 118140960795 + 2178333 * 2 ^ 59
def prefixEnd_2178333 : Nat := 4983230072969 + 3 ^ 40 * 2178333 * 2
def baseEnd_2178333 : Nat := 1118531854550530995819535

theorem tailTrace_2178333 : CollatzResearch.WordTrace tailWord_2178333 prefixEnd_2178333 1118531854550530995819535 := by
  unfold tailWord_2178333
  simp only [CollatzResearch.WordTrace]
  refine ⟨79450331617279045502715653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52966887744852697001810435 79450331617279045502715653)
  ·
    refine ⟨14896937178239821031759185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79450331617279045502715653 14896937178239821031759185)
    ·
      refine ⟨11172702883679865773819389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14896937178239821031759185 11172702883679865773819389)
      ·
        refine ⟨4189763581379949665182271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11172702883679865773819389 4189763581379949665182271)
        ·
          refine ⟨6284645372069924497773407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189763581379949665182271 6284645372069924497773407)
          ·
            refine ⟨9426968058104886746660111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284645372069924497773407 9426968058104886746660111)
            ·
              refine ⟨14140452087157330119990167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9426968058104886746660111 14140452087157330119990167)
              ·
                refine ⟨21210678130735995179985251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14140452087157330119990167 21210678130735995179985251)
                ·
                  refine ⟨31816017196103992769977877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21210678130735995179985251 31816017196103992769977877)
                  ·
                    refine ⟨1491375806067374661092713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31816017196103992769977877 1491375806067374661092713)
                    ·
                      refine ⟨1118531854550530995819535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491375806067374661092713 1118531854550530995819535)
                      ·
                        rfl

theorem cell23_2178333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2178333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178333 prefixEnd_2178333 := by exact prefixLift 2178333
  have htrace : WordTrace (prefixWord ++ tailWord_2178333) baseStart_2178333 baseEnd_2178333 := by
    simpa [prefixWord, tailWord_2178333, baseEnd_2178333] using wordTrace_append hprefix tailTrace_2178333
  have hstable : (prefixWord ++ tailWord_2178333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178333).length < 2 ^ (prefixWord ++ tailWord_2178333).sum := by decide
  have hdescent : baseEnd_2178333 < baseStart_2178333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178353 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2178353 : Nat := 118140960795 + 2178353 * 2 ^ 59
def prefixEnd_2178353 : Nat := 4983230072969 + 3 ^ 40 * 2178353 * 2
def baseEnd_2178353 : Nat := 1118542124163620917569443

theorem tailTrace_2178353 : CollatzResearch.WordTrace tailWord_2178353 prefixEnd_2178353 1118542124163620917569443 := by
  unfold tailWord_2178353
  simp only [CollatzResearch.WordTrace]
  refine ⟨79451061077206588918443713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52967374051471059278962475 79451061077206588918443713)
  ·
    refine ⟨59588295807904941688832785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79451061077206588918443713 59588295807904941688832785)
    ·
      refine ⟨44691221855928706266624589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59588295807904941688832785 44691221855928706266624589)
      ·
        refine ⟨16759208195973264849984221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44691221855928706266624589 16759208195973264849984221)
        ·
          refine ⟨6284703073489974318744083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16759208195973264849984221 6284703073489974318744083)
          ·
            refine ⟨9427054610234961478116125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284703073489974318744083 9427054610234961478116125)
            ·
              refine ⟨3535145478838110554293547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9427054610234961478116125 3535145478838110554293547)
              ·
                refine ⟨5302718218257165831440321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535145478838110554293547 5302718218257165831440321)
                ·
                  refine ⟨3977038663692874373580241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302718218257165831440321 3977038663692874373580241)
                  ·
                    refine ⟨2982778997769655780185181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977038663692874373580241 2982778997769655780185181)
                    ·
                      refine ⟨1118542124163620917569443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982778997769655780185181 1118542124163620917569443)
                      ·
                        rfl

theorem cell23_2178353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2178353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178353 prefixEnd_2178353 := by exact prefixLift 2178353
  have htrace : WordTrace (prefixWord ++ tailWord_2178353) baseStart_2178353 baseEnd_2178353 := by
    simpa [prefixWord, tailWord_2178353, baseEnd_2178353] using wordTrace_append hprefix tailTrace_2178353
  have hstable : (prefixWord ++ tailWord_2178353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178353).length < 2 ^ (prefixWord ++ tailWord_2178353).sum := by decide
  have hdescent : baseEnd_2178353 < baseStart_2178353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178356 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2178356 : Nat := 118140960795 + 2178356 * 2 ^ 59
def prefixEnd_2178356 : Nat := 4983230072969 + 3 ^ 40 * 2178356 * 2
def baseEnd_2178356 : Nat := 124282629400620489536881

theorem tailTrace_2178356 : CollatzResearch.WordTrace tailWord_2178356 prefixEnd_2178356 124282629400620489536881 := by
  unfold tailWord_2178356
  simp only [CollatzResearch.WordTrace]
  refine ⟨39725585248097860215401461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52967446997463813620535281 39725585248097860215401461)
  ·
    refine ⟨3724273617009174395193887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39725585248097860215401461 3724273617009174395193887)
    ·
      refine ⟨5586410425513761592790831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724273617009174395193887 5586410425513761592790831)
      ·
        refine ⟨8379615638270642389186247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586410425513761592790831 8379615638270642389186247)
        ·
          refine ⟨12569423457405963583779371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379615638270642389186247 12569423457405963583779371)
          ·
            refine ⟨18854135186108945375669057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12569423457405963583779371 18854135186108945375669057)
            ·
              refine ⟨14140601389581709031751793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18854135186108945375669057 14140601389581709031751793)
              ·
                refine ⟨10605451042186281773813845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14140601389581709031751793 10605451042186281773813845)
                ·
                  refine ⟨124282629400620489536881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10605451042186281773813845 124282629400620489536881)
                  ·
                    rfl

theorem cell23_2178356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2178356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178356 prefixEnd_2178356 := by exact prefixLift 2178356
  have htrace : WordTrace (prefixWord ++ tailWord_2178356) baseStart_2178356 baseEnd_2178356 := by
    simpa [prefixWord, tailWord_2178356, baseEnd_2178356] using wordTrace_append hprefix tailTrace_2178356
  have hstable : (prefixWord ++ tailWord_2178356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178356).length < 2 ^ (prefixWord ++ tailWord_2178356).sum := by decide
  have hdescent : baseEnd_2178356 < baseStart_2178356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178403 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 1, 5]
def baseStart_2178403 : Nat := 118140960795 + 2178403 * 2 ^ 59
def prefixEnd_2178403 : Nat := 4983230072969 + 3 ^ 40 * 2178403 * 2
def baseEnd_2178403 : Nat := 372855932732115240648071

theorem tailTrace_2178403 : CollatzResearch.WordTrace tailWord_2178403 prefixEnd_2178403 372855932732115240648071 := by
  unfold tailWord_2178403
  simp only [CollatzResearch.WordTrace]
  refine ⟨79452884727025447457763863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52968589818016964971842575 79452884727025447457763863)
  ·
    refine ⟨119179327090538171186645795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79452884727025447457763863 119179327090538171186645795)
    ·
      refine ⟨178768990635807256779968693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119179327090538171186645795 178768990635807256779968693)
      ·
        refine ⟨16759592872106930323122065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178768990635807256779968693 16759592872106930323122065)
        ·
          refine ⟨12569694654080197742341549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16759592872106930323122065 12569694654080197742341549)
          ·
            refine ⟨4713635495280074153378081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12569694654080197742341549 4713635495280074153378081)
            ·
              refine ⟨3535226621460055615033561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4713635495280074153378081 3535226621460055615033561)
              ·
                refine ⟨2651419966095041711275171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535226621460055615033561 2651419966095041711275171)
                ·
                  refine ⟨3977129949142562566912757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651419966095041711275171 3977129949142562566912757)
                  ·
                    refine ⟨372855932732115240648071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3977129949142562566912757 372855932732115240648071)
                    ·
                      rfl

theorem cell23_2178403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 5].length) (baseStart_2178403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178403 prefixEnd_2178403 := by exact prefixLift 2178403
  have htrace : WordTrace (prefixWord ++ tailWord_2178403) baseStart_2178403 baseEnd_2178403 := by
    simpa [prefixWord, tailWord_2178403, baseEnd_2178403] using wordTrace_append hprefix tailTrace_2178403
  have hstable : (prefixWord ++ tailWord_2178403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178403).length < 2 ^ (prefixWord ++ tailWord_2178403).sum := by decide
  have hdescent : baseEnd_2178403 < baseStart_2178403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178416 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_2178416 : Nat := 118140960795 + 2178416 * 2 ^ 59
def prefixEnd_2178416 : Nat := 4983230072969 + 3 ^ 40 * 2178416 * 2
def baseEnd_2178416 : Nat := 372858157814951390360551

theorem tailTrace_2178416 : CollatzResearch.WordTrace tailWord_2178416 prefixEnd_2178416 372858157814951390360551 := by
  unfold tailWord_2178416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39726679437989175338993551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52968905917318900451991401 39726679437989175338993551)
  ·
    refine ⟨59590019156983763008490327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39726679437989175338993551 59590019156983763008490327)
    ·
      refine ⟨89385028735475644512735491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59590019156983763008490327 89385028735475644512735491)
      ·
        refine ⟨134077543103213466769103237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89385028735475644512735491 134077543103213466769103237)
        ·
          refine ⟨25139539331852525019206857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134077543103213466769103237 25139539331852525019206857)
          ·
            refine ⟨18854654498889393764405143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25139539331852525019206857 18854654498889393764405143)
            ·
              refine ⟨28281981748334090646607715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18854654498889393764405143 28281981748334090646607715)
              ·
                refine ⟨42422972622501135969911573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28281981748334090646607715 42422972622501135969911573)
                ·
                  refine ⟨1988576841679740748589605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42422972622501135969911573 1988576841679740748589605)
                  ·
                    refine ⟨372858157814951390360551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988576841679740748589605 372858157814951390360551)
                    ·
                      rfl

theorem cell23_2178416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_2178416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178416 prefixEnd_2178416 := by exact prefixLift 2178416
  have htrace : WordTrace (prefixWord ++ tailWord_2178416) baseStart_2178416 baseEnd_2178416 := by
    simpa [prefixWord, tailWord_2178416, baseEnd_2178416] using wordTrace_append hprefix tailTrace_2178416
  have hstable : (prefixWord ++ tailWord_2178416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178416).length < 2 ^ (prefixWord ++ tailWord_2178416).sum := by decide
  have hdescent : baseEnd_2178416 < baseStart_2178416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178419 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_2178419 : Nat := 118140960795 + 2178419 * 2 ^ 59
def prefixEnd_2178419 : Nat := 4983230072969 + 3 ^ 40 * 2178419 * 2
def baseEnd_2178419 : Nat := 1118576013886817659344139

theorem tailTrace_2178419 : CollatzResearch.WordTrace tailWord_2178419 prefixEnd_2178419 1118576013886817659344139 := by
  unfold tailWord_2178419
  simp only [CollatzResearch.WordTrace]
  refine ⟨79453468294967482190346311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52968978863311654793564207 79453468294967482190346311)
  ·
    refine ⟨119180202442451223285519467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79453468294967482190346311 119180202442451223285519467)
    ·
      refine ⟨178770303663676834928279201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119180202442451223285519467 178770303663676834928279201)
      ·
        refine ⟨134077727747757626196209401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178770303663676834928279201 134077727747757626196209401)
        ·
          refine ⟨100558295810818219647157051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134077727747757626196209401 100558295810818219647157051)
          ·
            refine ⟨150837443716227329470735577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100558295810818219647157051 150837443716227329470735577)
            ·
              refine ⟨113128082787170497103051683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150837443716227329470735577 113128082787170497103051683)
              ·
                refine ⟨169692124180755745654577525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113128082787170497103051683 169692124180755745654577525)
                ·
                  refine ⟨15908636641945851155116643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169692124180755745654577525 15908636641945851155116643)
                  ·
                    refine ⟨23862954962918776732674965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15908636641945851155116643 23862954962918776732674965)
                    ·
                      refine ⟨1118576013886817659344139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23862954962918776732674965 1118576013886817659344139)
                      ·
                        rfl

theorem cell23_2178419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_2178419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178419 prefixEnd_2178419 := by exact prefixLift 2178419
  have htrace : WordTrace (prefixWord ++ tailWord_2178419) baseStart_2178419 baseEnd_2178419 := by
    simpa [prefixWord, tailWord_2178419, baseEnd_2178419] using wordTrace_append hprefix tailTrace_2178419
  have hstable : (prefixWord ++ tailWord_2178419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178419).length < 2 ^ (prefixWord ++ tailWord_2178419).sum := by decide
  have hdescent : baseEnd_2178419 < baseStart_2178419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178434 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2178434 : Nat := 118140960795 + 2178434 * 2 ^ 59
def prefixEnd_2178434 : Nat := 4983230072969 + 3 ^ 40 * 2178434 * 2
def baseEnd_2178434 : Nat := 1118583716096635100656571

theorem tailTrace_2178434 : CollatzResearch.WordTrace tailWord_2178434 prefixEnd_2178434 1118583716096635100656571 := by
  unfold tailWord_2178434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19863503847478284938035589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52969343593275426501428237 19863503847478284938035589)
  ·
    refine ⟨3724406971402178425881673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19863503847478284938035589 3724406971402178425881673)
    ·
      refine ⟨2793305228551633819411255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3724406971402178425881673 2793305228551633819411255)
      ·
        refine ⟨4189957842827450729116883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793305228551633819411255 4189957842827450729116883)
        ·
          refine ⟨6284936764241176093675325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189957842827450729116883 6284936764241176093675325)
          ·
            refine ⟨2356851286590441035128247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6284936764241176093675325 2356851286590441035128247)
            ·
              refine ⟨3535276929885661552692371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356851286590441035128247 3535276929885661552692371)
              ·
                refine ⟨5302915394828492329038557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535276929885661552692371 5302915394828492329038557)
                ·
                  refine ⟨1988593273060684623389459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5302915394828492329038557 1988593273060684623389459)
                  ·
                    refine ⟨2982889909591026935084189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988593273060684623389459 2982889909591026935084189)
                    ·
                      refine ⟨1118583716096635100656571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2982889909591026935084189 1118583716096635100656571)
                      ·
                        rfl

theorem cell23_2178434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2178434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178434 prefixEnd_2178434 := by exact prefixLift 2178434
  have htrace : WordTrace (prefixWord ++ tailWord_2178434) baseStart_2178434 baseEnd_2178434 := by
    simpa [prefixWord, tailWord_2178434, baseEnd_2178434] using wordTrace_append hprefix tailTrace_2178434
  have hstable : (prefixWord ++ tailWord_2178434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178434).length < 2 ^ (prefixWord ++ tailWord_2178434).sum := by decide
  have hdescent : baseEnd_2178434 < baseStart_2178434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178436 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2178436 : Nat := 118140960795 + 2178436 * 2 ^ 59
def prefixEnd_2178436 : Nat := 4983230072969 + 3 ^ 40 * 2178436 * 2
def baseEnd_2178436 : Nat := 1118584743057944092831561

theorem tailTrace_2178436 : CollatzResearch.WordTrace tailWord_2178436 prefixEnd_2178436 1118584743057944092831561 := by
  unfold tailWord_2178436
  simp only [CollatzResearch.WordTrace]
  refine ⟨39727044167952947046857581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52969392223937262729143441 39727044167952947046857581)
  ·
    refine ⟨14897641562982355142571593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39727044167952947046857581 14897641562982355142571593)
    ·
      refine ⟨11173231172236766356928695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14897641562982355142571593 11173231172236766356928695)
      ·
        refine ⟨16759846758355149535393043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173231172236766356928695 16759846758355149535393043)
        ·
          refine ⟨25139770137532724303089565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16759846758355149535393043 25139770137532724303089565)
          ·
            refine ⟨9427413801574771613658587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25139770137532724303089565 9427413801574771613658587)
            ·
              refine ⟨14141120702362157420487881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9427413801574771613658587 14141120702362157420487881)
              ·
                refine ⟨10605840526771618065365911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14141120702362157420487881 10605840526771618065365911)
                ·
                  refine ⟨15908760790157427098048867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605840526771618065365911 15908760790157427098048867)
                  ·
                    refine ⟨23863141185236140647073301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15908760790157427098048867 23863141185236140647073301)
                    ·
                      refine ⟨1118584743057944092831561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23863141185236140647073301 1118584743057944092831561)
                      ·
                        rfl

theorem cell23_2178436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2178436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178436 prefixEnd_2178436 := by exact prefixLift 2178436
  have htrace : WordTrace (prefixWord ++ tailWord_2178436) baseStart_2178436 baseEnd_2178436 := by
    simpa [prefixWord, tailWord_2178436, baseEnd_2178436] using wordTrace_append hprefix tailTrace_2178436
  have hstable : (prefixWord ++ tailWord_2178436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178436).length < 2 ^ (prefixWord ++ tailWord_2178436).sum := by decide
  have hdescent : baseEnd_2178436 < baseStart_2178436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178459 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 9]
def baseStart_2178459 : Nat := 118140960795 + 2178459 * 2 ^ 59
def prefixEnd_2178459 : Nat := 4983230072969 + 3 ^ 40 * 2178459 * 2
def baseEnd_2178459 : Nat := 372865517704332500947985

theorem tailTrace_2178459 : CollatzResearch.WordTrace tailWord_2178459 prefixEnd_2178459 372865517704332500947985 := by
  unfold tailWord_2178459
  simp only [CollatzResearch.WordTrace]
  refine ⟨79454927214822569021802431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52969951476548379347868287 79454927214822569021802431)
  ·
    refine ⟨119182390822233853532703647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79454927214822569021802431 119182390822233853532703647)
    ·
      refine ⟨178773586233350780299055471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119182390822233853532703647 178773586233350780299055471)
      ·
        refine ⟨268160379350026170448583207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178773586233350780299055471 268160379350026170448583207)
        ·
          refine ⟨402240569025039255672874811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268160379350026170448583207 402240569025039255672874811)
          ·
            refine ⟨603360853537558883509312217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402240569025039255672874811 603360853537558883509312217)
            ·
              refine ⟨452520640153169162631984163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603360853537558883509312217 452520640153169162631984163)
              ·
                refine ⟨678780960229753743947976245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452520640153169162631984163 678780960229753743947976245)
                ·
                  refine ⟨63635715021539413495122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678780960229753743947976245 63635715021539413495122773)
                  ·
                    refine ⟨372865517704332500947985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63635715021539413495122773 372865517704332500947985)
                    ·
                      rfl

theorem cell23_2178459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_2178459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178459 prefixEnd_2178459 := by exact prefixLift 2178459
  have htrace : WordTrace (prefixWord ++ tailWord_2178459) baseStart_2178459 baseEnd_2178459 := by
    simpa [prefixWord, tailWord_2178459, baseEnd_2178459] using wordTrace_append hprefix tailTrace_2178459
  have hstable : (prefixWord ++ tailWord_2178459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178459).length < 2 ^ (prefixWord ++ tailWord_2178459).sum := by decide
  have hdescent : baseEnd_2178459 < baseStart_2178459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178496 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_2178496 : Nat := 118140960795 + 2178496 * 2 ^ 59
def prefixEnd_2178496 : Nat := 4983230072969 + 3 ^ 40 * 2178496 * 2
def baseEnd_2178496 : Nat := 1118615551897213858081285

theorem tailTrace_2178496 : CollatzResearch.WordTrace tailWord_2178496 prefixEnd_2178496 1118615551897213858081285 := by
  unfold tailWord_2178496
  simp only [CollatzResearch.WordTrace]
  refine ⟨39728138357844262170449671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52970851143792349560599561 39728138357844262170449671)
  ·
    refine ⟨59592207536766393255674507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39728138357844262170449671 59592207536766393255674507)
    ·
      refine ⟨89388311305149589883511761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59592207536766393255674507 89388311305149589883511761)
      ·
        refine ⟨67041233478862192412633821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89388311305149589883511761 67041233478862192412633821)
        ·
          refine ⟨25140462554573322154737683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67041233478862192412633821 25140462554573322154737683)
          ·
            refine ⟨37710693831859983232106525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25140462554573322154737683 37710693831859983232106525)
            ·
              refine ⟨14141510186947493712039947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37710693831859983232106525 14141510186947493712039947)
              ·
                refine ⟨21212265280421240568059921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14141510186947493712039947 21212265280421240568059921)
                ·
                  refine ⟨15909198960315930426044941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21212265280421240568059921 15909198960315930426044941)
                  ·
                    refine ⟨5965949610118473909766853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15909198960315930426044941 5965949610118473909766853)
                    ·
                      refine ⟨1118615551897213858081285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5965949610118473909766853 1118615551897213858081285)
                      ·
                        rfl

theorem cell23_2178496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_2178496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178496 prefixEnd_2178496 := by exact prefixLift 2178496
  have htrace : WordTrace (prefixWord ++ tailWord_2178496) baseStart_2178496 baseEnd_2178496 := by
    simpa [prefixWord, tailWord_2178496, baseEnd_2178496] using wordTrace_append hprefix tailTrace_2178496
  have hstable : (prefixWord ++ tailWord_2178496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178496).length < 2 ^ (prefixWord ++ tailWord_2178496).sum := by decide
  have hdescent : baseEnd_2178496 < baseStart_2178496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178506 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_2178506 : Nat := 118140960795 + 2178506 * 2 ^ 59
def prefixEnd_2178506 : Nat := 4983230072969 + 3 ^ 40 * 2178506 * 2
def baseEnd_2178506 : Nat := 372873562234586272985413

theorem tailTrace_2178506 : CollatzResearch.WordTrace tailWord_2178506 prefixEnd_2178506 372873562234586272985413 := by
  unfold tailWord_2178506
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864160361413074012190843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52971094297101530699175581 19864160361413074012190843)
  ·
    refine ⟨29796240542119611018286265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19864160361413074012190843 29796240542119611018286265)
    ·
      refine ⟨22347180406589708263714699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29796240542119611018286265 22347180406589708263714699)
      ·
        refine ⟨33520770609884562395572049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22347180406589708263714699 33520770609884562395572049)
        ·
          refine ⟨25140577957413421796679037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33520770609884562395572049 25140577957413421796679037)
          ·
            refine ⟨9427716734030033173754639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25140577957413421796679037 9427716734030033173754639)
            ·
              refine ⟨14141575101045049760631959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9427716734030033173754639 14141575101045049760631959)
              ·
                refine ⟨21212362651567574640947939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14141575101045049760631959 21212362651567574640947939)
                ·
                  refine ⟨31818543977351361961421909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21212362651567574640947939 31818543977351361961421909)
                  ·
                    refine ⟨372873562234586272985413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31818543977351361961421909 372873562234586272985413)
                    ·
                      rfl

theorem cell23_2178506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_2178506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178506 prefixEnd_2178506 := by exact prefixLift 2178506
  have htrace : WordTrace (prefixWord ++ tailWord_2178506) baseStart_2178506 baseEnd_2178506 := by
    simpa [prefixWord, tailWord_2178506, baseEnd_2178506] using wordTrace_append hprefix tailTrace_2178506
  have hstable : (prefixWord ++ tailWord_2178506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178506).length < 2 ^ (prefixWord ++ tailWord_2178506).sum := by decide
  have hdescent : baseEnd_2178506 < baseStart_2178506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178536 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 9]
def baseStart_2178536 : Nat := 118140960795 + 2178536 * 2 ^ 59
def prefixEnd_2178536 : Nat := 4983230072969 + 3 ^ 40 * 2178536 * 2
def baseEnd_2178536 : Nat := 124292899013710411286789

theorem tailTrace_2178536 : CollatzResearch.WordTrace tailWord_2178536 prefixEnd_2178536 124292899013710411286789 := by
  unfold tailWord_2178536
  simp only [CollatzResearch.WordTrace]
  refine ⟨39728867817771805586177731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52971823757029074114903641 39728867817771805586177731)
  ·
    refine ⟨59593301726657708379266597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39728867817771805586177731 59593301726657708379266597)
    ·
      refine ⟨11173744073748320321112487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59593301726657708379266597 11173744073748320321112487)
      ·
        refine ⟨16760616110622480481668731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173744073748320321112487 16760616110622480481668731)
        ·
          refine ⟨25140924165933720722503097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16760616110622480481668731 25140924165933720722503097)
          ·
            refine ⟨18855693124450290541877323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25140924165933720722503097 18855693124450290541877323)
            ·
              refine ⟨28283539686675435812815985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18855693124450290541877323 28283539686675435812815985)
              ·
                refine ⟨21212654765006576859611989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28283539686675435812815985 21212654765006576859611989)
                ·
                  refine ⟨124292899013710411286789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21212654765006576859611989 124292899013710411286789)
                  ·
                    rfl

theorem cell23_2178536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_2178536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178536 prefixEnd_2178536 := by exact prefixLift 2178536
  have htrace : WordTrace (prefixWord ++ tailWord_2178536) baseStart_2178536 baseEnd_2178536 := by
    simpa [prefixWord, tailWord_2178536, baseEnd_2178536] using wordTrace_append hprefix tailTrace_2178536
  have hstable : (prefixWord ++ tailWord_2178536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178536).length < 2 ^ (prefixWord ++ tailWord_2178536).sum := by decide
  have hdescent : baseEnd_2178536 < baseStart_2178536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178541 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2178541 : Nat := 118140960795 + 2178541 * 2 ^ 59
def prefixEnd_2178541 : Nat := 4983230072969 + 3 ^ 40 * 2178541 * 2
def baseEnd_2178541 : Nat := 1118638658526666182018579

theorem tailTrace_2178541 : CollatzResearch.WordTrace tailWord_2178541 prefixEnd_2178541 1118638658526666182018579 := by
  unfold tailWord_2178541
  simp only [CollatzResearch.WordTrace]
  refine ⟨79457918000525497026287477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52971945333683664684191651 79457918000525497026287477)
  ·
    refine ⟨7449179812549265346214451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79457918000525497026287477 7449179812549265346214451)
    ·
      refine ⟨11173769718823898019321677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449179812549265346214451 11173769718823898019321677)
      ·
        refine ⟨4190163644558961757245629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11173769718823898019321677 4190163644558961757245629)
        ·
          refine ⟨1571311366709610658967111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4190163644558961757245629 1571311366709610658967111)
          ·
            refine ⟨2356967050064415988450667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571311366709610658967111 2356967050064415988450667)
            ·
              refine ⟨3535450575096623982676001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356967050064415988450667 3535450575096623982676001)
              ·
                refine ⟨2651587931322467987007001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535450575096623982676001 2651587931322467987007001)
                ·
                  refine ⟨1988690948491850990255251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2651587931322467987007001 1988690948491850990255251)
                  ·
                    refine ⟨2983036422737776485382877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988690948491850990255251 2983036422737776485382877)
                    ·
                      refine ⟨1118638658526666182018579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2983036422737776485382877 1118638658526666182018579)
                      ·
                        rfl

theorem cell23_2178541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2178541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178541 prefixEnd_2178541 := by exact prefixLift 2178541
  have htrace : WordTrace (prefixWord ++ tailWord_2178541) baseStart_2178541 baseEnd_2178541 := by
    simpa [prefixWord, tailWord_2178541, baseEnd_2178541] using wordTrace_append hprefix tailTrace_2178541
  have hstable : (prefixWord ++ tailWord_2178541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178541).length < 2 ^ (prefixWord ++ tailWord_2178541).sum := by decide
  have hdescent : baseEnd_2178541 < baseStart_2178541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178564 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2178564 : Nat := 118140960795 + 2178564 * 2 ^ 59
def prefixEnd_2178564 : Nat := 4983230072969 + 3 ^ 40 * 2178564 * 2
def baseEnd_2178564 : Nat := 1118650468581719592030973

theorem tailTrace_2178564 : CollatzResearch.WordTrace tailWord_2178564 prefixEnd_2178564 1118650468581719592030973 := by
  unfold tailWord_2178564
  simp only [CollatzResearch.WordTrace]
  refine ⟨39729378439721085977187373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52972504586294781302916497 39729378439721085977187373)
  ·
    refine ⟨14898516914895407241445265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39729378439721085977187373 14898516914895407241445265)
    ·
      refine ⟨11173887686171555431083949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14898516914895407241445265 11173887686171555431083949)
      ·
        refine ⟨4190207882314333286656481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11173887686171555431083949 4190207882314333286656481)
        ·
          refine ⟨3142655911735749964992361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4190207882314333286656481 3142655911735749964992361)
          ·
            refine ⟨2356991933801812473744271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3142655911735749964992361 2356991933801812473744271)
            ·
              refine ⟨3535487900702718710616407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356991933801812473744271 3535487900702718710616407)
              ·
                refine ⟨5303231851054078065924611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535487900702718710616407 5303231851054078065924611)
                ·
                  refine ⟨7954847776581117098886917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5303231851054078065924611 7954847776581117098886917)
                  ·
                    refine ⟨1491533958108959456041297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7954847776581117098886917 1491533958108959456041297)
                    ·
                      refine ⟨1118650468581719592030973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491533958108959456041297 1118650468581719592030973)
                      ·
                        rfl

theorem cell23_2178564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2178564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178564 prefixEnd_2178564 := by exact prefixLift 2178564
  have htrace : WordTrace (prefixWord ++ tailWord_2178564) baseStart_2178564 baseEnd_2178564 := by
    simpa [prefixWord, tailWord_2178564, baseEnd_2178564] using wordTrace_append hprefix tailTrace_2178564
  have hstable : (prefixWord ++ tailWord_2178564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178564).length < 2 ^ (prefixWord ++ tailWord_2178564).sum := by decide
  have hdescent : baseEnd_2178564 < baseStart_2178564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178640 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_2178640 : Nat := 118140960795 + 2178640 * 2 ^ 59
def prefixEnd_2178640 : Nat := 4983230072969 + 3 ^ 40 * 2178640 * 2
def baseEnd_2178640 : Nat := 1118689493111461294680623

theorem tailTrace_2178640 : CollatzResearch.WordTrace tailWord_2178640 prefixEnd_2178640 1118689493111461294680623 := by
  unfold tailWord_2178640
  simp only [CollatzResearch.WordTrace]
  refine ⟨39730764413583418467070687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52974352551444557956094249 39730764413583418467070687)
  ·
    refine ⟨59596146620375127700606031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39730764413583418467070687 59596146620375127700606031)
    ·
      refine ⟨89394219930562691550909047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59596146620375127700606031 89394219930562691550909047)
      ·
        refine ⟨134091329895844037326363571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89394219930562691550909047 134091329895844037326363571)
        ·
          refine ⟨201136994843766055989545357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134091329895844037326363571 201136994843766055989545357)
          ·
            refine ⟨75426373066412270996079509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201136994843766055989545357 75426373066412270996079509)
            ·
              refine ⟨3535611237488075202941227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75426373066412270996079509 3535611237488075202941227)
              ·
                refine ⟨5303416856232112804411841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535611237488075202941227 5303416856232112804411841)
                ·
                  refine ⟨3977562642174084603308881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303416856232112804411841 3977562642174084603308881)
                  ·
                    refine ⟨2983171981630563452481661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3977562642174084603308881 2983171981630563452481661)
                    ·
                      refine ⟨1118689493111461294680623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2983171981630563452481661 1118689493111461294680623)
                      ·
                        rfl

theorem cell23_2178640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_2178640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178640 prefixEnd_2178640 := by exact prefixLift 2178640
  have htrace : WordTrace (prefixWord ++ tailWord_2178640) baseStart_2178640 baseEnd_2178640 := by
    simpa [prefixWord, tailWord_2178640, baseEnd_2178640] using wordTrace_append hprefix tailTrace_2178640
  have hstable : (prefixWord ++ tailWord_2178640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178640).length < 2 ^ (prefixWord ++ tailWord_2178640).sum := by decide
  have hdescent : baseEnd_2178640 < baseStart_2178640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178660 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 6]
def baseStart_2178660 : Nat := 118140960795 + 2178660 * 2 ^ 59
def prefixEnd_2178660 : Nat := 4983230072969 + 3 ^ 40 * 2178660 * 2
def baseEnd_2178660 : Nat := 124299973636061246270059

theorem tailTrace_2178660 : CollatzResearch.WordTrace tailWord_2178660 prefixEnd_2178660 124299973636061246270059 := by
  unfold tailWord_2178660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39731129143547190174934717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52974838858062920233246289 39731129143547190174934717)
  ·
    refine ⟨14899173428830196315600519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39731129143547190174934717 14899173428830196315600519)
    ·
      refine ⟨22348760143245294473400779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14899173428830196315600519 22348760143245294473400779)
      ·
        refine ⟨33523140214867941710101169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22348760143245294473400779 33523140214867941710101169)
        ·
          refine ⟨25142355161150956282575877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33523140214867941710101169 25142355161150956282575877)
          ·
            refine ⟨4714191592715804302982977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25142355161150956282575877 4714191592715804302982977)
            ·
              refine ⟨3535643694536853227237233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4714191592715804302982977 3535643694536853227237233)
              ·
                refine ⟨2651732770902639920427925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535643694536853227237233 2651732770902639920427925)
                ·
                  refine ⟨124299973636061246270059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2651732770902639920427925 124299973636061246270059)
                  ·
                    rfl

theorem cell23_2178660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_2178660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178660 prefixEnd_2178660 := by exact prefixLift 2178660
  have htrace : WordTrace (prefixWord ++ tailWord_2178660) baseStart_2178660 baseEnd_2178660 := by
    simpa [prefixWord, tailWord_2178660, baseEnd_2178660] using wordTrace_append hprefix tailTrace_2178660
  have hstable : (prefixWord ++ tailWord_2178660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178660).length < 2 ^ (prefixWord ++ tailWord_2178660).sum := by decide
  have hdescent : baseEnd_2178660 < baseStart_2178660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178664 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2178664 : Nat := 118140960795 + 2178664 * 2 ^ 59
def prefixEnd_2178664 : Nat := 4983230072969 + 3 ^ 40 * 2178664 * 2
def baseEnd_2178664 : Nat := 372900605549056400260171

theorem tailTrace_2178664 : CollatzResearch.WordTrace tailWord_2178664 prefixEnd_2178664 372900605549056400260171 := by
  unfold tailWord_2178664
  simp only [CollatzResearch.WordTrace]
  refine ⟨39731202089539944516507523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52974936119386592688676697 39731202089539944516507523)
  ·
    refine ⟨59596803134309916774761285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39731202089539944516507523 59596803134309916774761285)
    ·
      refine ⟨11174400587683109395267741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59596803134309916774761285 11174400587683109395267741)
      ·
        refine ⟨4190400220381166023225403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11174400587683109395267741 4190400220381166023225403)
        ·
          refine ⟨6285600330571749034838105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4190400220381166023225403 6285600330571749034838105)
          ·
            refine ⟨4714200247928811776128579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6285600330571749034838105 4714200247928811776128579)
            ·
              refine ⟨7071300371893217664192869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714200247928811776128579 7071300371893217664192869)
              ·
                refine ⟨1325868819729978312036163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7071300371893217664192869 1325868819729978312036163)
                ·
                  refine ⟨1988803229594967468054245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325868819729978312036163 1988803229594967468054245)
                  ·
                    refine ⟨372900605549056400260171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988803229594967468054245 372900605549056400260171)
                    ·
                      rfl

theorem cell23_2178664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2178664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178664 prefixEnd_2178664 := by exact prefixLift 2178664
  have htrace : WordTrace (prefixWord ++ tailWord_2178664) baseStart_2178664 baseEnd_2178664 := by
    simpa [prefixWord, tailWord_2178664, baseEnd_2178664] using wordTrace_append hprefix tailTrace_2178664
  have hstable : (prefixWord ++ tailWord_2178664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178664).length < 2 ^ (prefixWord ++ tailWord_2178664).sum := by decide
  have hdescent : baseEnd_2178664 < baseStart_2178664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178697 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 2, 3, 2]
def baseStart_2178697 : Nat := 118140960795 + 2178697 * 2 ^ 59
def prefixEnd_2178697 : Nat := 4983230072969 + 3 ^ 40 * 2178697 * 2
def baseEnd_2178697 : Nat := 1118718761508767571667861

theorem tailTrace_2178697 : CollatzResearch.WordTrace tailWord_2178697 prefixEnd_2178697 1118718761508767571667861 := by
  unfold tailWord_2178697
  simp only [CollatzResearch.WordTrace]
  refine ⟨79463607787960335668966345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52975738525306890445977563 79463607787960335668966345)
  ·
    refine ⟨59597705840970251751724759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79463607787960335668966345 59597705840970251751724759)
    ·
      refine ⟨89396558761455377627587139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59597705840970251751724759 89396558761455377627587139)
      ·
        refine ⟨134094838142183066441380709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89396558761455377627587139 134094838142183066441380709)
        ·
          refine ⟨25142782151659324957758883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134094838142183066441380709 25142782151659324957758883)
          ·
            refine ⟨37714173227488987436638325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25142782151659324957758883 37714173227488987436638325)
            ·
              refine ⟨3535703740077092572184843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37714173227488987436638325 3535703740077092572184843)
              ·
                refine ⟨5303555610115638858277265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535703740077092572184843 5303555610115638858277265)
                ·
                  refine ⟨3977666707586729143707949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303555610115638858277265 3977666707586729143707949)
                  ·
                    refine ⟨1491625015345023428890481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3977666707586729143707949 1491625015345023428890481)
                    ·
                      refine ⟨1118718761508767571667861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491625015345023428890481 1118718761508767571667861)
                      ·
                        rfl

theorem cell23_2178697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3, 2].length) (baseStart_2178697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178697 prefixEnd_2178697 := by exact prefixLift 2178697
  have htrace : WordTrace (prefixWord ++ tailWord_2178697) baseStart_2178697 baseEnd_2178697 := by
    simpa [prefixWord, tailWord_2178697, baseEnd_2178697] using wordTrace_append hprefix tailTrace_2178697
  have hstable : (prefixWord ++ tailWord_2178697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178697).length < 2 ^ (prefixWord ++ tailWord_2178697).sum := by decide
  have hdescent : baseEnd_2178697 < baseStart_2178697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178723 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2178723 : Nat := 118140960795 + 2178723 * 2 ^ 59
def prefixEnd_2178723 : Nat := 4983230072969 + 3 ^ 40 * 2178723 * 2
def baseEnd_2178723 : Nat := 1118732112005784469942741

theorem tailTrace_2178723 : CollatzResearch.WordTrace tailWord_2178723 prefixEnd_2178723 1118732112005784469942741 := by
  unfold tailWord_2178723
  simp only [CollatzResearch.WordTrace]
  refine ⟨79464556085866142109412823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52976370723910761406275215 79464556085866142109412823)
  ·
    refine ⟨119196834128799213164119235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79464556085866142109412823 119196834128799213164119235)
    ·
      refine ⟨178795251193198819746178853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119196834128799213164119235 178795251193198819746178853)
      ·
        refine ⟨33524109598724778702408535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178795251193198819746178853 33524109598724778702408535)
        ·
          refine ⟨50286164398087168053612803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33524109598724778702408535 50286164398087168053612803)
          ·
            refine ⟨75429246597130752080419205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50286164398087168053612803 75429246597130752080419205)
            ·
              refine ⟨14142983736962016015078601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75429246597130752080419205 14142983736962016015078601)
              ·
                refine ⟨10607237802721512011308951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14142983736962016015078601 10607237802721512011308951)
                ·
                  refine ⟨15910856704082268016963427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10607237802721512011308951 15910856704082268016963427)
                  ·
                    refine ⟨23866285056123402025445141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15910856704082268016963427 23866285056123402025445141)
                    ·
                      refine ⟨1118732112005784469942741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23866285056123402025445141 1118732112005784469942741)
                      ·
                        rfl

theorem cell23_2178723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2178723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178723 prefixEnd_2178723 := by exact prefixLift 2178723
  have htrace : WordTrace (prefixWord ++ tailWord_2178723) baseStart_2178723 baseEnd_2178723 := by
    simpa [prefixWord, tailWord_2178723, baseEnd_2178723] using wordTrace_append hprefix tailTrace_2178723
  have hstable : (prefixWord ++ tailWord_2178723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178723).length < 2 ^ (prefixWord ++ tailWord_2178723).sum := by decide
  have hdescent : baseEnd_2178723 < baseStart_2178723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178750 : List Nat := [4, 2, 1, 1, 2, 3, 1, 9]
def baseStart_2178750 : Nat := 118140960795 + 2178750 * 2 ^ 59
def prefixEnd_2178750 : Nat := 4983230072969 + 3 ^ 40 * 2178750 * 2
def baseEnd_2178750 : Nat := 41435036147535402381671

theorem tailTrace_2178750 : CollatzResearch.WordTrace tailWord_2178750 prefixEnd_2178750 41435036147535402381671 := by
  unfold tailWord_2178750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9933192607096040715080713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52977027237845550480430469 9933192607096040715080713)
  ·
    refine ⟨7449894455322030536310535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9933192607096040715080713 7449894455322030536310535)
    ·
      refine ⟨11174841682983045804465803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449894455322030536310535 11174841682983045804465803)
      ·
        refine ⟨16762262524474568706698705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11174841682983045804465803 16762262524474568706698705)
        ·
          refine ⟨12571696893355926530024029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16762262524474568706698705 12571696893355926530024029)
          ·
            refine ⟨4714386335008472448759011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12571696893355926530024029 4714386335008472448759011)
            ·
              refine ⟨7071579502512708673138517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714386335008472448759011 7071579502512708673138517)
              ·
                refine ⟨41435036147535402381671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7071579502512708673138517 41435036147535402381671)
                ·
                  rfl

theorem cell23_2178750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_2178750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178750 prefixEnd_2178750 := by exact prefixLift 2178750
  have htrace : WordTrace (prefixWord ++ tailWord_2178750) baseStart_2178750 baseEnd_2178750 := by
    simpa [prefixWord, tailWord_2178750, baseEnd_2178750] using wordTrace_append hprefix tailTrace_2178750
  have hstable : (prefixWord ++ tailWord_2178750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178750).length < 2 ^ (prefixWord ++ tailWord_2178750).sum := by decide
  have hdescent : baseEnd_2178750 < baseStart_2178750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178760 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_2178760 : Nat := 118140960795 + 2178760 * 2 ^ 59
def prefixEnd_2178760 : Nat := 4983230072969 + 3 ^ 40 * 2178760 * 2
def baseEnd_2178760 : Nat := 1118751110790000825180071

theorem tailTrace_2178760 : CollatzResearch.WordTrace tailWord_2178760 prefixEnd_2178760 1118751110790000825180071 := by
  unfold tailWord_2178760
  simp only [CollatzResearch.WordTrace]
  refine ⟨39732952793366048714254867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52977270391154731619006489 39732952793366048714254867)
  ·
    refine ⟨59599429190049073071382301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39732952793366048714254867 59599429190049073071382301)
    ·
      refine ⟨22349785946268402401768363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59599429190049073071382301 22349785946268402401768363)
      ·
        refine ⟨33524678919402603602652545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22349785946268402401768363 33524678919402603602652545)
        ·
          refine ⟨25143509189551952701989409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33524678919402603602652545 25143509189551952701989409)
          ·
            refine ⟨18857631892163964526492057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25143509189551952701989409 18857631892163964526492057)
            ·
              refine ⟨14143223919122973394869043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18857631892163964526492057 14143223919122973394869043)
              ·
                refine ⟨21214835878684460092303565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14143223919122973394869043 21214835878684460092303565)
                ·
                  refine ⟨7955563454506672534613837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21214835878684460092303565 7955563454506672534613837)
                  ·
                    refine ⟨2983336295440002200480189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7955563454506672534613837 2983336295440002200480189)
                    ·
                      refine ⟨1118751110790000825180071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2983336295440002200480189 1118751110790000825180071)
                      ·
                        rfl

theorem cell23_2178760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_2178760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178760 prefixEnd_2178760 := by exact prefixLift 2178760
  have htrace : WordTrace (prefixWord ++ tailWord_2178760) baseStart_2178760 baseEnd_2178760 := by
    simpa [prefixWord, tailWord_2178760, baseEnd_2178760] using wordTrace_append hprefix tailTrace_2178760
  have hstable : (prefixWord ++ tailWord_2178760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178760).length < 2 ^ (prefixWord ++ tailWord_2178760).sum := by decide
  have hdescent : baseEnd_2178760 < baseStart_2178760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178777 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 3]
def baseStart_2178777 : Nat := 118140960795 + 2178777 * 2 ^ 59
def prefixEnd_2178777 : Nat := 4983230072969 + 3 ^ 40 * 2178777 * 2
def baseEnd_2178777 : Nat := 1118759839961127258667493

theorem tailTrace_2178777 : CollatzResearch.WordTrace tailWord_2178777 prefixEnd_2178777 1118759839961127258667493 := by
  unfold tailWord_2178777
  simp only [CollatzResearch.WordTrace]
  refine ⟨79466525627670509331878585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52977683751780339554585723 79466525627670509331878585)
  ·
    refine ⟨59599894220752881998908939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79466525627670509331878585 59599894220752881998908939)
    ·
      refine ⟨89399841331129322998363409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59599894220752881998908939 89399841331129322998363409)
      ·
        refine ⟨67049880998346992248772557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89399841331129322998363409 67049880998346992248772557)
        ·
          refine ⟨25143705374380122093289709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67049880998346992248772557 25143705374380122093289709)
          ·
            refine ⟨9428889515392545784983641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25143705374380122093289709 9428889515392545784983641)
            ·
              refine ⟨7071667136544409338737731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9428889515392545784983641 7071667136544409338737731)
              ·
                refine ⟨10607500704816614008106597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7071667136544409338737731 10607500704816614008106597)
                ·
                  refine ⟨1988906382153115126519987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10607500704816614008106597 1988906382153115126519987)
                  ·
                    refine ⟨2983359573229672689779981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988906382153115126519987 2983359573229672689779981)
                    ·
                      refine ⟨1118759839961127258667493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2983359573229672689779981 1118759839961127258667493)
                      ·
                        rfl

theorem cell23_2178777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_2178777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178777 prefixEnd_2178777 := by exact prefixLift 2178777
  have htrace : WordTrace (prefixWord ++ tailWord_2178777) baseStart_2178777 baseEnd_2178777 := by
    simpa [prefixWord, tailWord_2178777, baseEnd_2178777] using wordTrace_append hprefix tailTrace_2178777
  have hstable : (prefixWord ++ tailWord_2178777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178777).length < 2 ^ (prefixWord ++ tailWord_2178777).sum := by decide
  have hdescent : baseEnd_2178777 < baseStart_2178777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178778 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2]
def baseStart_2178778 : Nat := 118140960795 + 2178778 * 2 ^ 59
def prefixEnd_2178778 : Nat := 4983230072969 + 3 ^ 40 * 2178778 * 2
def baseEnd_2178778 : Nat := 1118760353441781754754989

theorem tailTrace_2178778 : CollatzResearch.WordTrace tailWord_2178778 prefixEnd_2178778 1118760353441781754754989 := by
  unfold tailWord_2178778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19866640525166721625666247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52977708067111257668443325 19866640525166721625666247)
  ·
    refine ⟨29799960787750082438499371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19866640525166721625666247 29799960787750082438499371)
    ·
      refine ⟨44699941181625123657749057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29799960787750082438499371 44699941181625123657749057)
      ·
        refine ⟨33524955886218842743311793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44699941181625123657749057 33524955886218842743311793)
        ·
          refine ⟨25143716914664132057483845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33524955886218842743311793 25143716914664132057483845)
          ·
            refine ⟨4714446921499524760778221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25143716914664132057483845 4714446921499524760778221)
            ·
              refine ⟨1767917595562321785291833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4714446921499524760778221 1767917595562321785291833)
              ·
                refine ⟨1325938196671741338968875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767917595562321785291833 1325938196671741338968875)
                ·
                  refine ⟨1988907295007612008453313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325938196671741338968875 1988907295007612008453313)
                  ·
                    refine ⟨1491680471255709006339985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1988907295007612008453313 1491680471255709006339985)
                    ·
                      refine ⟨1118760353441781754754989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491680471255709006339985 1118760353441781754754989)
                      ·
                        rfl

theorem cell23_2178778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_2178778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178778 prefixEnd_2178778 := by exact prefixLift 2178778
  have htrace : WordTrace (prefixWord ++ tailWord_2178778) baseStart_2178778 baseEnd_2178778 := by
    simpa [prefixWord, tailWord_2178778, baseEnd_2178778] using wordTrace_append hprefix tailTrace_2178778
  have hstable : (prefixWord ++ tailWord_2178778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178778).length < 2 ^ (prefixWord ++ tailWord_2178778).sum := by decide
  have hdescent : baseEnd_2178778 < baseStart_2178778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178793 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_2178793 : Nat := 118140960795 + 2178793 * 2 ^ 59
def prefixEnd_2178793 : Nat := 4983230072969 + 3 ^ 40 * 2178793 * 2
def baseEnd_2178793 : Nat := 372922685217199732022473

theorem tailTrace_2178793 : CollatzResearch.WordTrace tailWord_2178793 prefixEnd_2178793 372922685217199732022473 := by
  unfold tailWord_2178793
  simp only [CollatzResearch.WordTrace]
  refine ⟨79467109195612544064461033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52978072797075029376307355 79467109195612544064461033)
  ·
    refine ⟨59600331896709408048345775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79467109195612544064461033 59600331896709408048345775)
    ·
      refine ⟨89400497845064112072518663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59600331896709408048345775 89400497845064112072518663)
      ·
        refine ⟨134100746767596168108777995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89400497845064112072518663 134100746767596168108777995)
        ·
          refine ⟨201151120151394252163166993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134100746767596168108777995 201151120151394252163166993)
          ·
            refine ⟨150863340113545689122375245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201151120151394252163166993 150863340113545689122375245)
            ·
              refine ⟨56573752542579633420890717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150863340113545689122375245 56573752542579633420890717)
              ·
                refine ⟨21215157203467362532834019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56573752542579633420890717 21215157203467362532834019)
                ·
                  refine ⟨31822735805201043799251029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21215157203467362532834019 31822735805201043799251029)
                  ·
                    refine ⟨372922685217199732022473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31822735805201043799251029 372922685217199732022473)
                    ·
                      rfl

theorem cell23_2178793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_2178793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178793 prefixEnd_2178793 := by exact prefixLift 2178793
  have htrace : WordTrace (prefixWord ++ tailWord_2178793) baseStart_2178793 baseEnd_2178793 := by
    simpa [prefixWord, tailWord_2178793, baseEnd_2178793] using wordTrace_append hprefix tailTrace_2178793
  have hstable : (prefixWord ++ tailWord_2178793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178793).length < 2 ^ (prefixWord ++ tailWord_2178793).sum := by decide
  have hdescent : baseEnd_2178793 < baseStart_2178793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178817 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_2178817 : Nat := 118140960795 + 2178817 * 2 ^ 59
def prefixEnd_2178817 : Nat := 4983230072969 + 3 ^ 40 * 2178817 * 2
def baseEnd_2178817 : Nat := 1118780379187307102167309

theorem tailTrace_2178817 : CollatzResearch.WordTrace tailWord_2178817 prefixEnd_2178817 1118780379187307102167309 := by
  unfold tailWord_2178817
  simp only [CollatzResearch.WordTrace]
  refine ⟨79467984547525596163334705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52978656365017064108889803 79467984547525596163334705)
  ·
    refine ⟨59600988410644197122501029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79467984547525596163334705 59600988410644197122501029)
    ·
      refine ⟨11175185326995786960468943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59600988410644197122501029 11175185326995786960468943)
      ·
        refine ⟨16762777990493680440703415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11175185326995786960468943 16762777990493680440703415)
        ·
          refine ⟨25144166985740520661055123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16762777990493680440703415 25144166985740520661055123)
          ·
            refine ⟨37716250478610780991582685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25144166985740520661055123 37716250478610780991582685)
            ·
              refine ⟨14143593929479042871843507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37716250478610780991582685 14143593929479042871843507)
              ·
                refine ⟨21215390894218564307765261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14143593929479042871843507 21215390894218564307765261)
                ·
                  refine ⟨7955771585331961615411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21215390894218564307765261 7955771585331961615411973)
                  ·
                    refine ⟨1491707172249742802889745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7955771585331961615411973 1491707172249742802889745)
                    ·
                      refine ⟨1118780379187307102167309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491707172249742802889745 1118780379187307102167309)
                      ·
                        rfl

theorem cell23_2178817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_2178817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178817 prefixEnd_2178817 := by exact prefixLift 2178817
  have htrace : WordTrace (prefixWord ++ tailWord_2178817) baseStart_2178817 baseEnd_2178817 := by
    simpa [prefixWord, tailWord_2178817, baseEnd_2178817] using wordTrace_append hprefix tailTrace_2178817
  have hstable : (prefixWord ++ tailWord_2178817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178817).length < 2 ^ (prefixWord ++ tailWord_2178817).sum := by decide
  have hdescent : baseEnd_2178817 < baseStart_2178817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178822 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2178822 : Nat := 118140960795 + 2178822 * 2 ^ 59
def prefixEnd_2178822 : Nat := 4983230072969 + 3 ^ 40 * 2178822 * 2
def baseEnd_2178822 : Nat := 372927648863526527534929

theorem tailTrace_2178822 : CollatzResearch.WordTrace tailWord_2178822 prefixEnd_2178822 372927648863526527534929 := by
  unfold tailWord_2178822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483380216015858813039585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52978777941671654678177813 2483380216015858813039585)
  ·
    refine ⟨1862535162011894109779689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2483380216015858813039585 1862535162011894109779689)
    ·
      refine ⟨1396901371508920582334767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862535162011894109779689 1396901371508920582334767)
      ·
        refine ⟨2095352057263380873502151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396901371508920582334767 2095352057263380873502151)
        ·
          refine ⟨3143028085895071310253227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095352057263380873502151 3143028085895071310253227)
          ·
            refine ⟨4714542128842606965379841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143028085895071310253227 4714542128842606965379841)
            ·
              refine ⟨3535906596631955224034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4714542128842606965379841 3535906596631955224034881)
              ·
                refine ⟨2651929947473966418026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535906596631955224034881 2651929947473966418026161)
                ·
                  refine ⟨1988947460605474813519621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2651929947473966418026161 1988947460605474813519621)
                  ·
                    refine ⟨372927648863526527534929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1988947460605474813519621 372927648863526527534929)
                    ·
                      rfl

theorem cell23_2178822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2178822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178822 prefixEnd_2178822 := by exact prefixLift 2178822
  have htrace : WordTrace (prefixWord ++ tailWord_2178822) baseStart_2178822 baseEnd_2178822 := by
    simpa [prefixWord, tailWord_2178822, baseEnd_2178822] using wordTrace_append hprefix tailTrace_2178822
  have hstable : (prefixWord ++ tailWord_2178822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178822).length < 2 ^ (prefixWord ++ tailWord_2178822).sum := by decide
  have hdescent : baseEnd_2178822 < baseStart_2178822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178829 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2178829 : Nat := 118140960795 + 2178829 * 2 ^ 59
def prefixEnd_2178829 : Nat := 4983230072969 + 3 ^ 40 * 2178829 * 2
def baseEnd_2178829 : Nat := 1118786540955161055217255

theorem tailTrace_2178829 : CollatzResearch.WordTrace tailWord_2178829 prefixEnd_2178829 1118786540955161055217255 := by
  unfold tailWord_2178829
  simp only [CollatzResearch.WordTrace]
  refine ⟨79468422223482122212771541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52978948148988081475181027 79468422223482122212771541)
  ·
    refine ⟨1862541145862862239361833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79468422223482122212771541 1862541145862862239361833)
    ·
      refine ⟨1396905859397146679521375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862541145862862239361833 1396905859397146679521375)
      ·
        refine ⟨2095358789095720019282063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396905859397146679521375 2095358789095720019282063)
        ·
          refine ⟨3143038183643580028923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095358789095720019282063 3143038183643580028923095)
          ·
            refine ⟨4714557275465370043384643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143038183643580028923095 4714557275465370043384643)
            ·
              refine ⟨7071835913198055065076965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714557275465370043384643 7071835913198055065076965)
              ·
                refine ⟨1325969233724635324701931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7071835913198055065076965 1325969233724635324701931)
                ·
                  refine ⟨1988953850586952987052897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325969233724635324701931 1988953850586952987052897)
                  ·
                    refine ⟨1491715387940214740289673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1988953850586952987052897 1491715387940214740289673)
                    ·
                      refine ⟨1118786540955161055217255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491715387940214740289673 1118786540955161055217255)
                      ·
                        rfl

theorem cell23_2178829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2178829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178829 prefixEnd_2178829 := by exact prefixLift 2178829
  have htrace : WordTrace (prefixWord ++ tailWord_2178829) baseStart_2178829 baseEnd_2178829 := by
    simpa [prefixWord, tailWord_2178829, baseEnd_2178829] using wordTrace_append hprefix tailTrace_2178829
  have hstable : (prefixWord ++ tailWord_2178829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178829).length < 2 ^ (prefixWord ++ tailWord_2178829).sum := by decide
  have hdescent : baseEnd_2178829 < baseStart_2178829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178874 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_2178874 : Nat := 118140960795 + 2178874 * 2 ^ 59
def prefixEnd_2178874 : Nat := 4983230072969 + 3 ^ 40 * 2178874 * 2
def baseEnd_2178874 : Nat := 124312183064957042128283

theorem tailTrace_2178874 : CollatzResearch.WordTrace tailWord_2178874 prefixEnd_2178874 124312183064957042128283 := by
  unfold tailWord_2178874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19867515877079773724539919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52980042338879396598773117 19867515877079773724539919)
  ·
    refine ⟨29801273815619660586809879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19867515877079773724539919 29801273815619660586809879)
    ·
      refine ⟨44701910723429490880214819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29801273815619660586809879 44701910723429490880214819)
      ·
        refine ⟨67052866085144236320322229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44701910723429490880214819 67052866085144236320322229)
        ·
          refine ⟨6286206195482272155030209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67052866085144236320322229 6286206195482272155030209)
          ·
            refine ⟨4714654646611704116272657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6286206195482272155030209 4714654646611704116272657)
            ·
              refine ⟨3535990984958778087204493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4714654646611704116272657 3535990984958778087204493)
              ·
                refine ⟨1325996619359541782701685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3535990984958778087204493 1325996619359541782701685)
                ·
                  refine ⟨124312183064957042128283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1325996619359541782701685 124312183064957042128283)
                  ·
                    rfl

theorem cell23_2178874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_2178874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178874 prefixEnd_2178874 := by exact prefixLift 2178874
  have htrace : WordTrace (prefixWord ++ tailWord_2178874) baseStart_2178874 baseEnd_2178874 := by
    simpa [prefixWord, tailWord_2178874, baseEnd_2178874] using wordTrace_append hprefix tailTrace_2178874
  have hstable : (prefixWord ++ tailWord_2178874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178874).length < 2 ^ (prefixWord ++ tailWord_2178874).sum := by decide
  have hdescent : baseEnd_2178874 < baseStart_2178874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178951 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2178951 : Nat := 118140960795 + 2178951 * 2 ^ 59
def prefixEnd_2178951 : Nat := 4983230072969 + 3 ^ 40 * 2178951 * 2
def baseEnd_2178951 : Nat := 372949728531669859297231

theorem tailTrace_2178951 : CollatzResearch.WordTrace tailWord_2178951 prefixEnd_2178951 372949728531669859297231 := by
  unfold tailWord_2178951
  simp only [CollatzResearch.WordTrace]
  refine ⟨79472871929040137048712707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52981914619360091365808471 79472871929040137048712707)
  ·
    refine ⟨119209307893560205573069061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79472871929040137048712707 119209307893560205573069061)
    ·
      refine ⟨22351745230042538544950449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119209307893560205573069061 22351745230042538544950449)
      ·
        refine ⟨16763808922531903908712837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22351745230042538544950449 16763808922531903908712837)
        ·
          refine ⟨3143214172974731982883657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16763808922531903908712837 3143214172974731982883657)
          ·
            refine ⟨2357410629731048987162743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3143214172974731982883657 2357410629731048987162743)
            ·
              refine ⟨3536115944596573480744115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357410629731048987162743 3536115944596573480744115)
              ·
                refine ⟨5304173916894860221116173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536115944596573480744115 5304173916894860221116173)
                ·
                  refine ⟨1989065218835572582918565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5304173916894860221116173 1989065218835572582918565)
                  ·
                    refine ⟨372949728531669859297231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1989065218835572582918565 372949728531669859297231)
                    ·
                      rfl

theorem cell23_2178951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2178951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178951 prefixEnd_2178951 := by exact prefixLift 2178951
  have htrace : WordTrace (prefixWord ++ tailWord_2178951) baseStart_2178951 baseEnd_2178951 := by
    simpa [prefixWord, tailWord_2178951, baseEnd_2178951] using wordTrace_append hprefix tailTrace_2178951
  have hstable : (prefixWord ++ tailWord_2178951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178951).length < 2 ^ (prefixWord ++ tailWord_2178951).sum := by decide
  have hdescent : baseEnd_2178951 < baseStart_2178951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178964 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 6]
def baseStart_2178964 : Nat := 118140960795 + 2178964 * 2 ^ 59
def prefixEnd_2178964 : Nat := 4983230072969 + 3 ^ 40 * 2178964 * 2
def baseEnd_2178964 : Nat := 124317317871502003003237

theorem tailTrace_2178964 : CollatzResearch.WordTrace tailWord_2178964 prefixEnd_2178964 124317317871502003003237 := by
  unfold tailWord_2178964
  simp only [CollatzResearch.WordTrace]
  refine ⟨39736673038996520134467973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52982230718662026845957297 39736673038996520134467973)
  ·
    refine ⟨7450626194811847525212745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39736673038996520134467973 7450626194811847525212745)
    ·
      refine ⟨5587969646108885643909559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7450626194811847525212745 5587969646108885643909559)
      ·
        refine ⟨8381954469163328465864339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5587969646108885643909559 8381954469163328465864339)
        ·
          refine ⟨12572931703744992698796509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8381954469163328465864339 12572931703744992698796509)
          ·
            refine ⟨4714849388904372262048691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12572931703744992698796509 4714849388904372262048691)
            ·
              refine ⟨7072274083356558393073037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714849388904372262048691 7072274083356558393073037)
              ·
                refine ⟨2652102781258709397402389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7072274083356558393073037 2652102781258709397402389)
                ·
                  refine ⟨124317317871502003003237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2652102781258709397402389 124317317871502003003237)
                  ·
                    rfl

theorem cell23_2178964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_2178964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178964 prefixEnd_2178964 := by exact prefixLift 2178964
  have htrace : WordTrace (prefixWord ++ tailWord_2178964) baseStart_2178964 baseEnd_2178964 := by
    simpa [prefixWord, tailWord_2178964, baseEnd_2178964] using wordTrace_append hprefix tailTrace_2178964
  have hstable : (prefixWord ++ tailWord_2178964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178964).length < 2 ^ (prefixWord ++ tailWord_2178964).sum := by decide
  have hdescent : baseEnd_2178964 < baseStart_2178964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178991 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 1, 1, 3]
def baseStart_2178991 : Nat := 118140960795 + 2178991 * 2 ^ 59
def prefixEnd_2178991 : Nat := 4983230072969 + 3 ^ 40 * 2178991 * 2
def baseEnd_2178991 : Nat := 1118869724821189421391509

theorem tailTrace_2178991 : CollatzResearch.WordTrace tailWord_2178991 prefixEnd_2178991 1118869724821189421391509 := by
  unfold tailWord_2178991
  simp only [CollatzResearch.WordTrace]
  refine ⟨79474330848895223880168827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52982887232596815920112551 79474330848895223880168827)
  ·
    refine ⟨119211496273342835820253241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79474330848895223880168827 119211496273342835820253241)
    ·
      refine ⟨89408622205007126865189931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119211496273342835820253241 89408622205007126865189931)
      ·
        refine ⟨134112933307510690297784897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89408622205007126865189931 134112933307510690297784897)
        ·
          refine ⟨100584699980633017723338673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134112933307510690297784897 100584699980633017723338673)
          ·
            refine ⟨75438524985474763292504005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100584699980633017723338673 75438524985474763292504005)
            ·
              refine ⟨14144723434776518117344501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75438524985474763292504005 14144723434776518117344501)
              ·
                refine ⟨1326067822010298573501047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14144723434776518117344501 1326067822010298573501047)
                ·
                  refine ⟨1989101733015447860251571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326067822010298573501047 1989101733015447860251571)
                  ·
                    refine ⟨2983652599523171790377357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1989101733015447860251571 2983652599523171790377357)
                    ·
                      refine ⟨1118869724821189421391509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2983652599523171790377357 1118869724821189421391509)
                      ·
                        rfl

theorem cell23_2178991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 1, 3].length) (baseStart_2178991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2178991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2178991 prefixEnd_2178991 := by exact prefixLift 2178991
  have htrace : WordTrace (prefixWord ++ tailWord_2178991) baseStart_2178991 baseEnd_2178991 := by
    simpa [prefixWord, tailWord_2178991, baseEnd_2178991] using wordTrace_append hprefix tailTrace_2178991
  have hstable : (prefixWord ++ tailWord_2178991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178991).length < 2 ^ (prefixWord ++ tailWord_2178991).sum := by decide
  have hdescent : baseEnd_2178991 < baseStart_2178991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179024 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_2179024 : Nat := 118140960795 + 2179024 * 2 ^ 59
def prefixEnd_2179024 : Nat := 4983230072969 + 3 ^ 40 * 2179024 * 2
def baseEnd_2179024 : Nat := 372962223227595930759619

theorem tailTrace_2179024 : CollatzResearch.WordTrace tailWord_2179024 prefixEnd_2179024 372962223227595930759619 := by
  unfold tailWord_2179024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39737767228887835258060063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52983689638517113677413417 39737767228887835258060063)
  ·
    refine ⟨59606650843331752887090095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39737767228887835258060063 59606650843331752887090095)
    ·
      refine ⟨89409976264997629330635143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59606650843331752887090095 89409976264997629330635143)
      ·
        refine ⟨134114964397496443995952715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89409976264997629330635143 134114964397496443995952715)
        ·
          refine ⟨201172446596244665993929073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134114964397496443995952715 201172446596244665993929073)
          ·
            refine ⟨150879334947183499495446805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201172446596244665993929073 150879334947183499495446805)
            ·
              refine ⟨7072468825649226538849069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150879334947183499495446805 7072468825649226538849069)
              ·
                refine ⟨2652175809618459952068401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7072468825649226538849069 2652175809618459952068401)
                ·
                  refine ⟨1989131857213844964051301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2652175809618459952068401 1989131857213844964051301)
                  ·
                    refine ⟨372962223227595930759619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1989131857213844964051301 372962223227595930759619)
                    ·
                      rfl

theorem cell23_2179024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_2179024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179024 prefixEnd_2179024 := by exact prefixLift 2179024
  have htrace : WordTrace (prefixWord ++ tailWord_2179024) baseStart_2179024 baseEnd_2179024 := by
    simpa [prefixWord, tailWord_2179024, baseEnd_2179024] using wordTrace_append hprefix tailTrace_2179024
  have hstable : (prefixWord ++ tailWord_2179024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179024).length < 2 ^ (prefixWord ++ tailWord_2179024).sum := by decide
  have hdescent : baseEnd_2179024 < baseStart_2179024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179031 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_2179031 : Nat := 118140960795 + 2179031 * 2 ^ 59
def prefixEnd_2179031 : Nat := 4983230072969 + 3 ^ 40 * 2179031 * 2
def baseEnd_2179031 : Nat := 1118890264047369264891325

theorem tailTrace_2179031 : CollatzResearch.WordTrace tailWord_2179031 prefixEnd_2179031 1118890264047369264891325 := by
  unfold tailWord_2179031
  simp only [CollatzResearch.WordTrace]
  refine ⟨79475789768750310711624947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52983859845833540474416631 79475789768750310711624947)
  ·
    refine ⟨119213684653125466067437421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79475789768750310711624947 119213684653125466067437421)
    ·
      refine ⟨44705131744922049775289033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119213684653125466067437421 44705131744922049775289033)
      ·
        refine ⟨33528848808691537331466775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44705131744922049775289033 33528848808691537331466775)
        ·
          refine ⟨50293273213037305997200163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33528848808691537331466775 50293273213037305997200163)
          ·
            refine ⟨75439909819555958995800245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50293273213037305997200163 75439909819555958995800245)
            ·
              refine ⟨7072491545583371155856273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75439909819555958995800245 7072491545583371155856273)
              ·
                refine ⟨5304368659187528366892205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7072491545583371155856273 5304368659187528366892205)
                ·
                  refine ⟨1989138247195323137584577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5304368659187528366892205 1989138247195323137584577)
                  ·
                    refine ⟨1491853685396492353188433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1989138247195323137584577 1491853685396492353188433)
                    ·
                      refine ⟨1118890264047369264891325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491853685396492353188433 1118890264047369264891325)
                      ·
                        rfl

theorem cell23_2179031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_2179031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179031 prefixEnd_2179031 := by exact prefixLift 2179031
  have htrace : WordTrace (prefixWord ++ tailWord_2179031) baseStart_2179031 baseEnd_2179031 := by
    simpa [prefixWord, tailWord_2179031, baseEnd_2179031] using wordTrace_append hprefix tailTrace_2179031
  have hstable : (prefixWord ++ tailWord_2179031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179031).length < 2 ^ (prefixWord ++ tailWord_2179031).sum := by decide
  have hdescent : baseEnd_2179031 < baseStart_2179031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179042 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2179042 : Nat := 118140960795 + 2179042 * 2 ^ 59
def prefixEnd_2179042 : Nat := 4983230072969 + 3 ^ 40 * 2179042 * 2
def baseEnd_2179042 : Nat := 1118895912334568721853775

theorem tailTrace_2179042 : CollatzResearch.WordTrace tailWord_2179042 prefixEnd_2179042 1118895912334568721853775 := by
  unfold tailWord_2179042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869047742927614897568845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52984127314473639726850253 19869047742927614897568845)
  ·
    refine ⟨7450892903597855586588317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19869047742927614897568845 7450892903597855586588317)
    ·
      refine ⟨2794084838849195844970619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7450892903597855586588317 2794084838849195844970619)
      ·
        refine ⟨4191127258273793767455929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794084838849195844970619 4191127258273793767455929)
        ·
          refine ⟨3143345443705345325591947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4191127258273793767455929 3143345443705345325591947)
          ·
            refine ⟨4715018165558017988387921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143345443705345325591947 4715018165558017988387921)
            ·
              refine ⟨3536263624168513491290941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4715018165558017988387921 3536263624168513491290941)
              ·
                refine ⟨1326098859063192559234103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3536263624168513491290941 1326098859063192559234103)
                ·
                  refine ⟨1989148288594788838851155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326098859063192559234103 1989148288594788838851155)
                  ·
                    refine ⟨2983722432892183258276733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1989148288594788838851155 2983722432892183258276733)
                    ·
                      refine ⟨1118895912334568721853775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2983722432892183258276733 1118895912334568721853775)
                      ·
                        rfl

theorem cell23_2179042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2179042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179042 prefixEnd_2179042 := by exact prefixLift 2179042
  have htrace : WordTrace (prefixWord ++ tailWord_2179042) baseStart_2179042 baseEnd_2179042 := by
    simpa [prefixWord, tailWord_2179042, baseEnd_2179042] using wordTrace_append hprefix tailTrace_2179042
  have hstable : (prefixWord ++ tailWord_2179042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179042).length < 2 ^ (prefixWord ++ tailWord_2179042).sum := by decide
  have hdescent : baseEnd_2179042 < baseStart_2179042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179091 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 1, 3, 2]
def baseStart_2179091 : Nat := 118140960795 + 2179091 * 2 ^ 59
def prefixEnd_2179091 : Nat := 4983230072969 + 3 ^ 40 * 2179091 * 2
def baseEnd_2179091 : Nat := 1118921072886639030141049

theorem tailTrace_2179091 : CollatzResearch.WordTrace tailWord_2179091 prefixEnd_2179091 1118921072886639030141049 := by
  unfold tailWord_2179091
  simp only [CollatzResearch.WordTrace]
  refine ⟨79477978148532940958809127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52985318765688627305872751 79477978148532940958809127)
  ·
    refine ⟨119216967222799411438213691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79477978148532940958809127 119216967222799411438213691)
    ·
      refine ⟨178825450834199117157320537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119216967222799411438213691 178825450834199117157320537)
      ·
        refine ⟨134119088125649337867990403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178825450834199117157320537 134119088125649337867990403)
        ·
          refine ⟨201178632188474006801985605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134119088125649337867990403 201178632188474006801985605)
          ·
            refine ⟨37720993535338876275372301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201178632188474006801985605 37720993535338876275372301)
            ·
              refine ⟨14145372575752078603264613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37720993535338876275372301 14145372575752078603264613)
              ·
                refine ⟨2652257357953514738112115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14145372575752078603264613 2652257357953514738112115)
                ·
                  refine ⟨3978386036930272107168173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652257357953514738112115 3978386036930272107168173)
                  ·
                    refine ⟨1491894763848852040188065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3978386036930272107168173 1491894763848852040188065)
                    ·
                      refine ⟨1118921072886639030141049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491894763848852040188065 1118921072886639030141049)
                      ·
                        rfl

theorem cell23_2179091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3, 2].length) (baseStart_2179091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179091 prefixEnd_2179091 := by exact prefixLift 2179091
  have htrace : WordTrace (prefixWord ++ tailWord_2179091) baseStart_2179091 baseEnd_2179091 := by
    simpa [prefixWord, tailWord_2179091, baseEnd_2179091] using wordTrace_append hprefix tailTrace_2179091
  have hstable : (prefixWord ++ tailWord_2179091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179091).length < 2 ^ (prefixWord ++ tailWord_2179091).sum := by decide
  have hdescent : baseEnd_2179091 < baseStart_2179091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179158 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2179158 : Nat := 118140960795 + 2179158 * 2 ^ 59
def prefixEnd_2179158 : Nat := 4983230072969 + 3 ^ 40 * 2179158 * 2
def baseEnd_2179158 : Nat := 1118955476090490268003241

theorem tailTrace_2179158 : CollatzResearch.WordTrace tailWord_2179158 prefixEnd_2179158 1118955476090490268003241 := by
  unfold tailWord_2179158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4967526364955638212593633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52986947892860140934332085 4967526364955638212593633)
  ·
    refine ⟨3725644773716728659445225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4967526364955638212593633 3725644773716728659445225)
    ·
      refine ⟨2794233580287546494583919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3725644773716728659445225 2794233580287546494583919)
      ·
        refine ⟨4191350370431319741875879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794233580287546494583919 4191350370431319741875879)
        ·
          refine ⟨6287025555646979612813819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191350370431319741875879 6287025555646979612813819)
          ·
            refine ⟨9430538333470469419220729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287025555646979612813819 9430538333470469419220729)
            ·
              refine ⟨7072903750102852064415547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430538333470469419220729 7072903750102852064415547)
              ·
                refine ⟨10609355625154278096623321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072903750102852064415547 10609355625154278096623321)
                ·
                  refine ⟨7957016718865708572467491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10609355625154278096623321 7957016718865708572467491)
                  ·
                    refine ⟨11935525078298562858701237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7957016718865708572467491 11935525078298562858701237)
                    ·
                      refine ⟨1118955476090490268003241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11935525078298562858701237 1118955476090490268003241)
                      ·
                        rfl

theorem cell23_2179158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2179158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179158 prefixEnd_2179158 := by exact prefixLift 2179158
  have htrace : WordTrace (prefixWord ++ tailWord_2179158) baseStart_2179158 baseEnd_2179158 := by
    simpa [prefixWord, tailWord_2179158, baseEnd_2179158] using wordTrace_append hprefix tailTrace_2179158
  have hstable : (prefixWord ++ tailWord_2179158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179158).length < 2 ^ (prefixWord ++ tailWord_2179158).sum := by decide
  have hdescent : baseEnd_2179158 < baseStart_2179158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179178 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_2179178 : Nat := 118140960795 + 2179178 * 2 ^ 59
def prefixEnd_2179178 : Nat := 4983230072969 + 3 ^ 40 * 2179178 * 2
def baseEnd_2179178 : Nat := 124329527300397798861461

theorem tailTrace_2179178 : CollatzResearch.WordTrace tailWord_2179178 prefixEnd_2179178 124329527300397798861461 := by
  unfold tailWord_2179178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870287824804438704306547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52987434199478503211484125 19870287824804438704306547)
  ·
    refine ⟨29805431737206658056459821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19870287824804438704306547 29805431737206658056459821)
    ·
      refine ⟨11177036901452496771172433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29805431737206658056459821 11177036901452496771172433)
      ·
        refine ⟨8382777676089372578379325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11177036901452496771172433 8382777676089372578379325)
        ·
          refine ⟨3143541628533514716892247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8382777676089372578379325 3143541628533514716892247)
          ·
            refine ⟨4715312442800272075338371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143541628533514716892247 4715312442800272075338371)
            ·
              refine ⟨7072968664200408113007557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715312442800272075338371 7072968664200408113007557)
              ·
                refine ⟨1326181624537576521188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7072968664200408113007557 1326181624537576521188917)
                ·
                  refine ⟨124329527300397798861461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1326181624537576521188917 124329527300397798861461)
                  ·
                    rfl

theorem cell23_2179178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_2179178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179178 prefixEnd_2179178 := by exact prefixLift 2179178
  have htrace : WordTrace (prefixWord ++ tailWord_2179178) baseStart_2179178 baseEnd_2179178 := by
    simpa [prefixWord, tailWord_2179178, baseEnd_2179178] using wordTrace_append hprefix tailTrace_2179178
  have hstable : (prefixWord ++ tailWord_2179178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179178).length < 2 ^ (prefixWord ++ tailWord_2179178).sum := by decide
  have hdescent : baseEnd_2179178 < baseStart_2179178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179181 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2179181 : Nat := 118140960795 + 2179181 * 2 ^ 59
def prefixEnd_2179181 : Nat := 4983230072969 + 3 ^ 40 * 2179181 * 2
def baseEnd_2179181 : Nat := 1118967286145543678015635

theorem tailTrace_2179181 : CollatzResearch.WordTrace tailWord_2179181 prefixEnd_2179181 1118967286145543678015635 := by
  unfold tailWord_2179181
  simp only [CollatzResearch.WordTrace]
  refine ⟨79481260718206886329585397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52987507145471257553056931 79481260718206886329585397)
  ·
    refine ⟨7451368192331895593398631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79481260718206886329585397 7451368192331895593398631)
    ·
      refine ⟨11177052288497843390097947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451368192331895593398631 11177052288497843390097947)
      ·
        refine ⟨16765578432746765085146921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11177052288497843390097947 16765578432746765085146921)
        ·
          refine ⟨12574183824560073813860191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16765578432746765085146921 12574183824560073813860191)
          ·
            refine ⟨18861275736840110720790287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12574183824560073813860191 18861275736840110720790287)
            ·
              refine ⟨28291913605260166081185431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18861275736840110720790287 28291913605260166081185431)
              ·
                refine ⟨42437870407890249121778147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28291913605260166081185431 42437870407890249121778147)
                ·
                  refine ⟨63656805611835373682667221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42437870407890249121778147 63656805611835373682667221)
                  ·
                    refine ⟨1491956381527391570687513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63656805611835373682667221 1491956381527391570687513)
                    ·
                      refine ⟨1118967286145543678015635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1491956381527391570687513 1118967286145543678015635)
                      ·
                        rfl

theorem cell23_2179181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2179181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179181 prefixEnd_2179181 := by exact prefixLift 2179181
  have htrace : WordTrace (prefixWord ++ tailWord_2179181) baseStart_2179181 baseEnd_2179181 := by
    simpa [prefixWord, tailWord_2179181, baseEnd_2179181] using wordTrace_append hprefix tailTrace_2179181
  have hstable : (prefixWord ++ tailWord_2179181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179181).length < 2 ^ (prefixWord ++ tailWord_2179181).sum := by decide
  have hdescent : baseEnd_2179181 < baseStart_2179181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179184 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_2179184 : Nat := 118140960795 + 2179184 * 2 ^ 59
def prefixEnd_2179184 : Nat := 4983230072969 + 3 ^ 40 * 2179184 * 2
def baseEnd_2179184 : Nat := 1118968826587507166278121

theorem tailTrace_2179184 : CollatzResearch.WordTrace tailWord_2179184 prefixEnd_2179184 1118968826587507166278121 := by
  unfold tailWord_2179184
  simp only [CollatzResearch.WordTrace]
  refine ⟨39740685068598008920972303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52987580091464011894629737 39740685068598008920972303)
  ·
    refine ⟨59611027602897013381458455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39740685068598008920972303 59611027602897013381458455)
    ·
      refine ⟨89416541404345520072187683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59611027602897013381458455 89416541404345520072187683)
      ·
        refine ⟨134124812106518280108281525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89416541404345520072187683 134124812106518280108281525)
        ·
          refine ⟨12574201134986088760151393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134124812106518280108281525 12574201134986088760151393)
          ·
            refine ⟨9430650851239566570113545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12574201134986088760151393 9430650851239566570113545)
            ·
              refine ⟨7072988138429674927585159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430650851239566570113545 7072988138429674927585159)
              ·
                refine ⟨10609482207644512391377739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072988138429674927585159 10609482207644512391377739)
                ·
                  refine ⟨15914223311466768587066609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10609482207644512391377739 15914223311466768587066609)
                  ·
                    refine ⟨11935667483600076440299957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15914223311466768587066609 11935667483600076440299957)
                    ·
                      refine ⟨1118968826587507166278121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11935667483600076440299957 1118968826587507166278121)
                      ·
                        rfl

theorem cell23_2179184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_2179184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179184 prefixEnd_2179184 := by exact prefixLift 2179184
  have htrace : WordTrace (prefixWord ++ tailWord_2179184) baseStart_2179184 baseEnd_2179184 := by
    simpa [prefixWord, tailWord_2179184, baseEnd_2179184] using wordTrace_append hprefix tailTrace_2179184
  have hstable : (prefixWord ++ tailWord_2179184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179184).length < 2 ^ (prefixWord ++ tailWord_2179184).sum := by decide
  have hdescent : baseEnd_2179184 < baseStart_2179184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179208 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_2179208 : Nat := 118140960795 + 2179208 * 2 ^ 59
def prefixEnd_2179208 : Nat := 4983230072969 + 3 ^ 40 * 2179208 * 2
def baseEnd_2179208 : Nat := 372993716707738357459337

theorem tailTrace_2179208 : CollatzResearch.WordTrace tailWord_2179208 prefixEnd_2179208 372993716707738357459337 := by
  unfold tailWord_2179208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39741122744554534970409139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52988163659406046627212185 39741122744554534970409139)
  ·
    refine ⟨59611684116831802455613709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39741122744554534970409139 59611684116831802455613709)
    ·
      refine ⟨22354381543811925920855141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59611684116831802455613709 22354381543811925920855141)
      ·
        refine ⟨4191446539464736110160339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22354381543811925920855141 4191446539464736110160339)
        ·
          refine ⟨6287169809197104165240509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191446539464736110160339 6287169809197104165240509)
          ·
            refine ⟨2357688678448914061965191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6287169809197104165240509 2357688678448914061965191)
            ·
              refine ⟨3536533017673371092947787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357688678448914061965191 3536533017673371092947787)
              ·
                refine ⟨5304799526510056639421681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536533017673371092947787 5304799526510056639421681)
                ·
                  refine ⟨3978599644882542479566261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5304799526510056639421681 3978599644882542479566261)
                  ·
                    refine ⟨372993716707738357459337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3978599644882542479566261 372993716707738357459337)
                    ·
                      rfl

theorem cell23_2179208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_2179208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179208 prefixEnd_2179208 := by exact prefixLift 2179208
  have htrace : WordTrace (prefixWord ++ tailWord_2179208) baseStart_2179208 baseEnd_2179208 := by
    simpa [prefixWord, tailWord_2179208, baseEnd_2179208] using wordTrace_append hprefix tailTrace_2179208
  have hstable : (prefixWord ++ tailWord_2179208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179208).length < 2 ^ (prefixWord ++ tailWord_2179208).sum := by decide
  have hdescent : baseEnd_2179208 < baseStart_2179208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179281 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_2179281 : Nat := 118140960795 + 2179281 * 2 ^ 59
def prefixEnd_2179281 : Nat := 4983230072969 + 3 ^ 40 * 2179281 * 2
def baseEnd_2179281 : Nat := 373006211403664428921725

theorem tailTrace_2179281 : CollatzResearch.WordTrace tailWord_2179281 prefixEnd_2179281 373006211403664428921725 := by
  unfold tailWord_2179281
  simp only [CollatzResearch.WordTrace]
  refine ⟨79484908017844603408225697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52989938678563068938817131 79484908017844603408225697)
  ·
    refine ⟨59613681013383452556169273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79484908017844603408225697 59613681013383452556169273)
    ·
      refine ⟨44710260760037589417126955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59613681013383452556169273 44710260760037589417126955)
      ·
        refine ⟨67065391140056384125690433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44710260760037589417126955 67065391140056384125690433)
        ·
          refine ⟨50299043355042288094267825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67065391140056384125690433 50299043355042288094267825)
          ·
            refine ⟨37724282516281716070700869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50299043355042288094267825 37724282516281716070700869)
            ·
              refine ⟨7073302971802821763256413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37724282516281716070700869 7073302971802821763256413)
              ·
                refine ⟨2652488614426058161221155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7073302971802821763256413 2652488614426058161221155)
                ·
                  refine ⟨3978732921639087241831733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652488614426058161221155 3978732921639087241831733)
                  ·
                    refine ⟨373006211403664428921725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3978732921639087241831733 373006211403664428921725)
                    ·
                      rfl

theorem cell23_2179281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_2179281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179281 prefixEnd_2179281 := by exact prefixLift 2179281
  have htrace : WordTrace (prefixWord ++ tailWord_2179281) baseStart_2179281 baseEnd_2179281 := by
    simpa [prefixWord, tailWord_2179281, baseEnd_2179281] using wordTrace_append hprefix tailTrace_2179281
  have hstable : (prefixWord ++ tailWord_2179281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179281).length < 2 ^ (prefixWord ++ tailWord_2179281).sum := by decide
  have hdescent : baseEnd_2179281 < baseStart_2179281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179288 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_2179288 : Nat := 118140960795 + 2179288 * 2 ^ 59
def prefixEnd_2179288 : Nat := 4983230072969 + 3 ^ 40 * 2179288 * 2
def baseEnd_2179288 : Nat := 1119022228575574759377643

theorem tailTrace_2179288 : CollatzResearch.WordTrace tailWord_2179288 prefixEnd_2179288 1119022228575574759377643 := by
  unfold tailWord_2179288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39742581664409621801865259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52990108885879495735820345 39742581664409621801865259)
  ·
    refine ⟨59613872496614432702797889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39742581664409621801865259 59613872496614432702797889)
    ·
      refine ⟨44710404372460824527098417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59613872496614432702797889 44710404372460824527098417)
      ·
        refine ⟨33532803279345618395323813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44710404372460824527098417 33532803279345618395323813)
        ·
          refine ⟨6287400614877303449123215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33532803279345618395323813 6287400614877303449123215)
          ·
            refine ⟨9431100922315955173684823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287400614877303449123215 9431100922315955173684823)
            ·
              refine ⟨14146651383473932760527235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9431100922315955173684823 14146651383473932760527235)
              ·
                refine ⟨21219977075210899140790853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14146651383473932760527235 21219977075210899140790853)
                ·
                  refine ⟨3978745701602043588898285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21219977075210899140790853 3978745701602043588898285)
                  ·
                    refine ⟨1492029638100766345836857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3978745701602043588898285 1492029638100766345836857)
                    ·
                      refine ⟨1119022228575574759377643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492029638100766345836857 1119022228575574759377643)
                      ·
                        rfl

theorem cell23_2179288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_2179288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179288 prefixEnd_2179288 := by exact prefixLift 2179288
  have htrace : WordTrace (prefixWord ++ tailWord_2179288) baseStart_2179288 baseEnd_2179288 := by
    simpa [prefixWord, tailWord_2179288, baseEnd_2179288] using wordTrace_append hprefix tailTrace_2179288
  have hstable : (prefixWord ++ tailWord_2179288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179288).length < 2 ^ (prefixWord ++ tailWord_2179288).sum := by decide
  have hdescent : baseEnd_2179288 < baseStart_2179288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179318 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2179318 : Nat := 118140960795 + 2179318 * 2 ^ 59
def prefixEnd_2179318 : Nat := 4983230072969 + 3 ^ 40 * 2179318 * 2
def baseEnd_2179318 : Nat := 1119037632995209642002505

theorem tailTrace_2179318 : CollatzResearch.WordTrace tailWord_2179318 prefixEnd_2179318 1119037632995209642002505 := by
  unfold tailWord_2179318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4967891094919409920457663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52990838345807039151548405 4967891094919409920457663)
  ·
    refine ⟨7451836642379114880686495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4967891094919409920457663 7451836642379114880686495)
    ·
      refine ⟨11177754963568672321029743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451836642379114880686495 11177754963568672321029743)
      ·
        refine ⟨16766632445353008481544615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11177754963568672321029743 16766632445353008481544615)
        ·
          refine ⟨25149948668029512722316923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16766632445353008481544615 25149948668029512722316923)
          ·
            refine ⟨37724923002044269083475385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25149948668029512722316923 37724923002044269083475385)
            ·
              refine ⟨28293692251533201812606539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37724923002044269083475385 28293692251533201812606539)
              ·
                refine ⟨42440538377299802718909809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28293692251533201812606539 42440538377299802718909809)
                ·
                  refine ⟨31830403782974852039182357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42440538377299802718909809 31830403782974852039182357)
                  ·
                    refine ⟨1492050177326946189336673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31830403782974852039182357 1492050177326946189336673)
                    ·
                      refine ⟨1119037632995209642002505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492050177326946189336673 1119037632995209642002505)
                      ·
                        rfl

theorem cell23_2179318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2179318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179318 prefixEnd_2179318 := by exact prefixLift 2179318
  have htrace : WordTrace (prefixWord ++ tailWord_2179318) baseStart_2179318 baseEnd_2179318 := by
    simpa [prefixWord, tailWord_2179318, baseEnd_2179318] using wordTrace_append hprefix tailTrace_2179318
  have hstable : (prefixWord ++ tailWord_2179318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179318).length < 2 ^ (prefixWord ++ tailWord_2179318).sum := by decide
  have hdescent : baseEnd_2179318 < baseStart_2179318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179331 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4]
def baseStart_2179331 : Nat := 118140960795 + 2179331 * 2 ^ 59
def prefixEnd_2179331 : Nat := 4983230072969 + 3 ^ 40 * 2179331 * 2
def baseEnd_2179331 : Nat := 1119044308243718091139945

theorem tailTrace_2179331 : CollatzResearch.WordTrace tailWord_2179331 prefixEnd_2179331 1119044308243718091139945 := by
  unfold tailWord_2179331
  simp only [CollatzResearch.WordTrace]
  refine ⟨79486731667663461947545847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52991154445108974631697231 79486731667663461947545847)
  ·
    refine ⟨119230097501495192921318771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79486731667663461947545847 119230097501495192921318771)
    ·
      refine ⟨178845146252242789381978157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119230097501495192921318771 178845146252242789381978157)
      ·
        refine ⟨67066929844591046018241809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178845146252242789381978157 67066929844591046018241809)
        ·
          refine ⟨50300197383443284513681357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67066929844591046018241809 50300197383443284513681357)
          ·
            refine ⟨18862574018791231692630509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50300197383443284513681357 18862574018791231692630509)
            ·
              refine ⟨7073465257046711884736441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18862574018791231692630509 7073465257046711884736441)
              ·
                refine ⟨5305098942785033913552331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7073465257046711884736441 5305098942785033913552331)
                ·
                  refine ⟨7957648414177550870328497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305098942785033913552331 7957648414177550870328497)
                  ·
                    refine ⟨5968236310633163152746373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7957648414177550870328497 5968236310633163152746373)
                    ·
                      refine ⟨1119044308243718091139945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5968236310633163152746373 1119044308243718091139945)
                      ·
                        rfl

theorem cell23_2179331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_2179331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179331 prefixEnd_2179331 := by exact prefixLift 2179331
  have htrace : WordTrace (prefixWord ++ tailWord_2179331) baseStart_2179331 baseEnd_2179331 := by
    simpa [prefixWord, tailWord_2179331, baseEnd_2179331] using wordTrace_append hprefix tailTrace_2179331
  have hstable : (prefixWord ++ tailWord_2179331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179331).length < 2 ^ (prefixWord ++ tailWord_2179331).sum := by decide
  have hdescent : baseEnd_2179331 < baseStart_2179331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179338 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2179338 : Nat := 118140960795 + 2179338 * 2 ^ 59
def prefixEnd_2179338 : Nat := 4983230072969 + 3 ^ 40 * 2179338 * 2
def baseEnd_2179338 : Nat := 1119047902608299563752413

theorem tailTrace_2179338 : CollatzResearch.WordTrace tailWord_2179338 prefixEnd_2179338 1119047902608299563752413 := by
  unfold tailWord_2179338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19871746744659525535762667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52991324652425401428700445 19871746744659525535762667)
  ·
    refine ⟨29807620116989288303644001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19871746744659525535762667 29807620116989288303644001)
    ·
      refine ⟨22355715087741966227733001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29807620116989288303644001 22355715087741966227733001)
      ·
        refine ⟨16766786315806474670799751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22355715087741966227733001 16766786315806474670799751)
        ·
          refine ⟨25150179473709712006199627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16766786315806474670799751 25150179473709712006199627)
          ·
            refine ⟨37725269210564568009299441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25150179473709712006199627 37725269210564568009299441)
            ·
              refine ⟨28293951907923426006974581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37725269210564568009299441 28293951907923426006974581)
              ·
                refine ⟨2652557991367821188153867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28293951907923426006974581 2652557991367821188153867)
                ·
                  refine ⟨3978836987051731782230801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652557991367821188153867 3978836987051731782230801)
                  ·
                    refine ⟨2984127740288798836673101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3978836987051731782230801 2984127740288798836673101)
                    ·
                      refine ⟨1119047902608299563752413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2984127740288798836673101 1119047902608299563752413)
                      ·
                        rfl

theorem cell23_2179338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2179338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179338 prefixEnd_2179338 := by exact prefixLift 2179338
  have htrace : WordTrace (prefixWord ++ tailWord_2179338) baseStart_2179338 baseEnd_2179338 := by
    simpa [prefixWord, tailWord_2179338, baseEnd_2179338] using wordTrace_append hprefix tailTrace_2179338
  have hstable : (prefixWord ++ tailWord_2179338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179338).length < 2 ^ (prefixWord ++ tailWord_2179338).sum := by decide
  have hdescent : baseEnd_2179338 < baseStart_2179338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179352 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2179352 : Nat := 118140960795 + 2179352 * 2 ^ 59
def prefixEnd_2179352 : Nat := 4983230072969 + 3 ^ 40 * 2179352 * 2
def baseEnd_2179352 : Nat := 1119055091337462508977349

theorem tailTrace_2179352 : CollatzResearch.WordTrace tailWord_2179352 prefixEnd_2179352 1119055091337462508977349 := by
  unfold tailWord_2179352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39743748800293691267030155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52991665067058255022706873 39743748800293691267030155)
  ·
    refine ⟨59615623200440536900545233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39743748800293691267030155 59615623200440536900545233)
    ·
      refine ⟨44711717400330402675408925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59615623200440536900545233 44711717400330402675408925)
      ·
        refine ⟨16766894025123901003278347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44711717400330402675408925 16766894025123901003278347)
        ·
          refine ⟨25150341037685851504917521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16766894025123901003278347 25150341037685851504917521)
          ·
            refine ⟨18862755778264388628688141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25150341037685851504917521 18862755778264388628688141)
            ·
              refine ⟨7073533416849145735758053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18862755778264388628688141 7073533416849145735758053)
              ·
                refine ⟨1326287515659214825454635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7073533416849145735758053 1326287515659214825454635)
                ·
                  refine ⟨1989431273488822238181953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326287515659214825454635 1989431273488822238181953)
                  ·
                    refine ⟨1492073455116616678636465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1989431273488822238181953 1492073455116616678636465)
                    ·
                      refine ⟨1119055091337462508977349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492073455116616678636465 1119055091337462508977349)
                      ·
                        rfl

theorem cell23_2179352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2179352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179352 prefixEnd_2179352 := by exact prefixLift 2179352
  have htrace : WordTrace (prefixWord ++ tailWord_2179352) baseStart_2179352 baseEnd_2179352 := by
    simpa [prefixWord, tailWord_2179352, baseEnd_2179352] using wordTrace_append hprefix tailTrace_2179352
  have hstable : (prefixWord ++ tailWord_2179352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179352).length < 2 ^ (prefixWord ++ tailWord_2179352).sum := by decide
  have hdescent : baseEnd_2179352 < baseStart_2179352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179381 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2179381 : Nat := 118140960795 + 2179381 * 2 ^ 59
def prefixEnd_2179381 : Nat := 4983230072969 + 3 ^ 40 * 2179381 * 2
def baseEnd_2179381 : Nat := 1119069982276442895514715

theorem tailTrace_2179381 : CollatzResearch.WordTrace tailWord_2179381 prefixEnd_2179381 1119069982276442895514715 := by
  unfold tailWord_2179381
  simp only [CollatzResearch.WordTrace]
  refine ⟨79488555317482320486865997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52992370211654880324577331 79488555317482320486865997)
  ·
    refine ⟨29808208244055870182574749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79488555317482320486865997 29808208244055870182574749)
    ·
      refine ⟨11178078091520951318465531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29808208244055870182574749 11178078091520951318465531)
      ·
        refine ⟨16767117137281426977698297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11178078091520951318465531 16767117137281426977698297)
        ·
          refine ⟨12575337852961070233273723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16767117137281426977698297 12575337852961070233273723)
          ·
            refine ⟨18863006779441605349910585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12575337852961070233273723 18863006779441605349910585)
            ·
              refine ⟨14147255084581204012432939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18863006779441605349910585 14147255084581204012432939)
              ·
                refine ⟨21220882626871806018649409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14147255084581204012432939 21220882626871806018649409)
                ·
                  refine ⟨15915661970153854513987057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21220882626871806018649409 15915661970153854513987057)
                  ·
                    refine ⟨11936746477615390885490293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15915661970153854513987057 11936746477615390885490293)
                    ·
                      refine ⟨1119069982276442895514715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11936746477615390885490293 1119069982276442895514715)
                      ·
                        rfl

theorem cell23_2179381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2179381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179381 prefixEnd_2179381 := by exact prefixLift 2179381
  have htrace : WordTrace (prefixWord ++ tailWord_2179381) baseStart_2179381 baseEnd_2179381 := by
    simpa [prefixWord, tailWord_2179381, baseEnd_2179381] using wordTrace_append hprefix tailTrace_2179381
  have hstable : (prefixWord ++ tailWord_2179381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179381).length < 2 ^ (prefixWord ++ tailWord_2179381).sum := by decide
  have hdescent : baseEnd_2179381 < baseStart_2179381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179411 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3]
def baseStart_2179411 : Nat := 118140960795 + 2179411 * 2 ^ 59
def prefixEnd_2179411 : Nat := 4983230072969 + 3 ^ 40 * 2179411 * 2
def baseEnd_2179411 : Nat := 1119085386696077778139577

theorem tailTrace_2179411 : CollatzResearch.WordTrace tailWord_2179411 prefixEnd_2179411 1119085386696077778139577 := by
  unfold tailWord_2179411
  simp only [CollatzResearch.WordTrace]
  refine ⟨79489649507373635610458087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52993099671582423740305391 79489649507373635610458087)
  ·
    refine ⟨119234474261060453415687131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79489649507373635610458087 119234474261060453415687131)
    ·
      refine ⟨178851711391590680123530697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119234474261060453415687131 178851711391590680123530697)
      ·
        refine ⟨134138783543693010092648023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178851711391590680123530697 134138783543693010092648023)
        ·
          refine ⟨201208175315539515138972035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134138783543693010092648023 201208175315539515138972035)
          ·
            refine ⟨301812262973309272708458053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201208175315539515138972035 301812262973309272708458053)
            ·
              refine ⟨56589799307495488632835885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301812262973309272708458053 56589799307495488632835885)
              ·
                refine ⟨21221174740310808237313457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56589799307495488632835885 21221174740310808237313457)
                ·
                  refine ⟨15915881055233106177985093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21221174740310808237313457 15915881055233106177985093)
                  ·
                    refine ⟨2984227697856207408372205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15915881055233106177985093 2984227697856207408372205)
                    ·
                      refine ⟨1119085386696077778139577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2984227697856207408372205 1119085386696077778139577)
                      ·
                        rfl

theorem cell23_2179411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_2179411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179411 prefixEnd_2179411 := by exact prefixLift 2179411
  have htrace : WordTrace (prefixWord ++ tailWord_2179411) baseStart_2179411 baseEnd_2179411 := by
    simpa [prefixWord, tailWord_2179411, baseEnd_2179411] using wordTrace_append hprefix tailTrace_2179411
  have hstable : (prefixWord ++ tailWord_2179411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179411).length < 2 ^ (prefixWord ++ tailWord_2179411).sum := by decide
  have hdescent : baseEnd_2179411 < baseStart_2179411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179495 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2179495 : Nat := 118140960795 + 2179495 * 2 ^ 59
def prefixEnd_2179495 : Nat := 4983230072969 + 3 ^ 40 * 2179495 * 2
def baseEnd_2179495 : Nat := 373042839690351816496397

theorem tailTrace_2179495 : CollatzResearch.WordTrace tailWord_2179495 prefixEnd_2179495 373042839690351816496397 := by
  unfold tailWord_2179495
  simp only [CollatzResearch.WordTrace]
  refine ⟨79492713239069317956515939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52995142159379545304343959 79492713239069317956515939)
  ·
    refine ⟨119239069858603976934773909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79492713239069317956515939 119239069858603976934773909)
    ·
      refine ⟨5589331399622061418817527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119239069858603976934773909 5589331399622061418817527)
      ·
        refine ⟨8383997099433092128226291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589331399622061418817527 8383997099433092128226291)
        ·
          refine ⟨12575995649149638192339437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8383997099433092128226291 12575995649149638192339437)
          ·
            refine ⟨4715998368431114322127289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12575995649149638192339437 4715998368431114322127289)
            ·
              refine ⟨3536998776323335741595467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4715998368431114322127289 3536998776323335741595467)
              ·
                refine ⟨5305498164485003612393201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536998776323335741595467 5305498164485003612393201)
                ·
                  refine ⟨3979123623363752709294901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5305498164485003612393201 3979123623363752709294901)
                  ·
                    refine ⟨373042839690351816496397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3979123623363752709294901 373042839690351816496397)
                    ·
                      rfl

theorem cell23_2179495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2179495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179495 prefixEnd_2179495 := by exact prefixLift 2179495
  have htrace : WordTrace (prefixWord ++ tailWord_2179495) baseStart_2179495 baseEnd_2179495 := by
    simpa [prefixWord, tailWord_2179495, baseEnd_2179495] using wordTrace_append hprefix tailTrace_2179495
  have hstable : (prefixWord ++ tailWord_2179495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179495).length < 2 ^ (prefixWord ++ tailWord_2179495).sum := by decide
  have hdescent : baseEnd_2179495 < baseStart_2179495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179532 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2179532 : Nat := 118140960795 + 2179532 * 2 ^ 59
def prefixEnd_2179532 : Nat := 4983230072969 + 3 ^ 40 * 2179532 * 2
def baseEnd_2179532 : Nat := 1119147517855271804726521

theorem tailTrace_2179532 : CollatzResearch.WordTrace tailWord_2179532 prefixEnd_2179532 1119147517855271804726521 := by
  unfold tailWord_2179532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39747031369967636637806425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52996041826623515517075233 39747031369967636637806425)
  ·
    refine ⟨29810273527475727478354819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39747031369967636637806425 29810273527475727478354819)
    ·
      refine ⟨44715410291213591217532229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29810273527475727478354819 44715410291213591217532229)
      ·
        refine ⟨8384139429602548353287293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44715410291213591217532229 8384139429602548353287293)
        ·
          refine ⟨3144052286100955632482735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8384139429602548353287293 3144052286100955632482735)
          ·
            refine ⟨4716078429151433448724103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144052286100955632482735 4716078429151433448724103)
            ·
              refine ⟨7074117643727150173086155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716078429151433448724103 7074117643727150173086155)
              ·
                refine ⟨10611176465590725259629233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074117643727150173086155 10611176465590725259629233)
                ·
                  refine ⟨7958382349193043944721925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10611176465590725259629233 7958382349193043944721925)
                  ·
                    refine ⟨1492196690473695739635361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7958382349193043944721925 1492196690473695739635361)
                    ·
                      refine ⟨1119147517855271804726521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492196690473695739635361 1119147517855271804726521)
                      ·
                        rfl

theorem cell23_2179532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2179532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179532 prefixEnd_2179532 := by exact prefixLift 2179532
  have htrace : WordTrace (prefixWord ++ tailWord_2179532) baseStart_2179532 baseEnd_2179532 := by
    simpa [prefixWord, tailWord_2179532, baseEnd_2179532] using wordTrace_append hprefix tailTrace_2179532
  have hstable : (prefixWord ++ tailWord_2179532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179532).length < 2 ^ (prefixWord ++ tailWord_2179532).sum := by decide
  have hdescent : baseEnd_2179532 < baseStart_2179532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179542 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2179542 : Nat := 118140960795 + 2179542 * 2 ^ 59
def prefixEnd_2179542 : Nat := 4983230072969 + 3 ^ 40 * 2179542 * 2
def baseEnd_2179542 : Nat := 373050884220605588533825

theorem tailTrace_2179542 : CollatzResearch.WordTrace tailWord_2179542 prefixEnd_2179542 373050884220605588533825 := by
  unfold tailWord_2179542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968401716868690311467305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52996284979932696655651253 4968401716868690311467305)
  ·
    refine ⟨3726301287651517733600479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4968401716868690311467305 3726301287651517733600479)
    ·
      refine ⟨5589451931477276600400719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726301287651517733600479 5589451931477276600400719)
      ·
        refine ⟨8384177897215914900601079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589451931477276600400719 8384177897215914900601079)
        ·
          refine ⟨12576266845823872350901619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384177897215914900601079 12576266845823872350901619)
          ·
            refine ⟨18864400268735808526352429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576266845823872350901619 18864400268735808526352429)
            ·
              refine ⟨7074150100775928197382161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18864400268735808526352429 7074150100775928197382161)
              ·
                refine ⟨5305612575581946148036621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7074150100775928197382161 5305612575581946148036621)
                ·
                  refine ⟨1989604715843229805513733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5305612575581946148036621 1989604715843229805513733)
                  ·
                    refine ⟨373050884220605588533825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1989604715843229805513733 373050884220605588533825)
                    ·
                      rfl

theorem cell23_2179542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2179542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179542 prefixEnd_2179542 := by exact prefixLift 2179542
  have htrace : WordTrace (prefixWord ++ tailWord_2179542) baseStart_2179542 baseEnd_2179542 := by
    simpa [prefixWord, tailWord_2179542, baseEnd_2179542] using wordTrace_append hprefix tailTrace_2179542
  have hstable : (prefixWord ++ tailWord_2179542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179542).length < 2 ^ (prefixWord ++ tailWord_2179542).sum := by decide
  have hdescent : baseEnd_2179542 < baseStart_2179542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179605 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_2179605 : Nat := 118140960795 + 2179605 * 2 ^ 59
def prefixEnd_2179605 : Nat := 4983230072969 + 3 ^ 40 * 2179605 * 2
def baseEnd_2179605 : Nat := 1119185001943050019113685

theorem tailTrace_2179605 : CollatzResearch.WordTrace tailWord_2179605 prefixEnd_2179605 1119185001943050019113685 := by
  unfold tailWord_2179605
  simp only [CollatzResearch.WordTrace]
  refine ⟨79496725268670806743020269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52997816845780537828680179 79496725268670806743020269)
  ·
    refine ⟨29811271975751552528632601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79496725268670806743020269 29811271975751552528632601)
    ·
      refine ⟨22358453981813664396474451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29811271975751552528632601 22358453981813664396474451)
      ·
        refine ⟨33537680972720496594711677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22358453981813664396474451 33537680972720496594711677)
        ·
          refine ⟨12576630364770186223016879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33537680972720496594711677 12576630364770186223016879)
          ·
            refine ⟨18864945547155279334525319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576630364770186223016879 18864945547155279334525319)
            ·
              refine ⟨28297418320732919001787979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18864945547155279334525319 28297418320732919001787979)
              ·
                refine ⟨42446127481099378502681969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28297418320732919001787979 42446127481099378502681969)
                ·
                  refine ⟨31834595610824533877011477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42446127481099378502681969 31834595610824533877011477)
                  ·
                    refine ⟨1492246669257400025484913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31834595610824533877011477 1492246669257400025484913)
                    ·
                      refine ⟨1119185001943050019113685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492246669257400025484913 1119185001943050019113685)
                      ·
                        rfl

theorem cell23_2179605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_2179605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179605 prefixEnd_2179605 := by exact prefixLift 2179605
  have htrace : WordTrace (prefixWord ++ tailWord_2179605) baseStart_2179605 baseEnd_2179605 := by
    simpa [prefixWord, tailWord_2179605, baseEnd_2179605] using wordTrace_append hprefix tailTrace_2179605
  have hstable : (prefixWord ++ tailWord_2179605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179605).length < 2 ^ (prefixWord ++ tailWord_2179605).sum := by decide
  have hdescent : baseEnd_2179605 < baseStart_2179605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179645 : List Nat := [1, 4, 1, 3, 2, 2, 2, 8]
def baseStart_2179645 : Nat := 118140960795 + 2179645 * 2 ^ 59
def prefixEnd_2179645 : Nat := 4983230072969 + 3 ^ 40 * 2179645 * 2
def baseEnd_2179645 : Nat := 41452057080341846763463

theorem tailTrace_2179645 : CollatzResearch.WordTrace tailWord_2179645 prefixEnd_2179645 41452057080341846763463 := by
  unfold tailWord_2179645
  simp only [CollatzResearch.WordTrace]
  refine ⟨79498184188525893574476389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52998789459017262382984259 79498184188525893574476389)
  ·
    refine ⟨14905909535348605045214323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79498184188525893574476389 14905909535348605045214323)
    ·
      refine ⟨22358864303022907567821485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14905909535348605045214323 22358864303022907567821485)
      ·
        refine ⟨8384574113633590337933057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22358864303022907567821485 8384574113633590337933057)
        ·
          refine ⟨6288430585225192753449793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8384574113633590337933057 6288430585225192753449793)
          ·
            refine ⟨4716322938918894565087345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6288430585225192753449793 4716322938918894565087345)
            ·
              refine ⟨3537242204189170923815509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4716322938918894565087345 3537242204189170923815509)
              ·
                refine ⟨41452057080341846763463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3537242204189170923815509 41452057080341846763463)
                ·
                  rfl

theorem cell23_2179645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 8].length) (baseStart_2179645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179645 prefixEnd_2179645 := by exact prefixLift 2179645
  have htrace : WordTrace (prefixWord ++ tailWord_2179645) baseStart_2179645 baseEnd_2179645 := by
    simpa [prefixWord, tailWord_2179645, baseEnd_2179645] using wordTrace_append hprefix tailTrace_2179645
  have hstable : (prefixWord ++ tailWord_2179645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179645).length < 2 ^ (prefixWord ++ tailWord_2179645).sum := by decide
  have hdescent : baseEnd_2179645 < baseStart_2179645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179649 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2179649 : Nat := 118140960795 + 2179649 * 2 ^ 59
def prefixEnd_2179649 : Nat := 4983230072969 + 3 ^ 40 * 2179649 * 2
def baseEnd_2179649 : Nat := 373069198363949282321161

theorem tailTrace_2179649 : CollatzResearch.WordTrace tailWord_2179649 prefixEnd_2179649 373069198363949282321161 := by
  unfold tailWord_2179649
  simp only [CollatzResearch.WordTrace]
  refine ⟨79498330080511402257622001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52998886720340934838414667 79498330080511402257622001)
  ·
    refine ⟨59623747560383551693216501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79498330080511402257622001 59623747560383551693216501)
    ·
      refine ⟨5589726333785957971239047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59623747560383551693216501 5589726333785957971239047)
      ·
        refine ⟨8384589500678936956858571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589726333785957971239047 8384589500678936956858571)
        ·
          refine ⟨12576884251018405435287857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384589500678936956858571 12576884251018405435287857)
          ·
            refine ⟨9432663188263804076465893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12576884251018405435287857 9432663188263804076465893)
            ·
              refine ⟨1768624347799463264337355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9432663188263804076465893 1768624347799463264337355)
              ·
                refine ⟨2652936521699194896506033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768624347799463264337355 2652936521699194896506033)
                ·
                  refine ⟨1989702391274396172379525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2652936521699194896506033 1989702391274396172379525)
                  ·
                    refine ⟨373069198363949282321161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1989702391274396172379525 373069198363949282321161)
                    ·
                      rfl

theorem cell23_2179649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2179649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179649 prefixEnd_2179649 := by exact prefixLift 2179649
  have htrace : WordTrace (prefixWord ++ tailWord_2179649) baseStart_2179649 baseEnd_2179649 := by
    simpa [prefixWord, tailWord_2179649, baseEnd_2179649] using wordTrace_append hprefix tailTrace_2179649
  have hstable : (prefixWord ++ tailWord_2179649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179649).length < 2 ^ (prefixWord ++ tailWord_2179649).sum := by decide
  have hdescent : baseEnd_2179649 < baseStart_2179649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179676 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_2179676 : Nat := 118140960795 + 2179676 * 2 ^ 59
def prefixEnd_2179676 : Nat := 4983230072969 + 3 ^ 40 * 2179676 * 2
def baseEnd_2179676 : Nat := 1119221459069519241325859

theorem tailTrace_2179676 : CollatzResearch.WordTrace tailWord_2179676 prefixEnd_2179676 1119221459069519241325859 := by
  unfold tailWord_2179676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39749657425706792934427441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52999543234275723912569921 39749657425706792934427441)
  ·
    refine ⟨29812243069280094700820581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39749657425706792934427441 29812243069280094700820581)
    ·
      refine ⟨5589795575490017756403859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29812243069280094700820581 5589795575490017756403859)
      ·
        refine ⟨8384693363235026634605789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589795575490017756403859 8384693363235026634605789)
        ·
          refine ⟨3144260011213134987977171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8384693363235026634605789 3144260011213134987977171)
          ·
            refine ⟨4716390016819702481965757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144260011213134987977171 4716390016819702481965757)
            ·
              refine ⟨1768646256307388430737159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4716390016819702481965757 1768646256307388430737159)
              ·
                refine ⟨2652969384461082646105739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768646256307388430737159 2652969384461082646105739)
                ·
                  refine ⟨3979454076691623969158609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652969384461082646105739 3979454076691623969158609)
                  ·
                    refine ⟨2984590557518717976868957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3979454076691623969158609 2984590557518717976868957)
                    ·
                      refine ⟨1119221459069519241325859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2984590557518717976868957 1119221459069519241325859)
                      ·
                        rfl

theorem cell23_2179676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_2179676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179676 prefixEnd_2179676 := by exact prefixLift 2179676
  have htrace : WordTrace (prefixWord ++ tailWord_2179676) baseStart_2179676 baseEnd_2179676 := by
    simpa [prefixWord, tailWord_2179676, baseEnd_2179676] using wordTrace_append hprefix tailTrace_2179676
  have hstable : (prefixWord ++ tailWord_2179676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179676).length < 2 ^ (prefixWord ++ tailWord_2179676).sum := by decide
  have hdescent : baseEnd_2179676 < baseStart_2179676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179705 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_2179705 : Nat := 118140960795 + 2179705 * 2 ^ 59
def prefixEnd_2179705 : Nat := 4983230072969 + 3 ^ 40 * 2179705 * 2
def baseEnd_2179705 : Nat := 373078783336166542621075

theorem tailTrace_2179705 : CollatzResearch.WordTrace tailWord_2179705 prefixEnd_2179705 373078783336166542621075 := by
  unfold tailWord_2179705
  simp only [CollatzResearch.WordTrace]
  refine ⟨79500372568308523821660569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53000248378872349214440379 79500372568308523821660569)
  ·
    refine ⟨59625279426231392866245427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79500372568308523821660569 59625279426231392866245427)
    ·
      refine ⟨89437919139347089299368141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59625279426231392866245427 89437919139347089299368141)
      ·
        refine ⟨33539219677255158487263053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89437919139347089299368141 33539219677255158487263053)
        ·
          refine ⟨12577207378970684432723645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33539219677255158487263053 12577207378970684432723645)
          ·
            refine ⟨4716452767114006662271367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12577207378970684432723645 4716452767114006662271367)
            ·
              refine ⟨7074679150671009993407051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716452767114006662271367 7074679150671009993407051)
              ·
                refine ⟨10612018726006514990110577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074679150671009993407051 10612018726006514990110577)
                ·
                  refine ⟨7959014044504886242582933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10612018726006514990110577 7959014044504886242582933)
                  ·
                    refine ⟨373078783336166542621075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7959014044504886242582933 373078783336166542621075)
                    ·
                      rfl

theorem cell23_2179705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_2179705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179705 prefixEnd_2179705 := by exact prefixLift 2179705
  have htrace : WordTrace (prefixWord ++ tailWord_2179705) baseStart_2179705 baseEnd_2179705 := by
    simpa [prefixWord, tailWord_2179705, baseEnd_2179705] using wordTrace_append hprefix tailTrace_2179705
  have hstable : (prefixWord ++ tailWord_2179705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179705).length < 2 ^ (prefixWord ++ tailWord_2179705).sum := by decide
  have hdescent : baseEnd_2179705 < baseStart_2179705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179712 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2]
def baseStart_2179712 : Nat := 118140960795 + 2179712 * 2 ^ 59
def prefixEnd_2179712 : Nat := 4983230072969 + 3 ^ 40 * 2179712 * 2
def baseEnd_2179712 : Nat := 1119239944373081100475693

theorem tailTrace_2179712 : CollatzResearch.WordTrace tailWord_2179712 prefixEnd_2179712 1119239944373081100475693 := by
  unfold tailWord_2179712
  simp only [CollatzResearch.WordTrace]
  refine ⟨39750313939641582008582695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53000418586188776011443593 39750313939641582008582695)
  ·
    refine ⟨59625470909462373012874043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39750313939641582008582695 59625470909462373012874043)
    ·
      refine ⟨89438206364193559519311065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59625470909462373012874043 89438206364193559519311065)
      ·
        refine ⟨67078654773145169639483299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89438206364193559519311065 67078654773145169639483299)
        ·
          refine ⟨100617982159717754459224949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67078654773145169639483299 100617982159717754459224949)
          ·
            refine ⟨9432935827473539480552339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100617982159717754459224949 9432935827473539480552339)
            ·
              refine ⟨14149403741210309220828509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9432935827473539480552339 14149403741210309220828509)
              ·
                refine ⟨5306026402953865957810691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14149403741210309220828509 5306026402953865957810691)
                ·
                  refine ⟨7959039604430798936716037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5306026402953865957810691 7959039604430798936716037)
                  ·
                    refine ⟨1492319925830774800634257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7959039604430798936716037 1492319925830774800634257)
                    ·
                      refine ⟨1119239944373081100475693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492319925830774800634257 1119239944373081100475693)
                      ·
                        rfl

theorem cell23_2179712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_2179712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179712 prefixEnd_2179712 := by exact prefixLift 2179712
  have htrace : WordTrace (prefixWord ++ tailWord_2179712) baseStart_2179712 baseEnd_2179712 := by
    simpa [prefixWord, tailWord_2179712, baseEnd_2179712] using wordTrace_append hprefix tailTrace_2179712
  have hstable : (prefixWord ++ tailWord_2179712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179712).length < 2 ^ (prefixWord ++ tailWord_2179712).sum := by decide
  have hdescent : baseEnd_2179712 < baseStart_2179712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179728 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_2179728 : Nat := 118140960795 + 2179728 * 2 ^ 59
def prefixEnd_2179728 : Nat := 4983230072969 + 3 ^ 40 * 2179728 * 2
def baseEnd_2179728 : Nat := 1119248160063553037875619

theorem tailTrace_2179728 : CollatzResearch.WordTrace tailWord_2179728 prefixEnd_2179728 1119248160063553037875619 := by
  unfold tailWord_2179728
  simp only [CollatzResearch.WordTrace]
  refine ⟨39750605723612599374873919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53000807631483465833165225 39750605723612599374873919)
  ·
    refine ⟨59625908585418899062310879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39750605723612599374873919 59625908585418899062310879)
    ·
      refine ⟨89438862878128348593466319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59625908585418899062310879 89438862878128348593466319)
      ·
        refine ⟨134158294317192522890199479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89438862878128348593466319 134158294317192522890199479)
        ·
          refine ⟨201237441475788784335299219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134158294317192522890199479 201237441475788784335299219)
          ·
            refine ⟨301856162213683176502948829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201237441475788784335299219 301856162213683176502948829)
            ·
              refine ⟨113196060830131191188605811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301856162213683176502948829 113196060830131191188605811)
              ·
                refine ⟨169794091245196786782908717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113196060830131191188605811 169794091245196786782908717)
                ·
                  refine ⟨63672784216948795043590769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169794091245196786782908717 63672784216948795043590769)
                  ·
                    refine ⟨47754588162711596282693077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63672784216948795043590769 47754588162711596282693077)
                    ·
                      refine ⟨1119248160063553037875619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47754588162711596282693077 1119248160063553037875619)
                      ·
                        rfl

theorem cell23_2179728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_2179728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179728 prefixEnd_2179728 := by exact prefixLift 2179728
  have htrace : WordTrace (prefixWord ++ tailWord_2179728) baseStart_2179728 baseEnd_2179728 := by
    simpa [prefixWord, tailWord_2179728, baseEnd_2179728] using wordTrace_append hprefix tailTrace_2179728
  have hstable : (prefixWord ++ tailWord_2179728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179728).length < 2 ^ (prefixWord ++ tailWord_2179728).sum := by decide
  have hdescent : baseEnd_2179728 < baseStart_2179728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179742 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2179742 : Nat := 118140960795 + 2179742 * 2 ^ 59
def prefixEnd_2179742 : Nat := 4983230072969 + 3 ^ 40 * 2179742 * 2
def baseEnd_2179742 : Nat := 1119255348792715983100555

theorem tailTrace_2179742 : CollatzResearch.WordTrace tailWord_2179742 prefixEnd_2179742 1119255348792715983100555 := by
  unfold tailWord_2179742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9937715258646809892594685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53001148046116319427171653 9937715258646809892594685)
  ·
    refine ⟨3726643221992553709723007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9937715258646809892594685 3726643221992553709723007)
    ·
      refine ⟨5589964832988830564584511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726643221992553709723007 5589964832988830564584511)
      ·
        refine ⟨8384947249483245846876767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589964832988830564584511 8384947249483245846876767)
        ·
          refine ⟨12577420874224868770315151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384947249483245846876767 12577420874224868770315151)
          ·
            refine ⟨18866131311337303155472727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577420874224868770315151 18866131311337303155472727)
            ·
              refine ⟨28299196967005954733209091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18866131311337303155472727 28299196967005954733209091)
              ·
                refine ⟨42448795450508932099813637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28299196967005954733209091 42448795450508932099813637)
                ·
                  refine ⟨7959149146970424768715057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42448795450508932099813637 7959149146970424768715057)
                  ·
                    refine ⟨5969361860227818576536293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7959149146970424768715057 5969361860227818576536293)
                    ·
                      refine ⟨1119255348792715983100555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5969361860227818576536293 1119255348792715983100555)
                      ·
                        rfl

theorem cell23_2179742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2179742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179742 prefixEnd_2179742 := by exact prefixLift 2179742
  have htrace : WordTrace (prefixWord ++ tailWord_2179742) baseStart_2179742 baseEnd_2179742 := by
    simpa [prefixWord, tailWord_2179742, baseEnd_2179742] using wordTrace_append hprefix tailTrace_2179742
  have hstable : (prefixWord ++ tailWord_2179742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179742).length < 2 ^ (prefixWord ++ tailWord_2179742).sum := by decide
  have hdescent : baseEnd_2179742 < baseStart_2179742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179785 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_2179785 : Nat := 118140960795 + 2179785 * 2 ^ 59
def prefixEnd_2179785 : Nat := 4983230072969 + 3 ^ 40 * 2179785 * 2
def baseEnd_2179785 : Nat := 1119277428460859314862857

theorem tailTrace_2179785 : CollatzResearch.WordTrace tailWord_2179785 prefixEnd_2179785 1119277428460859314862857 := by
  unfold tailWord_2179785
  simp only [CollatzResearch.WordTrace]
  refine ⟨79503290408018697484572809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53002193605345798323048539 79503290408018697484572809)
  ·
    refine ⟨59627467806014023113429607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79503290408018697484572809 59627467806014023113429607)
    ·
      refine ⟨89441201709021034670144411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59627467806014023113429607 89441201709021034670144411)
      ·
        refine ⟨134161802563531552005216617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89441201709021034670144411 134161802563531552005216617)
        ·
          refine ⟨100621351922648664003912463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134161802563531552005216617 100621351922648664003912463)
          ·
            refine ⟨150932027883972996005868695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100621351922648664003912463 150932027883972996005868695)
            ·
              refine ⟨226398041825959494008803043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150932027883972996005868695 226398041825959494008803043)
              ·
                refine ⟨339597062738939241013204565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226398041825959494008803043 339597062738939241013204565)
                ·
                  refine ⟨3979653078971944230623491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 339597062738939241013204565 3979653078971944230623491)
                  ·
                    refine ⟨5969479618457916345935237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979653078971944230623491 5969479618457916345935237)
                    ·
                      refine ⟨1119277428460859314862857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5969479618457916345935237 1119277428460859314862857)
                      ·
                        rfl

theorem cell23_2179785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_2179785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179785 prefixEnd_2179785 := by exact prefixLift 2179785
  have htrace : WordTrace (prefixWord ++ tailWord_2179785) baseStart_2179785 baseEnd_2179785 := by
    simpa [prefixWord, tailWord_2179785, baseEnd_2179785] using wordTrace_append hprefix tailTrace_2179785
  have hstable : (prefixWord ++ tailWord_2179785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179785).length < 2 ^ (prefixWord ++ tailWord_2179785).sum := by decide
  have hdescent : baseEnd_2179785 < baseStart_2179785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179802 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_2179802 : Nat := 118140960795 + 2179802 * 2 ^ 59
def prefixEnd_2179802 : Nat := 4983230072969 + 3 ^ 40 * 2179802 * 2
def baseEnd_2179802 : Nat := 1119286157631985748350279

theorem tailTrace_2179802 : CollatzResearch.WordTrace tailWord_2179802 prefixEnd_2179802 1119286157631985748350279 := by
  unfold tailWord_2179802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19875977612239277346985415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53002606965971406258627773 19875977612239277346985415)
  ·
    refine ⟨29813966418358916020478123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19875977612239277346985415 29813966418358916020478123)
    ·
      refine ⟨44720949627538374030717185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29813966418358916020478123 44720949627538374030717185)
      ·
        refine ⟨33540712220653780523037889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44720949627538374030717185 33540712220653780523037889)
        ·
          refine ⟨25155534165490335392278417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33540712220653780523037889 25155534165490335392278417)
          ·
            refine ⟨18866650624117751544208813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25155534165490335392278417 18866650624117751544208813)
            ·
              refine ⟨7074993984044156829078305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18866650624117751544208813 7074993984044156829078305)
              ·
                refine ⟨5306245488033117621808729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7074993984044156829078305 5306245488033117621808729)
                ·
                  refine ⟨3979684116024838216356547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306245488033117621808729 3979684116024838216356547)
                  ·
                    refine ⟨5969526174037257324534821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979684116024838216356547 5969526174037257324534821)
                    ·
                      refine ⟨1119286157631985748350279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5969526174037257324534821 1119286157631985748350279)
                      ·
                        rfl

theorem cell23_2179802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_2179802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179802 prefixEnd_2179802 := by exact prefixLift 2179802
  have htrace : WordTrace (prefixWord ++ tailWord_2179802) baseStart_2179802 baseEnd_2179802 := by
    simpa [prefixWord, tailWord_2179802, baseEnd_2179802] using wordTrace_append hprefix tailTrace_2179802
  have hstable : (prefixWord ++ tailWord_2179802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179802).length < 2 ^ (prefixWord ++ tailWord_2179802).sum := by decide
  have hdescent : baseEnd_2179802 < baseStart_2179802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179872 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_2179872 : Nat := 118140960795 + 2179872 * 2 ^ 59
def prefixEnd_2179872 : Nat := 4983230072969 + 3 ^ 40 * 2179872 * 2
def baseEnd_2179872 : Nat := 373107367092600158158319

theorem tailTrace_2179872 : CollatzResearch.WordTrace tailWord_2179872 prefixEnd_2179872 373107367092600158158319 := by
  unfold tailWord_2179872
  simp only [CollatzResearch.WordTrace]
  refine ⟨39753231779351755671494935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53004309039135674228659913 39753231779351755671494935)
  ·
    refine ⟨59629847669027633507242403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39753231779351755671494935 59629847669027633507242403)
    ·
      refine ⟨89444771503541450260863605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59629847669027633507242403 89444771503541450260863605)
      ·
        refine ⟨8385447328457010961955963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89444771503541450260863605 8385447328457010961955963)
        ·
          refine ⟨12578170992685516442933945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8385447328457010961955963 12578170992685516442933945)
          ·
            refine ⟨9433628244514137332200459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12578170992685516442933945 9433628244514137332200459)
            ·
              refine ⟨14150442366771205998300689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9433628244514137332200459 14150442366771205998300689)
              ·
                refine ⟨10612831775078404498725517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14150442366771205998300689 10612831775078404498725517)
                ·
                  refine ⟨3979811915654401687022069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10612831775078404498725517 3979811915654401687022069)
                  ·
                    refine ⟨373107367092600158158319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3979811915654401687022069 373107367092600158158319)
                    ·
                      rfl

theorem cell23_2179872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_2179872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179872 prefixEnd_2179872 := by exact prefixLift 2179872
  have htrace : WordTrace (prefixWord ++ tailWord_2179872) baseStart_2179872 baseEnd_2179872 := by
    simpa [prefixWord, tailWord_2179872, baseEnd_2179872] using wordTrace_append hprefix tailTrace_2179872
  have hstable : (prefixWord ++ tailWord_2179872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179872).length < 2 ^ (prefixWord ++ tailWord_2179872).sum := by decide
  have hdescent : baseEnd_2179872 < baseStart_2179872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179886 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2179886 : Nat := 118140960795 + 2179886 * 2 ^ 59
def prefixEnd_2179886 : Nat := 4983230072969 + 3 ^ 40 * 2179886 * 2
def baseEnd_2179886 : Nat := 1119329290006963419699893

theorem tailTrace_2179886 : CollatzResearch.WordTrace tailWord_2179886 prefixEnd_2179886 1119329290006963419699893 := by
  unfold tailWord_2179886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938371772581598966749939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53004649453768527822666341 9938371772581598966749939)
  ·
    refine ⟨14907557658872398450124909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9938371772581598966749939 14907557658872398450124909)
    ·
      refine ⟨5590334122077149418796841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14907557658872398450124909 5590334122077149418796841)
      ·
        refine ⟨4192750591557862064097631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5590334122077149418796841 4192750591557862064097631)
        ·
          refine ⟨6289125887336793096146447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192750591557862064097631 6289125887336793096146447)
          ·
            refine ⟨9433688831005189644219671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289125887336793096146447 9433688831005189644219671)
            ·
              refine ⟨14150533246507784466329507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9433688831005189644219671 14150533246507784466329507)
              ·
                refine ⟨21225799869761676699494261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14150533246507784466329507 21225799869761676699494261)
                ·
                  refine ⟨1989918737790157190577587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21225799869761676699494261 1989918737790157190577587)
                  ·
                    refine ⟨2984878106685235785866381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1989918737790157190577587 2984878106685235785866381)
                    ·
                      refine ⟨1119329290006963419699893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2984878106685235785866381 1119329290006963419699893)
                      ·
                        rfl

theorem cell23_2179886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2179886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179886 prefixEnd_2179886 := by exact prefixLift 2179886
  have htrace : WordTrace (prefixWord ++ tailWord_2179886) baseStart_2179886 baseEnd_2179886 := by
    simpa [prefixWord, tailWord_2179886, baseEnd_2179886] using wordTrace_append hprefix tailTrace_2179886
  have hstable : (prefixWord ++ tailWord_2179886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179886).length < 2 ^ (prefixWord ++ tailWord_2179886).sum := by decide
  have hdescent : baseEnd_2179886 < baseStart_2179886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179903 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 1, 1, 3]
def baseStart_2179903 : Nat := 118140960795 + 2179903 * 2 ^ 59
def prefixEnd_2179903 : Nat := 4983230072969 + 3 ^ 40 * 2179903 * 2
def baseEnd_2179903 : Nat := 1119338019178089853187315

theorem tailTrace_2179903 : CollatzResearch.WordTrace tailWord_2179903 prefixEnd_2179903 1119338019178089853187315 := by
  unfold tailWord_2179903
  simp only [CollatzResearch.WordTrace]
  refine ⟨79507594221591203637368363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53005062814394135758245575 79507594221591203637368363)
  ·
    refine ⟨119261391332386805456052545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79507594221591203637368363 119261391332386805456052545)
    ·
      refine ⟨89446043499290104092039409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119261391332386805456052545 89446043499290104092039409)
      ·
        refine ⟨67084532624467578069029557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89446043499290104092039409 67084532624467578069029557)
        ·
          refine ⟨6289174933543835443971521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67084532624467578069029557 6289174933543835443971521)
          ·
            refine ⟨4716881200157876582978641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6289174933543835443971521 4716881200157876582978641)
            ·
              refine ⟨3537660900118407437233981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4716881200157876582978641 3537660900118407437233981)
              ·
                refine ⟨1326622837544402788962743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3537660900118407437233981 1326622837544402788962743)
                ·
                  refine ⟨1989934256316604183444115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326622837544402788962743 1989934256316604183444115)
                  ·
                    refine ⟨2984901384474906275166173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1989934256316604183444115 2984901384474906275166173)
                    ·
                      refine ⟨1119338019178089853187315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2984901384474906275166173 1119338019178089853187315)
                      ·
                        rfl

theorem cell23_2179903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_2179903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179903 prefixEnd_2179903 := by exact prefixLift 2179903
  have htrace : WordTrace (prefixWord ++ tailWord_2179903) baseStart_2179903 baseEnd_2179903 := by
    simpa [prefixWord, tailWord_2179903, baseEnd_2179903] using wordTrace_append hprefix tailTrace_2179903
  have hstable : (prefixWord ++ tailWord_2179903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179903).length < 2 ^ (prefixWord ++ tailWord_2179903).sum := by decide
  have hdescent : baseEnd_2179903 < baseStart_2179903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179910 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_2179910 : Nat := 118140960795 + 2179910 * 2 ^ 59
def prefixEnd_2179910 : Nat := 4983230072969 + 3 ^ 40 * 2179910 * 2
def baseEnd_2179910 : Nat := 124371290393630147311087

theorem tailTrace_2179910 : CollatzResearch.WordTrace tailWord_2179910 prefixEnd_2179910 124371290393630147311087 := by
  unfold tailWord_2179910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484620297892682619777287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53005233021710562555248789 2484620297892682619777287)
  ·
    refine ⟨3726930446839023929665931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484620297892682619777287 3726930446839023929665931)
    ·
      refine ⟨5590395670258535894498897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726930446839023929665931 5590395670258535894498897)
      ·
        refine ⟨4192796752693901920874173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5590395670258535894498897 4192796752693901920874173)
        ·
          refine ⟨1572298782260213220327815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4192796752693901920874173 1572298782260213220327815)
          ·
            refine ⟨2358448173390319830491723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572298782260213220327815 2358448173390319830491723)
            ·
              refine ⟨3537672260085479745737585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358448173390319830491723 3537672260085479745737585)
              ·
                refine ⟨2653254195064109809303189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3537672260085479745737585 2653254195064109809303189)
                ·
                  refine ⟨124371290393630147311087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2653254195064109809303189 124371290393630147311087)
                  ·
                    rfl

theorem cell23_2179910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_2179910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179910 prefixEnd_2179910 := by exact prefixLift 2179910
  have htrace : WordTrace (prefixWord ++ tailWord_2179910) baseStart_2179910 baseEnd_2179910 := by
    simpa [prefixWord, tailWord_2179910, baseEnd_2179910] using wordTrace_append hprefix tailTrace_2179910
  have hstable : (prefixWord ++ tailWord_2179910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179910).length < 2 ^ (prefixWord ++ tailWord_2179910).sum := by decide
  have hdescent : baseEnd_2179910 < baseStart_2179910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179912 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2179912 : Nat := 118140960795 + 2179912 * 2 ^ 59
def prefixEnd_2179912 : Nat := 4983230072969 + 3 ^ 40 * 2179912 * 2
def baseEnd_2179912 : Nat := 1119342640503980317974773

theorem tailTrace_2179912 : CollatzResearch.WordTrace tailWord_2179912 prefixEnd_2179912 1119342640503980317974773 := by
  unfold tailWord_2179912
  simp only [CollatzResearch.WordTrace]
  refine ⟨39753961239279299087222995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53005281652372398782963993 39753961239279299087222995)
  ·
    refine ⟨59630941858918948630834493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39753961239279299087222995 59630941858918948630834493)
    ·
      refine ⟨22361603197094605736562935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59630941858918948630834493 22361603197094605736562935)
      ·
        refine ⟨33542404795641908604844403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22361603197094605736562935 33542404795641908604844403)
        ·
          refine ⟨50313607193462862907266605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33542404795641908604844403 50313607193462862907266605)
          ·
            refine ⟨18867602697548573590224977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50313607193462862907266605 18867602697548573590224977)
            ·
              refine ⟨14150702023161430192668733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18867602697548573590224977 14150702023161430192668733)
              ·
                refine ⟨5306513258685536322250775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14150702023161430192668733 5306513258685536322250775)
                ·
                  refine ⟨7959769888028304483376163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5306513258685536322250775 7959769888028304483376163)
                  ·
                    refine ⟨11939654832042456725064245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7959769888028304483376163 11939654832042456725064245)
                    ·
                      refine ⟨1119342640503980317974773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11939654832042456725064245 1119342640503980317974773)
                      ·
                        rfl

theorem cell23_2179912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2179912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179912 prefixEnd_2179912 := by exact prefixLift 2179912
  have htrace : WordTrace (prefixWord ++ tailWord_2179912) baseStart_2179912 baseEnd_2179912 := by
    simpa [prefixWord, tailWord_2179912, baseEnd_2179912] using wordTrace_append hprefix tailTrace_2179912
  have hstable : (prefixWord ++ tailWord_2179912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179912).length < 2 ^ (prefixWord ++ tailWord_2179912).sum := by decide
  have hdescent : baseEnd_2179912 < baseStart_2179912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179922 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2179922 : Nat := 118140960795 + 2179922 * 2 ^ 59
def prefixEnd_2179922 : Nat := 4983230072969 + 3 ^ 40 * 2179922 * 2
def baseEnd_2179922 : Nat := 1119347775310525278849727

theorem tailTrace_2179922 : CollatzResearch.WordTrace tailWord_2179922 prefixEnd_2179922 1119347775310525278849727 := by
  unfold tailWord_2179922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19877071802130592470577505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53005524805681579921540013 19877071802130592470577505)
  ·
    refine ⟨14907803851597944352933129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19877071802130592470577505 14907803851597944352933129)
    ·
      refine ⟨11180852888698458264699847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14907803851597944352933129 11180852888698458264699847)
      ·
        refine ⟨16771279333047687397049771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11180852888698458264699847 16771279333047687397049771)
        ·
          refine ⟨25156918999571531095574657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16771279333047687397049771 25156918999571531095574657)
          ·
            refine ⟨18867689249678648321680993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25156918999571531095574657 18867689249678648321680993)
            ·
              refine ⟨14150766937258986241260745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18867689249678648321680993 14150766937258986241260745)
              ·
                refine ⟨10613075202944239680945559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14150766937258986241260745 10613075202944239680945559)
                ·
                  refine ⟨15919612804416359521418339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10613075202944239680945559 15919612804416359521418339)
                  ·
                    refine ⟨23879419206624539282127509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15919612804416359521418339 23879419206624539282127509)
                    ·
                      refine ⟨1119347775310525278849727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23879419206624539282127509 1119347775310525278849727)
                      ·
                        rfl

theorem cell23_2179922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2179922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179922 prefixEnd_2179922 := by exact prefixLift 2179922
  have htrace : WordTrace (prefixWord ++ tailWord_2179922) baseStart_2179922 baseEnd_2179922 := by
    simpa [prefixWord, tailWord_2179922, baseEnd_2179922] using wordTrace_append hprefix tailTrace_2179922
  have hstable : (prefixWord ++ tailWord_2179922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179922).length < 2 ^ (prefixWord ++ tailWord_2179922).sum := by decide
  have hdescent : baseEnd_2179922 < baseStart_2179922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179936 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 2, 4]
def baseStart_2179936 : Nat := 118140960795 + 2179936 * 2 ^ 59
def prefixEnd_2179936 : Nat := 4983230072969 + 3 ^ 40 * 2179936 * 2
def baseEnd_2179936 : Nat := 373118321346562741358221

theorem tailTrace_2179936 : CollatzResearch.WordTrace tailWord_2179936 prefixEnd_2179936 373118321346562741358221 := by
  unfold tailWord_2179936
  simp only [CollatzResearch.WordTrace]
  refine ⟨39754398915235825136659831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53005865220314433515546441 39754398915235825136659831)
  ·
    refine ⟨59631598372853737704989747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39754398915235825136659831 59631598372853737704989747)
    ·
      refine ⟨89447397559280606557484621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59631598372853737704989747 89447397559280606557484621)
      ·
        refine ⟨33542774084730227459056733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89447397559280606557484621 33542774084730227459056733)
        ·
          refine ⟨12578540281773835297146275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33542774084730227459056733 12578540281773835297146275)
          ·
            refine ⟨18867810422660752945719413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12578540281773835297146275 18867810422660752945719413)
            ·
              refine ⟨1768857227124445588661195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18867810422660752945719413 1768857227124445588661195)
              ·
                refine ⟨2653285840686668382991793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768857227124445588661195 2653285840686668382991793)
                ·
                  refine ⟨1989964380515001287243845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2653285840686668382991793 1989964380515001287243845)
                  ·
                    refine ⟨373118321346562741358221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1989964380515001287243845 373118321346562741358221)
                    ·
                      rfl

theorem cell23_2179936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_2179936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179936 prefixEnd_2179936 := by exact prefixLift 2179936
  have htrace : WordTrace (prefixWord ++ tailWord_2179936) baseStart_2179936 baseEnd_2179936 := by
    simpa [prefixWord, tailWord_2179936, baseEnd_2179936] using wordTrace_append hprefix tailTrace_2179936
  have hstable : (prefixWord ++ tailWord_2179936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179936).length < 2 ^ (prefixWord ++ tailWord_2179936).sum := by decide
  have hdescent : baseEnd_2179936 < baseStart_2179936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179939 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2179939 : Nat := 118140960795 + 2179939 * 2 ^ 59
def prefixEnd_2179939 : Nat := 4983230072969 + 3 ^ 40 * 2179939 * 2
def baseEnd_2179939 : Nat := 1119356504481651712337149

theorem tailTrace_2179939 : CollatzResearch.WordTrace tailWord_2179939 prefixEnd_2179939 1119356504481651712337149 := by
  unfold tailWord_2179939
  simp only [CollatzResearch.WordTrace]
  refine ⟨79508907249460781785678871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53005938166307187857119247 79508907249460781785678871)
  ·
    refine ⟨119263360874191172678518307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79508907249460781785678871 119263360874191172678518307)
    ·
      refine ⟨178895041311286759017777461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119263360874191172678518307 178895041311286759017777461)
      ·
        refine ⟨16771410122933133657916637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178895041311286759017777461 16771410122933133657916637)
        ·
          refine ⟨6289278796099925121718739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16771410122933133657916637 6289278796099925121718739)
          ·
            refine ⟨9433918194149887682578109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289278796099925121718739 9433918194149887682578109)
            ·
              refine ⟨3537719322806207880966791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9433918194149887682578109 3537719322806207880966791)
              ·
                refine ⟨5306578984209311821450187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537719322806207880966791 5306578984209311821450187)
                ·
                  refine ⟨7959868476313967732175281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5306578984209311821450187 7959868476313967732175281)
                  ·
                    refine ⟨5969901357235475799131461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7959868476313967732175281 5969901357235475799131461)
                    ·
                      refine ⟨1119356504481651712337149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5969901357235475799131461 1119356504481651712337149)
                      ·
                        rfl

theorem cell23_2179939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2179939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179939 prefixEnd_2179939 := by exact prefixLift 2179939
  have htrace : WordTrace (prefixWord ++ tailWord_2179939) baseStart_2179939 baseEnd_2179939 := by
    simpa [prefixWord, tailWord_2179939, baseEnd_2179939] using wordTrace_append hprefix tailTrace_2179939
  have hstable : (prefixWord ++ tailWord_2179939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179939).length < 2 ^ (prefixWord ++ tailWord_2179939).sum := by decide
  have hdescent : baseEnd_2179939 < baseStart_2179939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179966 : List Nat := [4, 2, 3, 1, 2, 2, 9]
def baseStart_2179966 : Nat := 118140960795 + 2179966 * 2 ^ 59
def prefixEnd_2179966 : Nat := 4983230072969 + 3 ^ 40 * 2179966 * 2
def baseEnd_2179966 : Nat := 13819387264929914897525

theorem tailTrace_2179966 : CollatzResearch.WordTrace tailWord_2179966 prefixEnd_2179966 13819387264929914897525 := by
  unfold tailWord_2179966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938736502545370674613969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53006594680241976931274501 9938736502545370674613969)
  ·
    refine ⟨7454052376909028005960477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9938736502545370674613969 7454052376909028005960477)
    ·
      refine ⟨2795269641340885502235179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7454052376909028005960477 2795269641340885502235179)
      ·
        refine ⟨4192904462011328253352769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795269641340885502235179 4192904462011328253352769)
        ·
          refine ⟨3144678346508496190014577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4192904462011328253352769 3144678346508496190014577)
          ·
            refine ⟨2358508759881372142510933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3144678346508496190014577 2358508759881372142510933)
            ·
              refine ⟨13819387264929914897525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2358508759881372142510933 13819387264929914897525)
              ·
                rfl

theorem cell23_2179966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 9].length) (baseStart_2179966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179966 prefixEnd_2179966 := by exact prefixLift 2179966
  have htrace : WordTrace (prefixWord ++ tailWord_2179966) baseStart_2179966 baseEnd_2179966 := by
    simpa [prefixWord, tailWord_2179966, baseEnd_2179966] using wordTrace_append hprefix tailTrace_2179966
  have hstable : (prefixWord ++ tailWord_2179966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179966).length < 2 ^ (prefixWord ++ tailWord_2179966).sum := by decide
  have hdescent : baseEnd_2179966 < baseStart_2179966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179972 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2179972 : Nat := 118140960795 + 2179972 * 2 ^ 59
def prefixEnd_2179972 : Nat := 4983230072969 + 3 ^ 40 * 2179972 * 2
def baseEnd_2179972 : Nat := 1119373449343250083224497

theorem tailTrace_2179972 : CollatzResearch.WordTrace tailWord_2179972 prefixEnd_2179972 1119373449343250083224497 := by
  unfold tailWord_2179972
  simp only [CollatzResearch.WordTrace]
  refine ⟨39755055429170614210815085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53006740572227485614420113 39755055429170614210815085)
  ·
    refine ⟨14908145785938980329055657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39755055429170614210815085 14908145785938980329055657)
    ·
      refine ⟨11181109339454235246791743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14908145785938980329055657 11181109339454235246791743)
      ·
        refine ⟨16771664009181352870187615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11181109339454235246791743 16771664009181352870187615)
        ·
          refine ⟨25157496013772029305281423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16771664009181352870187615 25157496013772029305281423)
          ·
            refine ⟨37736244020658043957922135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25157496013772029305281423 37736244020658043957922135)
            ·
              refine ⟨56604366030987065936883203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37736244020658043957922135 56604366030987065936883203)
              ·
                refine ⟨84906549046480598905324805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56604366030987065936883203 84906549046480598905324805)
                ·
                  refine ⟨15919977946215112294748401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84906549046480598905324805 15919977946215112294748401)
                  ·
                    refine ⟨11939983459661334221061301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15919977946215112294748401 11939983459661334221061301)
                    ·
                      refine ⟨1119373449343250083224497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11939983459661334221061301 1119373449343250083224497)
                      ·
                        rfl

theorem cell23_2179972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2179972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179972 prefixEnd_2179972 := by exact prefixLift 2179972
  have htrace : WordTrace (prefixWord ++ tailWord_2179972) baseStart_2179972 baseEnd_2179972 := by
    simpa [prefixWord, tailWord_2179972, baseEnd_2179972] using wordTrace_append hprefix tailTrace_2179972
  have hstable : (prefixWord ++ tailWord_2179972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179972).length < 2 ^ (prefixWord ++ tailWord_2179972).sum := by decide
  have hdescent : baseEnd_2179972 < baseStart_2179972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179976 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2179976 : Nat := 118140960795 + 2179976 * 2 ^ 59
def prefixEnd_2179976 : Nat := 4983230072969 + 3 ^ 40 * 2179976 * 2
def baseEnd_2179976 : Nat := 1119375503265868067574479

theorem tailTrace_2179976 : CollatzResearch.WordTrace tailWord_2179976 prefixEnd_2179976 1119375503265868067574479 := by
  unfold tailWord_2179976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39755128375163368552387891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53006837833551158069850521 39755128375163368552387891)
  ·
    refine ⟨59632692562745052828581837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39755128375163368552387891 59632692562745052828581837)
    ·
      refine ⟨22362259711029394810718189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59632692562745052828581837 22362259711029394810718189)
      ·
        refine ⟨8385847391636023054019321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22362259711029394810718189 8385847391636023054019321)
        ·
          refine ⟨6289385543727017290514491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8385847391636023054019321 6289385543727017290514491)
          ·
            refine ⟨9434078315590525935771737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289385543727017290514491 9434078315590525935771737)
            ·
              refine ⟨7075558736692894451828803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9434078315590525935771737 7075558736692894451828803)
              ·
                refine ⟨10613338105039341677743205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7075558736692894451828803 10613338105039341677743205)
                ·
                  refine ⟨1990000894694876564576851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10613338105039341677743205 1990000894694876564576851)
                  ·
                    refine ⟨2985001342042314846865277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1990000894694876564576851 2985001342042314846865277)
                    ·
                      refine ⟨1119375503265868067574479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2985001342042314846865277 1119375503265868067574479)
                      ·
                        rfl

theorem cell23_2179976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2179976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2179976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2179976 prefixEnd_2179976 := by exact prefixLift 2179976
  have htrace : WordTrace (prefixWord ++ tailWord_2179976) baseStart_2179976 baseEnd_2179976 := by
    simpa [prefixWord, tailWord_2179976, baseEnd_2179976] using wordTrace_append hprefix tailTrace_2179976
  have hstable : (prefixWord ++ tailWord_2179976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179976).length < 2 ^ (prefixWord ++ tailWord_2179976).sum := by decide
  have hdescent : baseEnd_2179976 < baseStart_2179976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180012 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_2180012 : Nat := 118140960795 + 2180012 * 2 ^ 59
def prefixEnd_2180012 : Nat := 4983230072969 + 3 ^ 40 * 2180012 * 2
def baseEnd_2180012 : Nat := 1119393988569429926724313

theorem tailTrace_2180012 : CollatzResearch.WordTrace tailWord_2180012 prefixEnd_2180012 1119393988569429926724313 := by
  unfold tailWord_2180012
  simp only [CollatzResearch.WordTrace]
  refine ⟨39755784889098157626543145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53007713185464210168724193 39755784889098157626543145)
  ·
    refine ⟨29816838666823618219907359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39755784889098157626543145 29816838666823618219907359)
    ·
      refine ⟨44725258000235427329861039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29816838666823618219907359 44725258000235427329861039)
      ·
        refine ⟨67087887000353140994791559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44725258000235427329861039 67087887000353140994791559)
        ·
          refine ⟨100631830500529711492187339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67087887000353140994791559 100631830500529711492187339)
          ·
            refine ⟨150947745750794567238281009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100631830500529711492187339 150947745750794567238281009)
            ·
              refine ⟨113210809313095925428710757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150947745750794567238281009 113210809313095925428710757)
              ·
                refine ⟨21227026746205486017883267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113210809313095925428710757 21227026746205486017883267)
                ·
                  refine ⟨31840540119308229026824901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21227026746205486017883267 31840540119308229026824901)
                  ·
                    refine ⟨5970101272370292942529669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31840540119308229026824901 5970101272370292942529669)
                    ·
                      refine ⟨1119393988569429926724313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5970101272370292942529669 1119393988569429926724313)
                      ·
                        rfl

theorem cell23_2180012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_2180012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180012 prefixEnd_2180012 := by exact prefixLift 2180012
  have htrace : WordTrace (prefixWord ++ tailWord_2180012) baseStart_2180012 baseEnd_2180012 := by
    simpa [prefixWord, tailWord_2180012, baseEnd_2180012] using wordTrace_append hprefix tailTrace_2180012
  have hstable : (prefixWord ++ tailWord_2180012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180012).length < 2 ^ (prefixWord ++ tailWord_2180012).sum := by decide
  have hdescent : baseEnd_2180012 < baseStart_2180012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180042 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2180042 : Nat := 118140960795 + 2180042 * 2 ^ 59
def prefixEnd_2180042 : Nat := 4983230072969 + 3 ^ 40 * 2180042 * 2
def baseEnd_2180042 : Nat := 1119409392989064809349175

theorem tailTrace_2180042 : CollatzResearch.WordTrace tailWord_2180042 prefixEnd_2180042 1119409392989064809349175 := by
  unfold tailWord_2180042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878165992021907594169595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53008442645391753584452253 19878165992021907594169595)
  ·
    refine ⟨29817248988032861391254393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19878165992021907594169595 29817248988032861391254393)
    ·
      refine ⟨22362936741024646043440795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29817248988032861391254393 22362936741024646043440795)
      ·
        refine ⟨33544405111536969065161193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22362936741024646043440795 33544405111536969065161193)
        ·
          refine ⟨25158303833652726798870895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33544405111536969065161193 25158303833652726798870895)
          ·
            refine ⟨37737455750479090198306343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25158303833652726798870895 37737455750479090198306343)
            ·
              refine ⟨56606183625718635297459515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37737455750479090198306343 56606183625718635297459515)
              ·
                refine ⟨84909275438577952946189273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56606183625718635297459515 84909275438577952946189273)
                ·
                  refine ⟨63681956578933464709641955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84909275438577952946189273 63681956578933464709641955)
                  ·
                    refine ⟨95522934868400197064462933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63681956578933464709641955 95522934868400197064462933)
                    ·
                      refine ⟨1119409392989064809349175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 95522934868400197064462933 1119409392989064809349175)
                      ·
                        rfl

theorem cell23_2180042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2180042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180042 prefixEnd_2180042 := by exact prefixLift 2180042
  have htrace : WordTrace (prefixWord ++ tailWord_2180042) baseStart_2180042 baseEnd_2180042 := by
    simpa [prefixWord, tailWord_2180042, baseEnd_2180042] using wordTrace_append hprefix tailTrace_2180042
  have hstable : (prefixWord ++ tailWord_2180042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180042).length < 2 ^ (prefixWord ++ tailWord_2180042).sum := by decide
  have hdescent : baseEnd_2180042 < baseStart_2180042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180049 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_2180049 : Nat := 118140960795 + 2180049 * 2 ^ 59
def prefixEnd_2180049 : Nat := 4983230072969 + 3 ^ 40 * 2180049 * 2
def baseEnd_2180049 : Nat := 1119412987353646281961643

theorem tailTrace_2180049 : CollatzResearch.WordTrace tailWord_2180049 prefixEnd_2180049 1119412987353646281961643 := by
  unfold tailWord_2180049
  simp only [CollatzResearch.WordTrace]
  refine ⟨79512919279062270572183201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53008612852708180381455467 79512919279062270572183201)
  ·
    refine ⟨59634689459296702929137401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79512919279062270572183201 59634689459296702929137401)
    ·
      refine ⟨44726017094472527196853051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59634689459296702929137401 44726017094472527196853051)
      ·
        refine ⟨67089025641708790795279577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44726017094472527196853051 67089025641708790795279577)
        ·
          refine ⟨50316769231281593096459683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67089025641708790795279577 50316769231281593096459683)
          ·
            refine ⟨75475153846922389644689525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50316769231281593096459683 75475153846922389644689525)
            ·
              refine ⟨7075795673148974029189643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75475153846922389644689525 7075795673148974029189643)
              ·
                refine ⟨10613693509723461043784465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7075795673148974029189643 10613693509723461043784465)
                ·
                  refine ⟨7960270132292595782838349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10613693509723461043784465 7960270132292595782838349)
                  ·
                    refine ⟨2985101299609723418564381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7960270132292595782838349 2985101299609723418564381)
                    ·
                      refine ⟨1119412987353646281961643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2985101299609723418564381 1119412987353646281961643)
                      ·
                        rfl

theorem cell23_2180049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_2180049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180049 prefixEnd_2180049 := by exact prefixLift 2180049
  have htrace : WordTrace (prefixWord ++ tailWord_2180049) baseStart_2180049 baseEnd_2180049 := by
    simpa [prefixWord, tailWord_2180049, baseEnd_2180049] using wordTrace_append hprefix tailTrace_2180049
  have hstable : (prefixWord ++ tailWord_2180049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180049).length < 2 ^ (prefixWord ++ tailWord_2180049).sum := by decide
  have hdescent : baseEnd_2180049 < baseStart_2180049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180050 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2180050 : Nat := 118140960795 + 2180050 * 2 ^ 59
def prefixEnd_2180050 : Nat := 4983230072969 + 3 ^ 40 * 2180050 * 2
def baseEnd_2180050 : Nat := 1119413500834300778049139

theorem tailTrace_2180050 : CollatzResearch.WordTrace tailWord_2180050 prefixEnd_2180050 1119413500834300778049139 := by
  unfold tailWord_2180050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878238938014661935742401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53008637168039098495313069 19878238938014661935742401)
  ·
    refine ⟨14908679203510996451806801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19878238938014661935742401 14908679203510996451806801)
    ·
      refine ⟨11181509402633247338855101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14908679203510996451806801 11181509402633247338855101)
      ·
        refine ⟨4193066025987467752070663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11181509402633247338855101 4193066025987467752070663)
        ·
          refine ⟨6289599038981201628105995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193066025987467752070663 6289599038981201628105995)
          ·
            refine ⟨9434398558471802442158993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289599038981201628105995 9434398558471802442158993)
            ·
              refine ⟨7075798918853851831619245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9434398558471802442158993 7075798918853851831619245)
              ·
                refine ⟨2653424594570194436857217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7075798918853851831619245 2653424594570194436857217)
                ·
                  refine ⟨1990068445927645827642913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2653424594570194436857217 1990068445927645827642913)
                  ·
                    refine ⟨1492551334445734370732185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990068445927645827642913 1492551334445734370732185)
                    ·
                      refine ⟨1119413500834300778049139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492551334445734370732185 1119413500834300778049139)
                      ·
                        rfl

theorem cell23_2180050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2180050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180050 prefixEnd_2180050 := by exact prefixLift 2180050
  have htrace : WordTrace (prefixWord ++ tailWord_2180050) baseStart_2180050 baseEnd_2180050 := by
    simpa [prefixWord, tailWord_2180050, baseEnd_2180050] using wordTrace_append hprefix tailTrace_2180050
  have hstable : (prefixWord ++ tailWord_2180050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180050).length < 2 ^ (prefixWord ++ tailWord_2180050).sum := by decide
  have hdescent : baseEnd_2180050 < baseStart_2180050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180089 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2180089 : Nat := 118140960795 + 2180089 * 2 ^ 59
def prefixEnd_2180089 : Nat := 4983230072969 + 3 ^ 40 * 2180089 * 2
def baseEnd_2180089 : Nat := 1119433526579826125461459

theorem tailTrace_2180089 : CollatzResearch.WordTrace tailWord_2180089 prefixEnd_2180089 1119433526579826125461459 := by
  unfold tailWord_2180089
  simp only [CollatzResearch.WordTrace]
  refine ⟨79514378198917357403639321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53009585465944904935759547 79514378198917357403639321)
  ·
    refine ⟨59635783649188018052729491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79514378198917357403639321 59635783649188018052729491)
    ·
      refine ⟨89453675473782027079094237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59635783649188018052729491 89453675473782027079094237)
      ·
        refine ⟨33545128302668260154660339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89453675473782027079094237 33545128302668260154660339)
        ·
          refine ⟨50317692454002390231990509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33545128302668260154660339 50317692454002390231990509)
          ·
            refine ⟨18869134670250896336996441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50317692454002390231990509 18869134670250896336996441)
            ·
              refine ⟨14151851002688172252747331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18869134670250896336996441 14151851002688172252747331)
              ·
                refine ⟨21227776504032258379120997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14151851002688172252747331 21227776504032258379120997)
                ·
                  refine ⟨3980208094506048446085187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21227776504032258379120997 3980208094506048446085187)
                  ·
                    refine ⟨5970312141759072669127781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3980208094506048446085187 5970312141759072669127781)
                    ·
                      refine ⟨1119433526579826125461459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5970312141759072669127781 1119433526579826125461459)
                      ·
                        rfl

theorem cell23_2180089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2180089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180089 prefixEnd_2180089 := by exact prefixLift 2180089
  have htrace : WordTrace (prefixWord ++ tailWord_2180089) baseStart_2180089 baseEnd_2180089 := by
    simpa [prefixWord, tailWord_2180089, baseEnd_2180089] using wordTrace_append hprefix tailTrace_2180089
  have hstable : (prefixWord ++ tailWord_2180089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180089).length < 2 ^ (prefixWord ++ tailWord_2180089).sum := by decide
  have hdescent : baseEnd_2180089 < baseStart_2180089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180112 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 12]
def baseStart_2180112 : Nat := 118140960795 + 2180112 * 2 ^ 59
def prefixEnd_2180112 : Nat := 4983230072969 + 3 ^ 40 * 2180112 * 2
def baseEnd_2180112 : Nat := 124382815181653281719317

theorem tailTrace_2180112 : CollatzResearch.WordTrace tailWord_2180112 prefixEnd_2180112 124382815181653281719317 := by
  unfold tailWord_2180112
  simp only [CollatzResearch.WordTrace]
  refine ⟨39757608538917016165863295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53010144718556021554484393 39757608538917016165863295)
  ·
    refine ⟨59636412808375524248794943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39757608538917016165863295 59636412808375524248794943)
    ·
      refine ⟨89454619212563286373192415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59636412808375524248794943 89454619212563286373192415)
      ·
        refine ⟨134181928818844929559788623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89454619212563286373192415 134181928818844929559788623)
        ·
          refine ⟨201272893228267394339682935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134181928818844929559788623 201272893228267394339682935)
          ·
            refine ⟨301909339842401091509524403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201272893228267394339682935 301909339842401091509524403)
            ·
              refine ⟨452864009763601637264286605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301909339842401091509524403 452864009763601637264286605)
              ·
                refine ⟨169824003661350613974107477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452864009763601637264286605 169824003661350613974107477)
                ·
                  refine ⟨124382815181653281719317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 169824003661350613974107477 124382815181653281719317)
                  ·
                    rfl

theorem cell23_2180112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_2180112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180112 prefixEnd_2180112 := by exact prefixLift 2180112
  have htrace : WordTrace (prefixWord ++ tailWord_2180112) baseStart_2180112 baseEnd_2180112 := by
    simpa [prefixWord, tailWord_2180112, baseEnd_2180112] using wordTrace_append hprefix tailTrace_2180112
  have hstable : (prefixWord ++ tailWord_2180112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180112).length < 2 ^ (prefixWord ++ tailWord_2180112).sum := by decide
  have hdescent : baseEnd_2180112 < baseStart_2180112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180129 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 8]
def baseStart_2180129 : Nat := 118140960795 + 2180129 * 2 ^ 59
def prefixEnd_2180129 : Nat := 4983230072969 + 3 ^ 40 * 2180129 * 2
def baseEnd_2180129 : Nat := 124383785089556218773475

theorem tailTrace_2180129 : CollatzResearch.WordTrace tailWord_2180129 prefixEnd_2180129 124383785089556218773475 := by
  unfold tailWord_2180129
  simp only [CollatzResearch.WordTrace]
  refine ⟨79515837118772444235095441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53010558079181629490063627 79515837118772444235095441)
  ·
    refine ⟨59636877839079333176321581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79515837118772444235095441 59636877839079333176321581)
    ·
      refine ⟨22363829189654749941120593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59636877839079333176321581 22363829189654749941120593)
      ·
        refine ⟨16772871892241062455840445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22363829189654749941120593 16772871892241062455840445)
        ·
          refine ⟨6289826959590398420940167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16772871892241062455840445 6289826959590398420940167)
          ·
            refine ⟨9434740439385597631410251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289826959590398420940167 9434740439385597631410251)
            ·
              refine ⟨14152110659078396447115377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9434740439385597631410251 14152110659078396447115377)
              ·
                refine ⟨10614082994308797335336533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14152110659078396447115377 10614082994308797335336533)
                ·
                  refine ⟨124383785089556218773475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10614082994308797335336533 124383785089556218773475)
                  ·
                    rfl

theorem cell23_2180129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_2180129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180129 prefixEnd_2180129 := by exact prefixLift 2180129
  have htrace : WordTrace (prefixWord ++ tailWord_2180129) baseStart_2180129 baseEnd_2180129 := by
    simpa [prefixWord, tailWord_2180129, baseEnd_2180129] using wordTrace_append hprefix tailTrace_2180129
  have hstable : (prefixWord ++ tailWord_2180129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180129).length < 2 ^ (prefixWord ++ tailWord_2180129).sum := by decide
  have hdescent : baseEnd_2180129 < baseStart_2180129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180150 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2180150 : Nat := 118140960795 + 2180150 * 2 ^ 59
def prefixEnd_2180150 : Nat := 4983230072969 + 3 ^ 40 * 2180150 * 2
def baseEnd_2180150 : Nat := 373154949633250128932893

theorem tailTrace_2180150 : CollatzResearch.WordTrace tailWord_2180150 prefixEnd_2180150 373154949633250128932893 := by
  unfold tailWord_2180150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969787690731022801350619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53011068701130909881073269 4969787690731022801350619)
  ·
    refine ⟨7454681536096534202025929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4969787690731022801350619 7454681536096534202025929)
    ·
      refine ⟨5591011152072400651519447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7454681536096534202025929 5591011152072400651519447)
      ·
        refine ⟨8386516728108600977279171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5591011152072400651519447 8386516728108600977279171)
        ·
          refine ⟨12579775092162901465918757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8386516728108600977279171 12579775092162901465918757)
          ·
            refine ⟨2358707829780544024859767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12579775092162901465918757 2358707829780544024859767)
            ·
              refine ⟨3538061744670816037289651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358707829780544024859767 3538061744670816037289651)
              ·
                refine ⟨5307092617006224055934477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538061744670816037289651 5307092617006224055934477)
                ·
                  refine ⟨1990159731377334020975429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5307092617006224055934477 1990159731377334020975429)
                  ·
                    refine ⟨373154949633250128932893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990159731377334020975429 373154949633250128932893)
                    ·
                      rfl

theorem cell23_2180150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2180150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180150 prefixEnd_2180150 := by exact prefixLift 2180150
  have htrace : WordTrace (prefixWord ++ tailWord_2180150) baseStart_2180150 baseEnd_2180150 := by
    simpa [prefixWord, tailWord_2180150, baseEnd_2180150] using wordTrace_append hprefix tailTrace_2180150
  have hstable : (prefixWord ++ tailWord_2180150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180150).length < 2 ^ (prefixWord ++ tailWord_2180150).sum := by decide
  have hdescent : baseEnd_2180150 < baseStart_2180150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180159 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 3, 5]
def baseStart_2180159 : Nat := 118140960795 + 2180159 * 2 ^ 59
def prefixEnd_2180159 : Nat := 4983230072969 + 3 ^ 40 * 2180159 * 2
def baseEnd_2180159 : Nat := 373156490075213617195379

theorem tailTrace_2180159 : CollatzResearch.WordTrace tailWord_2180159 prefixEnd_2180159 373156490075213617195379 := by
  unfold tailWord_2180159
  simp only [CollatzResearch.WordTrace]
  refine ⟨79516931308663759358687531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53011287539109172905791687 79516931308663759358687531)
  ·
    refine ⟨119275396962995639038031297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79516931308663759358687531 119275396962995639038031297)
    ·
      refine ⟨89456547722246729278523473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119275396962995639038031297 89456547722246729278523473)
      ·
        refine ⟨67092410791685046958892605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89456547722246729278523473 67092410791685046958892605)
        ·
          refine ⟨25159654046881892609584727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67092410791685046958892605 25159654046881892609584727)
          ·
            refine ⟨37739481070322838914377091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25159654046881892609584727 37739481070322838914377091)
            ·
              refine ⟨56609221605484258371565637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37739481070322838914377091 56609221605484258371565637)
              ·
                refine ⟨10614229051028298444668557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56609221605484258371565637 10614229051028298444668557)
                ·
                  refine ⟨3980335894135611916750709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10614229051028298444668557 3980335894135611916750709)
                  ·
                    refine ⟨373156490075213617195379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3980335894135611916750709 373156490075213617195379)
                    ·
                      rfl

theorem cell23_2180159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_2180159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180159 prefixEnd_2180159 := by exact prefixLift 2180159
  have htrace : WordTrace (prefixWord ++ tailWord_2180159) baseStart_2180159 baseEnd_2180159 := by
    simpa [prefixWord, tailWord_2180159, baseEnd_2180159] using wordTrace_append hprefix tailTrace_2180159
  have hstable : (prefixWord ++ tailWord_2180159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180159).length < 2 ^ (prefixWord ++ tailWord_2180159).sum := by decide
  have hdescent : baseEnd_2180159 < baseStart_2180159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180209 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2180209 : Nat := 118140960795 + 2180209 * 2 ^ 59
def prefixEnd_2180209 : Nat := 4983230072969 + 3 ^ 40 * 2180209 * 2
def baseEnd_2180209 : Nat := 1119495144258365655960907

theorem tailTrace_2180209 : CollatzResearch.WordTrace tailWord_2180209 prefixEnd_2180209 1119495144258365655960907 := by
  unfold tailWord_2180209
  simp only [CollatzResearch.WordTrace]
  refine ⟨79518754958482617898007681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53012503305655078598671787 79518754958482617898007681)
  ·
    refine ⟨59639066218861963423505761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79518754958482617898007681 59639066218861963423505761)
    ·
      refine ⟨44729299664146472567629321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59639066218861963423505761 44729299664146472567629321)
      ·
        refine ⟨33546974748109854425721991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44729299664146472567629321 33546974748109854425721991)
        ·
          refine ⟨50320462122164781638582987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33546974748109854425721991 50320462122164781638582987)
          ·
            refine ⟨75480693183247172457874481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50320462122164781638582987 75480693183247172457874481)
            ·
              refine ⟨56610519887435379343405861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75480693183247172457874481 56610519887435379343405861)
              ·
                refine ⟨10614472478894133626888599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56610519887435379343405861 10614472478894133626888599)
                ·
                  refine ⟨15921708718341200440332899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10614472478894133626888599 15921708718341200440332899)
                  ·
                    refine ⟨23882563077511800660499349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15921708718341200440332899 23882563077511800660499349)
                    ·
                      refine ⟨1119495144258365655960907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23882563077511800660499349 1119495144258365655960907)
                      ·
                        rfl

theorem cell23_2180209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2180209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180209 prefixEnd_2180209 := by exact prefixLift 2180209
  have htrace : WordTrace (prefixWord ++ tailWord_2180209) baseStart_2180209 baseEnd_2180209 := by
    simpa [prefixWord, tailWord_2180209, baseEnd_2180209] using wordTrace_append hprefix tailTrace_2180209
  have hstable : (prefixWord ++ tailWord_2180209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180209).length < 2 ^ (prefixWord ++ tailWord_2180209).sum := by decide
  have hdescent : baseEnd_2180209 < baseStart_2180209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180216 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_2180216 : Nat := 118140960795 + 2180216 * 2 ^ 59
def prefixEnd_2180216 : Nat := 4983230072969 + 3 ^ 40 * 2180216 * 2
def baseEnd_2180216 : Nat := 1119498738622947128573375

theorem tailTrace_2180216 : CollatzResearch.WordTrace tailWord_2180216 prefixEnd_2180216 1119498738622947128573375 := by
  unfold tailWord_2180216
  simp only [CollatzResearch.WordTrace]
  refine ⟨39759505134728629046756251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53012673512971505395675001 39759505134728629046756251)
  ·
    refine ⟨59639257702092943570134377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39759505134728629046756251 59639257702092943570134377)
    ·
      refine ⟨44729443276569707677600783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59639257702092943570134377 44729443276569707677600783)
      ·
        refine ⟨67094164914854561516401175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44729443276569707677600783 67094164914854561516401175)
        ·
          refine ⟨100641247372281842274601763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67094164914854561516401175 100641247372281842274601763)
          ·
            refine ⟨150961871058422763411902645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100641247372281842274601763 150961871058422763411902645)
            ·
              refine ⟨14152675411727134069865873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150961871058422763411902645 14152675411727134069865873)
              ·
                refine ⟨10614506558795350552399405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14152675411727134069865873 10614506558795350552399405)
                ·
                  refine ⟨3980439959548256457149777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10614506558795350552399405 3980439959548256457149777)
                  ·
                    refine ⟨2985329969661192342862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3980439959548256457149777 2985329969661192342862333)
                    ·
                      refine ⟨1119498738622947128573375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2985329969661192342862333 1119498738622947128573375)
                      ·
                        rfl

theorem cell23_2180216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_2180216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180216 prefixEnd_2180216 := by exact prefixLift 2180216
  have htrace : WordTrace (prefixWord ++ tailWord_2180216) baseStart_2180216 baseEnd_2180216 := by
    simpa [prefixWord, tailWord_2180216, baseEnd_2180216] using wordTrace_append hprefix tailTrace_2180216
  have hstable : (prefixWord ++ tailWord_2180216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180216).length < 2 ^ (prefixWord ++ tailWord_2180216).sum := by decide
  have hdescent : baseEnd_2180216 < baseStart_2180216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180247 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 1, 2, 2]
def baseStart_2180247 : Nat := 118140960795 + 2180247 * 2 ^ 59
def prefixEnd_2180247 : Nat := 4983230072969 + 3 ^ 40 * 2180247 * 2
def baseEnd_2180247 : Nat := 1119514656523236507285733

theorem tailTrace_2180247 : CollatzResearch.WordTrace tailWord_2180247 prefixEnd_2180247 1119514656523236507285733 := by
  unfold tailWord_2180247
  simp only [CollatzResearch.WordTrace]
  refine ⟨79520140932344950387890995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53013427288229966925260663 79520140932344950387890995)
  ·
    refine ⟨119280211398517425581836493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79520140932344950387890995 119280211398517425581836493)
    ·
      refine ⟨44730079274444034593188685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119280211398517425581836493 44730079274444034593188685)
      ·
        refine ⟨16773779727916512972445757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44730079274444034593188685 16773779727916512972445757)
        ·
          refine ⟨6290167397968692364667159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16773779727916512972445757 6290167397968692364667159)
          ·
            refine ⟨9435251096953038547000739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290167397968692364667159 9435251096953038547000739)
            ·
              refine ⟨14152876645429557820501109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435251096953038547000739 14152876645429557820501109)
              ·
                refine ⟨1326832185509021045671979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14152876645429557820501109 1326832185509021045671979)
                ·
                  refine ⟨1990248278263531568507969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326832185509021045671979 1990248278263531568507969)
                  ·
                    refine ⟨1492686208697648676380977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990248278263531568507969 1492686208697648676380977)
                    ·
                      refine ⟨1119514656523236507285733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492686208697648676380977 1119514656523236507285733)
                      ·
                        rfl

theorem cell23_2180247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_2180247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180247 prefixEnd_2180247 := by exact prefixLift 2180247
  have htrace : WordTrace (prefixWord ++ tailWord_2180247) baseStart_2180247 baseEnd_2180247 := by
    simpa [prefixWord, tailWord_2180247, baseEnd_2180247] using wordTrace_append hprefix tailTrace_2180247
  have hstable : (prefixWord ++ tailWord_2180247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180247).length < 2 ^ (prefixWord ++ tailWord_2180247).sum := by decide
  have hdescent : baseEnd_2180247 < baseStart_2180247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180250 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2180250 : Nat := 118140960795 + 2180250 * 2 ^ 59
def prefixEnd_2180250 : Nat := 4983230072969 + 3 ^ 40 * 2180250 * 2
def baseEnd_2180250 : Nat := 1119516196965199995548219

theorem tailTrace_2180250 : CollatzResearch.WordTrace tailWord_2180250 prefixEnd_2180250 1119516196965199995548219 := by
  unfold tailWord_2180250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19880062587833520475062551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53013500234222721266833469 19880062587833520475062551)
  ·
    refine ⟨29820093881750280712593827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19880062587833520475062551 29820093881750280712593827)
    ·
      refine ⟨44730140822625421068890741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29820093881750280712593827 44730140822625421068890741)
      ·
        refine ⟨4193450702121133225208507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44730140822625421068890741 4193450702121133225208507)
        ·
          refine ⟨6290176053181699837812761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193450702121133225208507 6290176053181699837812761)
          ·
            refine ⟨4717632039886274878359571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6290176053181699837812761 4717632039886274878359571)
            ·
              refine ⟨7076448059829412317539357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4717632039886274878359571 7076448059829412317539357)
              ·
                refine ⟨2653668022436029619077259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7076448059829412317539357 2653668022436029619077259)
                ·
                  refine ⟨3980502033654044428615889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653668022436029619077259 3980502033654044428615889)
                  ·
                    refine ⟨2985376525240533321461917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3980502033654044428615889 2985376525240533321461917)
                    ·
                      refine ⟨1119516196965199995548219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2985376525240533321461917 1119516196965199995548219)
                      ·
                        rfl

theorem cell23_2180250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2180250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180250 prefixEnd_2180250 := by exact prefixLift 2180250
  have htrace : WordTrace (prefixWord ++ tailWord_2180250) baseStart_2180250 baseEnd_2180250 := by
    simpa [prefixWord, tailWord_2180250, baseEnd_2180250] using wordTrace_append hprefix tailTrace_2180250
  have hstable : (prefixWord ++ tailWord_2180250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180250).length < 2 ^ (prefixWord ++ tailWord_2180250).sum := by decide
  have hdescent : baseEnd_2180250 < baseStart_2180250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180320 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2]
def baseStart_2180320 : Nat := 118140960795 + 2180320 * 2 ^ 59
def prefixEnd_2180320 : Nat := 4983230072969 + 3 ^ 40 * 2180320 * 2
def baseEnd_2180320 : Nat := 1119552140611014721672897

theorem tailTrace_2180320 : CollatzResearch.WordTrace tailWord_2180320 prefixEnd_2180320 1119552140611014721672897 := by
  unfold tailWord_2180320
  simp only [CollatzResearch.WordTrace]
  refine ⟨39761401730540241927649207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53015202307386989236865609 39761401730540241927649207)
  ·
    refine ⟨59642102595810362891473811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39761401730540241927649207 59642102595810362891473811)
    ·
      refine ⟨89463153893715544337210717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59642102595810362891473811 89463153893715544337210717)
      ·
        refine ⟨33548682710143329126454019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89463153893715544337210717 33548682710143329126454019)
        ·
          refine ⟨50323024065214993689681029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33548682710143329126454019 50323024065214993689681029)
          ·
            refine ⟨9435567012227811316815193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50323024065214993689681029 9435567012227811316815193)
            ·
              refine ⟨7076675259170858487611395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9435567012227811316815193 7076675259170858487611395)
              ·
                refine ⟨10615012888756287731417093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7076675259170858487611395 10615012888756287731417093)
                ·
                  refine ⟨1990314916641803949640705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10615012888756287731417093 1990314916641803949640705)
                  ·
                    refine ⟨1492736187481352962230529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990314916641803949640705 1492736187481352962230529)
                    ·
                      refine ⟨1119552140611014721672897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492736187481352962230529 1119552140611014721672897)
                      ·
                        rfl

theorem cell23_2180320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_2180320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180320 prefixEnd_2180320 := by exact prefixLift 2180320
  have htrace : WordTrace (prefixWord ++ tailWord_2180320) baseStart_2180320 baseEnd_2180320 := by
    simpa [prefixWord, tailWord_2180320, baseEnd_2180320] using wordTrace_append hprefix tailTrace_2180320
  have hstable : (prefixWord ++ tailWord_2180320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180320).length < 2 ^ (prefixWord ++ tailWord_2180320).sum := by decide
  have hdescent : baseEnd_2180320 < baseStart_2180320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180403 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 5, 4]
def baseStart_2180403 : Nat := 118140960795 + 2180403 * 2 ^ 59
def prefixEnd_2180403 : Nat := 4983230072969 + 3 ^ 40 * 2180403 * 2
def baseEnd_2180403 : Nat := 373198253168445965645005

theorem tailTrace_2180403 : CollatzResearch.WordTrace tailWord_2180403 prefixEnd_2180403 373198253168445965645005 := by
  unfold tailWord_2180403
  simp only [CollatzResearch.WordTrace]
  refine ⟨79525830719779789030569863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53017220479853192687046575 79525830719779789030569863)
  ·
    refine ⟨119288746079669683545854795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79525830719779789030569863 119288746079669683545854795)
    ·
      refine ⟨178933119119504525318782193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119288746079669683545854795 178933119119504525318782193)
      ·
        refine ⟨134199839339628393989086645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178933119119504525318782193 134199839339628393989086645)
        ·
          refine ⟨12581234938090161936476873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134199839339628393989086645 12581234938090161936476873)
          ·
            refine ⟨9435926203567621452357655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12581234938090161936476873 9435926203567621452357655)
            ·
              refine ⟨14153889305351432178536483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435926203567621452357655 14153889305351432178536483)
              ·
                refine ⟨21230833958027148267804725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14153889305351432178536483 21230833958027148267804725)
                ·
                  refine ⟨1990390683565045150106693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21230833958027148267804725 1990390683565045150106693)
                  ·
                    refine ⟨373198253168445965645005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990390683565045150106693 373198253168445965645005)
                    ·
                      rfl

theorem cell23_2180403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 4].length) (baseStart_2180403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180403 prefixEnd_2180403 := by exact prefixLift 2180403
  have htrace : WordTrace (prefixWord ++ tailWord_2180403) baseStart_2180403 baseEnd_2180403 := by
    simpa [prefixWord, tailWord_2180403, baseEnd_2180403] using wordTrace_append hprefix tailTrace_2180403
  have hstable : (prefixWord ++ tailWord_2180403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180403).length < 2 ^ (prefixWord ++ tailWord_2180403).sum := by decide
  have hdescent : baseEnd_2180403 < baseStart_2180403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180416 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 8]
def baseStart_2180416 : Nat := 118140960795 + 2180416 * 2 ^ 59
def prefixEnd_2180416 : Nat := 4983230072969 + 3 ^ 40 * 2180416 * 2
def baseEnd_2180416 : Nat := 124400159417094038452495

theorem tailTrace_2180416 : CollatzResearch.WordTrace tailWord_2180416 prefixEnd_2180416 124400159417094038452495 := by
  unfold tailWord_2180416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39763152434366346125396551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53017536579155128167195401 39763152434366346125396551)
  ·
    refine ⟨59644728651549519188094827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39763152434366346125396551 59644728651549519188094827)
    ·
      refine ⟨89467092977324278782142241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59644728651549519188094827 89467092977324278782142241)
      ·
        refine ⟨67100319732993209086606681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89467092977324278782142241 67100319732993209086606681)
        ·
          refine ⟨50325239799744906814955011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67100319732993209086606681 50325239799744906814955011)
          ·
            refine ⟨75487859699617360222432517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50325239799744906814955011 75487859699617360222432517)
            ·
              refine ⟨14153973693678255041706097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75487859699617360222432517 14153973693678255041706097)
              ·
                refine ⟨10615480270258691281279573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14153973693678255041706097 10615480270258691281279573)
                ·
                  refine ⟨124400159417094038452495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10615480270258691281279573 124400159417094038452495)
                  ·
                    rfl

theorem cell23_2180416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_2180416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180416 prefixEnd_2180416 := by exact prefixLift 2180416
  have htrace : WordTrace (prefixWord ++ tailWord_2180416) baseStart_2180416 baseEnd_2180416 := by
    simpa [prefixWord, tailWord_2180416, baseEnd_2180416] using wordTrace_append hprefix tailTrace_2180416
  have hstable : (prefixWord ++ tailWord_2180416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180416).length < 2 ^ (prefixWord ++ tailWord_2180416).sum := by decide
  have hdescent : baseEnd_2180416 < baseStart_2180416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180437 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_2180437 : Nat := 118140960795 + 2180437 * 2 ^ 59
def prefixEnd_2180437 : Nat := 4983230072969 + 3 ^ 40 * 2180437 * 2
def baseEnd_2180437 : Nat := 373204072615863587969953

theorem tailTrace_2180437 : CollatzResearch.WordTrace tailWord_2180437 prefixEnd_2180437 373204072615863587969953 := by
  unfold tailWord_2180437
  simp only [CollatzResearch.WordTrace]
  refine ⟨79527070801656612837307565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53018047201104408558205043 79527070801656612837307565)
  ·
    refine ⟨29822651550621229813990337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79527070801656612837307565 29822651550621229813990337)
    ·
      refine ⟨22366988662965922360492753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29822651550621229813990337 22366988662965922360492753)
      ·
        refine ⟨16775241497224441770369565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22366988662965922360492753 16775241497224441770369565)
        ·
          refine ⟨6290715561459165663888587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16775241497224441770369565 6290715561459165663888587)
          ·
            refine ⟨9436073342188748495832881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290715561459165663888587 9436073342188748495832881)
            ·
              refine ⟨7077055006641561371874661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9436073342188748495832881 7077055006641561371874661)
              ·
                refine ⟨1326947813745292757226499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7077055006641561371874661 1326947813745292757226499)
                ·
                  refine ⟨1990421720617939135839749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326947813745292757226499 1990421720617939135839749)
                  ·
                    refine ⟨373204072615863587969953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1990421720617939135839749 373204072615863587969953)
                    ·
                      rfl

theorem cell23_2180437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_2180437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180437 prefixEnd_2180437 := by exact prefixLift 2180437
  have htrace : WordTrace (prefixWord ++ tailWord_2180437) baseStart_2180437 baseEnd_2180437 := by
    simpa [prefixWord, tailWord_2180437, baseEnd_2180437] using wordTrace_append hprefix tailTrace_2180437
  have hstable : (prefixWord ++ tailWord_2180437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180437).length < 2 ^ (prefixWord ++ tailWord_2180437).sum := by decide
  have hdescent : baseEnd_2180437 < baseStart_2180437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180487 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_2180487 : Nat := 118140960795 + 2180487 * 2 ^ 59
def prefixEnd_2180487 : Nat := 4983230072969 + 3 ^ 40 * 2180487 * 2
def baseEnd_2180487 : Nat := 1119637891880315568284629

theorem tailTrace_2180487 : CollatzResearch.WordTrace tailWord_2180487 prefixEnd_2180487 1119637891880315568284629 := by
  unfold tailWord_2180487
  simp only [CollatzResearch.WordTrace]
  refine ⟨79528894451475471376627715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53019262967650314251085143 79528894451475471376627715)
  ·
    refine ⟨119293341677213207064941573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79528894451475471376627715 119293341677213207064941573)
    ·
      refine ⟨22367501564477476324676545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119293341677213207064941573 22367501564477476324676545)
      ·
        refine ⟨16775626173358107243507409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22367501564477476324676545 16775626173358107243507409)
        ·
          refine ⟨12581719630018580432630557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16775626173358107243507409 12581719630018580432630557)
          ·
            refine ⟨4718144861256967662236459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12581719630018580432630557 4718144861256967662236459)
            ·
              refine ⟨7077217291885451493354689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718144861256967662236459 7077217291885451493354689)
              ·
                refine ⟨5307912968914088620016017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7077217291885451493354689 5307912968914088620016017)
                ·
                  refine ⟨3980934726685566465012013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5307912968914088620016017 3980934726685566465012013)
                  ·
                    refine ⟨1492850522507087424379505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3980934726685566465012013 1492850522507087424379505)
                    ·
                      refine ⟨1119637891880315568284629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492850522507087424379505 1119637891880315568284629)
                      ·
                        rfl

theorem cell23_2180487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_2180487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180487 prefixEnd_2180487 := by exact prefixLift 2180487
  have htrace : WordTrace (prefixWord ++ tailWord_2180487) baseStart_2180487 baseEnd_2180487 := by
    simpa [prefixWord, tailWord_2180487, baseEnd_2180487] using wordTrace_append hprefix tailTrace_2180487
  have hstable : (prefixWord ++ tailWord_2180487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180487).length < 2 ^ (prefixWord ++ tailWord_2180487).sum := by decide
  have hdescent : baseEnd_2180487 < baseStart_2180487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180503 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_2180503 : Nat := 118140960795 + 2180503 * 2 ^ 59
def prefixEnd_2180503 : Nat := 4983230072969 + 3 ^ 40 * 2180503 * 2
def baseEnd_2180503 : Nat := 1119646107570787505684555

theorem tailTrace_2180503 : CollatzResearch.WordTrace tailWord_2180503 prefixEnd_2180503 1119646107570787505684555 := by
  unfold tailWord_2180503
  simp only [CollatzResearch.WordTrace]
  refine ⟨79529478019417506109210163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53019652012945004072806775 79529478019417506109210163)
  ·
    refine ⟨119294217029126259163815245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79529478019417506109210163 119294217029126259163815245)
    ·
      refine ⟨44735331385922347186430717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119294217029126259163815245 44735331385922347186430717)
      ·
        refine ⟨16775749269720880194911519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44735331385922347186430717 16775749269720880194911519)
        ·
          refine ⟨25163623904581320292367279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16775749269720880194911519 25163623904581320292367279)
          ·
            refine ⟨37745435856871980438550919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25163623904581320292367279 37745435856871980438550919)
            ·
              refine ⟨56618153785307970657826379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37745435856871980438550919 56618153785307970657826379)
              ·
                refine ⟨84927230677961955986739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56618153785307970657826379 84927230677961955986739569)
                ·
                  refine ⟨63695423008471466990054677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84927230677961955986739569 63695423008471466990054677)
                  ·
                    refine ⟨2985722953522100015158813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63695423008471466990054677 2985722953522100015158813)
                    ·
                      refine ⟨1119646107570787505684555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2985722953522100015158813 1119646107570787505684555)
                      ·
                        rfl

theorem cell23_2180503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_2180503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180503 prefixEnd_2180503 := by exact prefixLift 2180503
  have htrace : WordTrace (prefixWord ++ tailWord_2180503) baseStart_2180503 baseEnd_2180503 := by
    simpa [prefixWord, tailWord_2180503, baseEnd_2180503] using wordTrace_append hprefix tailTrace_2180503
  have hstable : (prefixWord ++ tailWord_2180503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180503).length < 2 ^ (prefixWord ++ tailWord_2180503).sum := by decide
  have hdescent : baseEnd_2180503 < baseStart_2180503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180537 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2180537 : Nat := 118140960795 + 2180537 * 2 ^ 59
def prefixEnd_2180537 : Nat := 4983230072969 + 3 ^ 40 * 2180537 * 2
def baseEnd_2180537 : Nat := 1119663565913040372659399

theorem tailTrace_2180537 : CollatzResearch.WordTrace tailWord_2180537 prefixEnd_2180537 1119663565913040372659399 := by
  unfold tailWord_2180537
  simp only [CollatzResearch.WordTrace]
  refine ⟨79530718101294329915947865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53020478734196219943965243 79530718101294329915947865)
  ·
    refine ⟨59648038575970747436960899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79530718101294329915947865 59648038575970747436960899)
    ·
      refine ⟨89472057863956121155441349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59648038575970747436960899 89472057863956121155441349)
      ·
        refine ⟨16776010849491772716645253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89472057863956121155441349 16776010849491772716645253)
        ·
          refine ⟨3145502034279707384370985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16776010849491772716645253 3145502034279707384370985)
          ·
            refine ⟨2359126525709780538278239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3145502034279707384370985 2359126525709780538278239)
            ·
              refine ⟨3538689788564670807417359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359126525709780538278239 3538689788564670807417359)
              ·
                refine ⟨5308034682847006211126039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538689788564670807417359 5308034682847006211126039)
                ·
                  refine ⟨7962052024270509316689059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308034682847006211126039 7962052024270509316689059)
                  ·
                    refine ⟨11943078036405763975033589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7962052024270509316689059 11943078036405763975033589)
                    ·
                      refine ⟨1119663565913040372659399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11943078036405763975033589 1119663565913040372659399)
                      ·
                        rfl

theorem cell23_2180537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2180537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180537 prefixEnd_2180537 := by exact prefixLift 2180537
  have htrace : WordTrace (prefixWord ++ tailWord_2180537) baseStart_2180537 baseEnd_2180537 := by
    simpa [prefixWord, tailWord_2180537, baseEnd_2180537] using wordTrace_append hprefix tailTrace_2180537
  have hstable : (prefixWord ++ tailWord_2180537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180537).length < 2 ^ (prefixWord ++ tailWord_2180537).sum := by decide
  have hdescent : baseEnd_2180537 < baseStart_2180537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180540 : List Nat := [2, 2, 2, 4, 3, 10]
def baseStart_2180540 : Nat := 118140960795 + 2180540 * 2 ^ 59
def prefixEnd_2180540 : Nat := 4983230072969 + 3 ^ 40 * 2180540 * 2
def baseEnd_2180540 : Nat := 4607675334794254571695

theorem tailTrace_2180540 : CollatzResearch.WordTrace tailWord_2180540 prefixEnd_2180540 4607675334794254571695 := by
  unfold tailWord_2180540
  simp only [CollatzResearch.WordTrace]
  refine ⟨39765413760141730714153537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53020551680188974285538049 39765413760141730714153537)
  ·
    refine ⟨29824060320106298035615153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39765413760141730714153537 29824060320106298035615153)
    ·
      refine ⟨22368045240079723526711365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29824060320106298035615153 22368045240079723526711365)
      ·
        refine ⟨4194008482514948161258381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22368045240079723526711365 4194008482514948161258381)
        ·
          refine ⟨1572753180943105560471893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4194008482514948161258381 1572753180943105560471893)
          ·
            refine ⟨4607675334794254571695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1572753180943105560471893 4607675334794254571695)
            ·
              rfl

theorem cell23_2180540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 10].length) (baseStart_2180540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180540 prefixEnd_2180540 := by exact prefixLift 2180540
  have htrace : WordTrace (prefixWord ++ tailWord_2180540) baseStart_2180540 baseEnd_2180540 := by
    simpa [prefixWord, tailWord_2180540, baseEnd_2180540] using wordTrace_append hprefix tailTrace_2180540
  have hstable : (prefixWord ++ tailWord_2180540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180540).length < 2 ^ (prefixWord ++ tailWord_2180540).sum := by decide
  have hdescent : baseEnd_2180540 < baseStart_2180540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180577 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_2180577 : Nat := 118140960795 + 2180577 * 2 ^ 59
def prefixEnd_2180577 : Nat := 4983230072969 + 3 ^ 40 * 2180577 * 2
def baseEnd_2180577 : Nat := 1119684105139220216159215

theorem tailTrace_2180577 : CollatzResearch.WordTrace tailWord_2180577 prefixEnd_2180577 1119684105139220216159215 := by
  unfold tailWord_2180577
  simp only [CollatzResearch.WordTrace]
  refine ⟨79532177021149416747403985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53021451347432944498269323 79532177021149416747403985)
  ·
    refine ⟨59649132765862062560552989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79532177021149416747403985 59649132765862062560552989)
    ·
      refine ⟨22368424787198273460207371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59649132765862062560552989 22368424787198273460207371)
      ·
        refine ⟨33552637180797410190311057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22368424787198273460207371 33552637180797410190311057)
        ·
          refine ⟨25164477885598057642733293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33552637180797410190311057 25164477885598057642733293)
          ·
            refine ⟨9436679207099271616024985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25164477885598057642733293 9436679207099271616024985)
            ·
              refine ⟨7077509405324453712018739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9436679207099271616024985 7077509405324453712018739)
              ·
                refine ⟨10616264107986680568028109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077509405324453712018739 10616264107986680568028109)
                ·
                  refine ⟨3981099040495005213010541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10616264107986680568028109 3981099040495005213010541)
                  ·
                    refine ⟨1492912140185626954878953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3981099040495005213010541 1492912140185626954878953)
                    ·
                      refine ⟨1119684105139220216159215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492912140185626954878953 1119684105139220216159215)
                      ·
                        rfl

theorem cell23_2180577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_2180577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180577 prefixEnd_2180577 := by exact prefixLift 2180577
  have htrace : WordTrace (prefixWord ++ tailWord_2180577) baseStart_2180577 baseEnd_2180577 := by
    simpa [prefixWord, tailWord_2180577, baseEnd_2180577] using wordTrace_append hprefix tailTrace_2180577
  have hstable : (prefixWord ++ tailWord_2180577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180577).length < 2 ^ (prefixWord ++ tailWord_2180577).sum := by decide
  have hdescent : baseEnd_2180577 < baseStart_2180577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180603 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_2180603 : Nat := 118140960795 + 2180603 * 2 ^ 59
def prefixEnd_2180603 : Nat := 4983230072969 + 3 ^ 40 * 2180603 * 2
def baseEnd_2180603 : Nat := 1119697455636237114434095

theorem tailTrace_2180603 : CollatzResearch.WordTrace tailWord_2180603 prefixEnd_2180603 1119697455636237114434095 := by
  unfold tailWord_2180603
  simp only [CollatzResearch.WordTrace]
  refine ⟨79533125319055223187850463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53022083546036815458566975 79533125319055223187850463)
  ·
    refine ⟨119299687978582834781775695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79533125319055223187850463 119299687978582834781775695)
    ·
      refine ⟨178949531967874252172663543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119299687978582834781775695 178949531967874252172663543)
      ·
        refine ⟨268424297951811378258995315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178949531967874252172663543 268424297951811378258995315)
        ·
          refine ⟨402636446927717067388492973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268424297951811378258995315 402636446927717067388492973)
          ·
            refine ⟨150988667597893900270684865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402636446927717067388492973 150988667597893900270684865)
            ·
              refine ⟨113241500698420425203013649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150988667597893900270684865 113241500698420425203013649)
              ·
                refine ⟨84931125523815318902260237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113241500698420425203013649 84931125523815318902260237)
                ·
                  refine ⟨31849172071430744588347589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84931125523815318902260237 31849172071430744588347589)
                  ·
                    refine ⟨5971719763393264610315173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31849172071430744588347589 5971719763393264610315173)
                    ·
                      refine ⟨1119697455636237114434095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5971719763393264610315173 1119697455636237114434095)
                      ·
                        rfl

theorem cell23_2180603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_2180603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180603 prefixEnd_2180603 := by exact prefixLift 2180603
  have htrace : WordTrace (prefixWord ++ tailWord_2180603) baseStart_2180603 baseEnd_2180603 := by
    simpa [prefixWord, tailWord_2180603, baseEnd_2180603] using wordTrace_append hprefix tailTrace_2180603
  have hstable : (prefixWord ++ tailWord_2180603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180603).length < 2 ^ (prefixWord ++ tailWord_2180603).sum := by decide
  have hdescent : baseEnd_2180603 < baseStart_2180603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180628 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2180628 : Nat := 118140960795 + 2180628 * 2 ^ 59
def prefixEnd_2180628 : Nat := 4983230072969 + 3 ^ 40 * 2180628 * 2
def baseEnd_2180628 : Nat := 1119710292652599516621481

theorem tailTrace_2180628 : CollatzResearch.WordTrace tailWord_2180628 prefixEnd_2180628 1119710292652599516621481 := by
  unfold tailWord_2180628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39767018571982326228755269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53022691429309768305007025 39767018571982326228755269)
  ·
    refine ⟨7456315982246686167891613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39767018571982326228755269 7456315982246686167891613)
    ·
      refine ⟨2796118493342507312959355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7456315982246686167891613 2796118493342507312959355)
      ·
        refine ⟨4194177740013760969439033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2796118493342507312959355 4194177740013760969439033)
        ·
          refine ⟨3145633305010320727079275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4194177740013760969439033 3145633305010320727079275)
          ·
            refine ⟨4718449957515481090618913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145633305010320727079275 4718449957515481090618913)
            ·
              refine ⟨3538837468136610817964185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718449957515481090618913 3538837468136610817964185)
              ·
                refine ⟨2654128101102458113473139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3538837468136610817964185 2654128101102458113473139)
                ·
                  refine ⟨3981192151653687170209709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654128101102458113473139 3981192151653687170209709)
                  ·
                    refine ⟨1492947056870132688828641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3981192151653687170209709 1492947056870132688828641)
                    ·
                      refine ⟨1119710292652599516621481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1492947056870132688828641 1119710292652599516621481)
                      ·
                        rfl

theorem cell23_2180628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2180628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180628 prefixEnd_2180628 := by exact prefixLift 2180628
  have htrace : WordTrace (prefixWord ++ tailWord_2180628) baseStart_2180628 baseEnd_2180628 := by
    simpa [prefixWord, tailWord_2180628, baseEnd_2180628] using wordTrace_append hprefix tailTrace_2180628
  have hstable : (prefixWord ++ tailWord_2180628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180628).length < 2 ^ (prefixWord ++ tailWord_2180628).sum := by decide
  have hdescent : baseEnd_2180628 < baseStart_2180628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180664 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 5]
def baseStart_2180664 : Nat := 118140960795 + 2180664 * 2 ^ 59
def prefixEnd_2180664 : Nat := 4983230072969 + 3 ^ 40 * 2180664 * 2
def baseEnd_2180664 : Nat := 124414308661795708419035

theorem tailTrace_2180664 : CollatzResearch.WordTrace tailWord_2180664 prefixEnd_2180664 124414308661795708419035 := by
  unfold tailWord_2180664
  simp only [CollatzResearch.WordTrace]
  refine ⟨39767675085917115302910523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53023566781222820403880697 39767675085917115302910523)
  ·
    refine ⟨59651512628875672954365785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39767675085917115302910523 59651512628875672954365785)
    ·
      refine ⟨44738634471656754715774339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59651512628875672954365785 44738634471656754715774339)
      ·
        refine ⟨67107951707485132073661509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44738634471656754715774339 67107951707485132073661509)
        ·
          refine ⟨12582740945153462263811533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67107951707485132073661509 12582740945153462263811533)
          ·
            refine ⟨4718527854432548348929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12582740945153462263811533 4718527854432548348929325)
            ·
              refine ⟨1769447945412205630848497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4718527854432548348929325 1769447945412205630848497)
              ·
                refine ⟨1327085959059154223136373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769447945412205630848497 1327085959059154223136373)
                ·
                  refine ⟨124414308661795708419035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1327085959059154223136373 124414308661795708419035)
                  ·
                    rfl

theorem cell23_2180664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 5].length) (baseStart_2180664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180664 prefixEnd_2180664 := by exact prefixLift 2180664
  have htrace : WordTrace (prefixWord ++ tailWord_2180664) baseStart_2180664 baseEnd_2180664 := by
    simpa [prefixWord, tailWord_2180664, baseEnd_2180664] using wordTrace_append hprefix tailTrace_2180664
  have hstable : (prefixWord ++ tailWord_2180664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180664).length < 2 ^ (prefixWord ++ tailWord_2180664).sum := by decide
  have hdescent : baseEnd_2180664 < baseStart_2180664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180737 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 6]
def baseStart_2180737 : Nat := 118140960795 + 2180737 * 2 ^ 59
def prefixEnd_2180737 : Nat := 4983230072969 + 3 ^ 40 * 2180737 * 2
def baseEnd_2180737 : Nat := 124418473560437732239831

theorem tailTrace_2180737 : CollatzResearch.WordTrace tailWord_2180737 prefixEnd_2180737 124418473560437732239831 := by
  unfold tailWord_2180737
  simp only [CollatzResearch.WordTrace]
  refine ⟨79538012700569764073228465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53025341800379842715485643 79538012700569764073228465)
  ·
    refine ⟨59653509525427323054921349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79538012700569764073228465 59653509525427323054921349)
    ·
      refine ⟨11185033036017623072797753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59653509525427323054921349 11185033036017623072797753)
      ·
        refine ⟨8388774777013217304598315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11185033036017623072797753 8388774777013217304598315)
        ·
          refine ⟨12583162165519825956897473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388774777013217304598315 12583162165519825956897473)
          ·
            refine ⟨9437371624139869467673105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12583162165519825956897473 9437371624139869467673105)
            ·
              refine ⟨7078028718104902100754829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9437371624139869467673105 7078028718104902100754829)
              ·
                refine ⟨2654260769289338287783061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7078028718104902100754829 2654260769289338287783061)
                ·
                  refine ⟨124418473560437732239831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2654260769289338287783061 124418473560437732239831)
                  ·
                    rfl

theorem cell23_2180737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_2180737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180737 prefixEnd_2180737 := by exact prefixLift 2180737
  have htrace : WordTrace (prefixWord ++ tailWord_2180737) baseStart_2180737 baseEnd_2180737 := by
    simpa [prefixWord, tailWord_2180737, baseEnd_2180737] using wordTrace_append hprefix tailTrace_2180737
  have hstable : (prefixWord ++ tailWord_2180737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180737).length < 2 ^ (prefixWord ++ tailWord_2180737).sum := by decide
  have hdescent : baseEnd_2180737 < baseStart_2180737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180781 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2180781 : Nat := 118140960795 + 2180781 * 2 ^ 59
def prefixEnd_2180781 : Nat := 4983230072969 + 3 ^ 40 * 2180781 * 2
def baseEnd_2180781 : Nat := 1119788855192737418008277

theorem tailTrace_2180781 : CollatzResearch.WordTrace tailWord_2180781 prefixEnd_2180781 1119788855192737418008277 := by
  unfold tailWord_2180781
  simp only [CollatzResearch.WordTrace]
  refine ⟨79539617512410359587830197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53026411674940239725220131 79539617512410359587830197)
  ·
    refine ⟨7456839141788471211359081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79539617512410359587830197 7456839141788471211359081)
    ·
      refine ⟨5592629356341353408519311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7456839141788471211359081 5592629356341353408519311)
      ·
        refine ⟨8388944034512030112778967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592629356341353408519311 8388944034512030112778967)
        ·
          refine ⟨12583416051768045169168451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388944034512030112778967 12583416051768045169168451)
          ·
            refine ⟨18875124077652067753752677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583416051768045169168451 18875124077652067753752677)
            ·
              refine ⟨3539085764559762703828627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18875124077652067753752677 3539085764559762703828627)
              ·
                refine ⟨5308628646839644055742941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539085764559762703828627 5308628646839644055742941)
                ·
                  refine ⟨1990735742564866520903603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5308628646839644055742941 1990735742564866520903603)
                  ·
                    refine ⟨2986103613847299781355405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1990735742564866520903603 2986103613847299781355405)
                    ·
                      refine ⟨1119788855192737418008277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2986103613847299781355405 1119788855192737418008277)
                      ·
                        rfl

theorem cell23_2180781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2180781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180781 prefixEnd_2180781 := by exact prefixLift 2180781
  have htrace : WordTrace (prefixWord ++ tailWord_2180781) baseStart_2180781 baseEnd_2180781 := by
    simpa [prefixWord, tailWord_2180781, baseEnd_2180781] using wordTrace_append hprefix tailTrace_2180781
  have hstable : (prefixWord ++ tailWord_2180781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180781).length < 2 ^ (prefixWord ++ tailWord_2180781).sum := by decide
  have hdescent : baseEnd_2180781 < baseStart_2180781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180804 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_2180804 : Nat := 118140960795 + 2180804 * 2 ^ 59
def prefixEnd_2180804 : Nat := 4983230072969 + 3 ^ 40 * 2180804 * 2
def baseEnd_2180804 : Nat := 1119800665247790828020671

theorem tailTrace_2180804 : CollatzResearch.WordTrace tailWord_2180804 prefixEnd_2180804 1119800665247790828020671 := by
  unfold tailWord_2180804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39770228195663517257958733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53026970927551356343944977 39770228195663517257958733)
  ·
    refine ⟨14913835573373818971734525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39770228195663517257958733 14913835573373818971734525)
    ·
      refine ⟨5592688340015182114400447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14913835573373818971734525 5592688340015182114400447)
      ·
        refine ⟨8389032510022773171600671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592688340015182114400447 8389032510022773171600671)
        ·
          refine ⟨12583548765034159757401007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8389032510022773171600671 12583548765034159757401007)
          ·
            refine ⟨18875323147551239636101511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583548765034159757401007 18875323147551239636101511)
            ·
              refine ⟨28312984721326859454152267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18875323147551239636101511 28312984721326859454152267)
              ·
                refine ⟨42469477081990289181228401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28312984721326859454152267 42469477081990289181228401)
                ·
                  refine ⟨31852107811492716885921301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42469477081990289181228401 31852107811492716885921301)
                  ·
                    refine ⟨1493067553663721104027561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31852107811492716885921301 1493067553663721104027561)
                    ·
                      refine ⟨1119800665247790828020671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493067553663721104027561 1119800665247790828020671)
                      ·
                        rfl

theorem cell23_2180804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_2180804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180804 prefixEnd_2180804 := by exact prefixLift 2180804
  have htrace : WordTrace (prefixWord ++ tailWord_2180804) baseStart_2180804 baseEnd_2180804 := by
    simpa [prefixWord, tailWord_2180804, baseEnd_2180804] using wordTrace_append hprefix tailTrace_2180804
  have hstable : (prefixWord ++ tailWord_2180804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180804).length < 2 ^ (prefixWord ++ tailWord_2180804).sum := by decide
  have hdescent : baseEnd_2180804 < baseStart_2180804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180824 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2180824 : Nat := 118140960795 + 2180824 * 2 ^ 59
def prefixEnd_2180824 : Nat := 4983230072969 + 3 ^ 40 * 2180824 * 2
def baseEnd_2180824 : Nat := 1119810934860880749770579

theorem tailTrace_2180824 : CollatzResearch.WordTrace tailWord_2180824 prefixEnd_2180824 1119810934860880749770579 := by
  unfold tailWord_2180824
  simp only [CollatzResearch.WordTrace]
  refine ⟨39770592925627288965822763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53027457234169718621097017 39770592925627288965822763)
  ·
    refine ⟨59655889388440933448734145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39770592925627288965822763 59655889388440933448734145)
    ·
      refine ⟨44741917041330700086550609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59655889388440933448734145 44741917041330700086550609)
      ·
        refine ⟨33556437780998025064912957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44741917041330700086550609 33556437780998025064912957)
        ·
          refine ⟨12583664167874259399342359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33556437780998025064912957 12583664167874259399342359)
          ·
            refine ⟨18875496251811389099013539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583664167874259399342359 18875496251811389099013539)
            ·
              refine ⟨28313244377717083648520309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18875496251811389099013539 28313244377717083648520309)
              ·
                refine ⟨2654366660410976592048779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28313244377717083648520309 2654366660410976592048779)
                ·
                  refine ⟨3981549990616464888073169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654366660410976592048779 3981549990616464888073169)
                  ·
                    refine ⟨2986162492962348666054877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3981549990616464888073169 2986162492962348666054877)
                    ·
                      refine ⟨1119810934860880749770579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2986162492962348666054877 1119810934860880749770579)
                      ·
                        rfl

theorem cell23_2180824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2180824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180824 prefixEnd_2180824 := by exact prefixLift 2180824
  have htrace : WordTrace (prefixWord ++ tailWord_2180824) baseStart_2180824 baseEnd_2180824 := by
    simpa [prefixWord, tailWord_2180824, baseEnd_2180824] using wordTrace_append hprefix tailTrace_2180824
  have hstable : (prefixWord ++ tailWord_2180824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180824).length < 2 ^ (prefixWord ++ tailWord_2180824).sum := by decide
  have hdescent : baseEnd_2180824 < baseStart_2180824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180864 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2]
def baseStart_2180864 : Nat := 118140960795 + 2180864 * 2 ^ 59
def prefixEnd_2180864 : Nat := 4983230072969 + 3 ^ 40 * 2180864 * 2
def baseEnd_2180864 : Nat := 1119831474087060593270395

theorem tailTrace_2180864 : CollatzResearch.WordTrace tailWord_2180864 prefixEnd_2180864 1119831474087060593270395 := by
  unfold tailWord_2180864
  simp only [CollatzResearch.WordTrace]
  refine ⟨39771322385554832381550823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53028429847406443175401097 39771322385554832381550823)
  ·
    refine ⟨59656983578332248572326235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39771322385554832381550823 59656983578332248572326235)
    ·
      refine ⟨89485475367498372858489353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59656983578332248572326235 89485475367498372858489353)
      ·
        refine ⟨67114106525623779643867015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89485475367498372858489353 67114106525623779643867015)
        ·
          refine ⟨100671159788435669465800523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67114106525623779643867015 100671159788435669465800523)
          ·
            refine ⟨151006739682653504198700785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100671159788435669465800523 151006739682653504198700785)
            ·
              refine ⟨113255054761990128149025589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151006739682653504198700785 113255054761990128149025589)
              ·
                refine ⟨10617661383936574513971149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113255054761990128149025589 10617661383936574513971149)
                ·
                  refine ⟨3981623018976215442739181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10617661383936574513971149 3981623018976215442739181)
                  ·
                    refine ⟨1493108632116080791027193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3981623018976215442739181 1493108632116080791027193)
                    ·
                      refine ⟨1119831474087060593270395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493108632116080791027193 1119831474087060593270395)
                      ·
                        rfl

theorem cell23_2180864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_2180864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180864 prefixEnd_2180864 := by exact prefixLift 2180864
  have htrace : WordTrace (prefixWord ++ tailWord_2180864) baseStart_2180864 baseEnd_2180864 := by
    simpa [prefixWord, tailWord_2180864, baseEnd_2180864] using wordTrace_append hprefix tailTrace_2180864
  have hstable : (prefixWord ++ tailWord_2180864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180864).length < 2 ^ (prefixWord ++ tailWord_2180864).sum := by decide
  have hdescent : baseEnd_2180864 < baseStart_2180864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180871 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2180871 : Nat := 118140960795 + 2180871 * 2 ^ 59
def prefixEnd_2180871 : Nat := 4983230072969 + 3 ^ 40 * 2180871 * 2
def baseEnd_2180871 : Nat := 1119835068451642065882863

theorem tailTrace_2180871 : CollatzResearch.WordTrace tailWord_2180871 prefixEnd_2180871 1119835068451642065882863 := by
  unfold tailWord_2180871
  simp only [CollatzResearch.WordTrace]
  refine ⟨79542900082084304958606467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53028600054722869972404311 79542900082084304958606467)
  ·
    refine ⟨119314350123126457437909701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79542900082084304958606467 119314350123126457437909701)
    ·
      refine ⟨22371440648086210769608069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119314350123126457437909701 22371440648086210769608069)
      ·
        refine ⟨4194645121516164519301513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22371440648086210769608069 4194645121516164519301513)
        ·
          refine ⟨3145983841137123389476135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4194645121516164519301513 3145983841137123389476135)
          ·
            refine ⟨4718975761705685084214203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145983841137123389476135 4718975761705685084214203)
            ·
              refine ⟨7078463642558527626321305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718975761705685084214203 7078463642558527626321305)
              ·
                refine ⟨5308847731918895719740979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7078463642558527626321305 5308847731918895719740979)
                ·
                  refine ⟨7963271597878343579611469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308847731918895719740979 7963271597878343579611469)
                  ·
                    refine ⟨2986226849204378842354301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7963271597878343579611469 2986226849204378842354301)
                    ·
                      refine ⟨1119835068451642065882863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2986226849204378842354301 1119835068451642065882863)
                      ·
                        rfl

theorem cell23_2180871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2180871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180871 prefixEnd_2180871 := by exact prefixLift 2180871
  have htrace : WordTrace (prefixWord ++ tailWord_2180871) baseStart_2180871 baseEnd_2180871 := by
    simpa [prefixWord, tailWord_2180871, baseEnd_2180871] using wordTrace_append hprefix tailTrace_2180871
  have hstable : (prefixWord ++ tailWord_2180871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180871).length < 2 ^ (prefixWord ++ tailWord_2180871).sum := by decide
  have hdescent : baseEnd_2180871 < baseStart_2180871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180904 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2180904 : Nat := 118140960795 + 2180904 * 2 ^ 59
def prefixEnd_2180904 : Nat := 4983230072969 + 3 ^ 40 * 2180904 * 2
def baseEnd_2180904 : Nat := 373284004437746812256737

theorem tailTrace_2180904 : CollatzResearch.WordTrace tailWord_2180904 prefixEnd_2180904 373284004437746812256737 := by
  unfold tailWord_2180904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39772051845482375797278883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53029402460643167729705177 39772051845482375797278883)
  ·
    refine ⟨59658077768223563695918325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39772051845482375797278883 59658077768223563695918325)
    ·
      refine ⟨5592944790770959096492343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59658077768223563695918325 5592944790770959096492343)
      ·
        refine ⟨8389417186156438644738515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592944790770959096492343 8389417186156438644738515)
        ·
          refine ⟨12584125779234657967107773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8389417186156438644738515 12584125779234657967107773)
          ·
            refine ⟨4719047167212996737665415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12584125779234657967107773 4719047167212996737665415)
            ·
              refine ⟨7078570750819495106498123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4719047167212996737665415 7078570750819495106498123)
              ·
                refine ⟨10617856126229242659747185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7078570750819495106498123 10617856126229242659747185)
                ·
                  refine ⟨7963392094671931994810389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10617856126229242659747185 7963392094671931994810389)
                  ·
                    refine ⟨373284004437746812256737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7963392094671931994810389 373284004437746812256737)
                    ·
                      rfl

theorem cell23_2180904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2180904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180904 prefixEnd_2180904 := by exact prefixLift 2180904
  have htrace : WordTrace (prefixWord ++ tailWord_2180904) baseStart_2180904 baseEnd_2180904 := by
    simpa [prefixWord, tailWord_2180904, baseEnd_2180904] using wordTrace_append hprefix tailTrace_2180904
  have hstable : (prefixWord ++ tailWord_2180904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180904).length < 2 ^ (prefixWord ++ tailWord_2180904).sum := by decide
  have hdescent : baseEnd_2180904 < baseStart_2180904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180941 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2180941 : Nat := 118140960795 + 2180941 * 2 ^ 59
def prefixEnd_2180941 : Nat := 4983230072969 + 3 ^ 40 * 2180941 * 2
def baseEnd_2180941 : Nat := 1119871012097456792007541

theorem tailTrace_2180941 : CollatzResearch.WordTrace tailWord_2180941 prefixEnd_2180941 1119871012097456792007541 := by
  unfold tailWord_2180941
  simp only [CollatzResearch.WordTrace]
  refine ⟨79545453191830706913654677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53030302127887137942436451 79545453191830706913654677)
  ·
    refine ⟨3728693118367064386577563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79545453191830706913654677 3728693118367064386577563)
    ·
      refine ⟨5593039677550596579866345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728693118367064386577563 5593039677550596579866345)
      ·
        refine ⟨4194779758162947434899759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5593039677550596579866345 4194779758162947434899759)
        ·
          refine ⟨6292169637244421152349639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194779758162947434899759 6292169637244421152349639)
          ·
            refine ⟨9438254455866631728524459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292169637244421152349639 9438254455866631728524459)
            ·
              refine ⟨14157381683799947592786689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9438254455866631728524459 14157381683799947592786689)
              ·
                refine ⟨10618036262849960694590017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14157381683799947592786689 10618036262849960694590017)
                ·
                  refine ⟨7963527197137470520942513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10618036262849960694590017 7963527197137470520942513)
                  ·
                    refine ⟨5972645397853102890706885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7963527197137470520942513 5972645397853102890706885)
                    ·
                      refine ⟨1119871012097456792007541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5972645397853102890706885 1119871012097456792007541)
                      ·
                        rfl

theorem cell23_2180941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2180941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180941 prefixEnd_2180941 := by exact prefixLift 2180941
  have htrace : WordTrace (prefixWord ++ tailWord_2180941) baseStart_2180941 baseEnd_2180941 := by
    simpa [prefixWord, tailWord_2180941, baseEnd_2180941] using wordTrace_append hprefix tailTrace_2180941
  have hstable : (prefixWord ++ tailWord_2180941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180941).length < 2 ^ (prefixWord ++ tailWord_2180941).sum := by decide
  have hdescent : baseEnd_2180941 < baseStart_2180941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180945 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_2180945 : Nat := 118140960795 + 2180945 * 2 ^ 59
def prefixEnd_2180945 : Nat := 4983230072969 + 3 ^ 40 * 2180945 * 2
def baseEnd_2180945 : Nat := 1119873066020074776357523

theorem tailTrace_2180945 : CollatzResearch.WordTrace tailWord_2180945 prefixEnd_2180945 1119873066020074776357523 := by
  unfold tailWord_2180945
  simp only [CollatzResearch.WordTrace]
  refine ⟨79545599083816215596800289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53030399389210810397866859 79545599083816215596800289)
  ·
    refine ⟨59659199312862161697600217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79545599083816215596800289 59659199312862161697600217)
    ·
      refine ⟨44744399484646621273200163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59659199312862161697600217 44744399484646621273200163)
      ·
        refine ⟨67116599226969931909800245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44744399484646621273200163 67116599226969931909800245)
        ·
          refine ⟨6292181177528431116543773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67116599226969931909800245 6292181177528431116543773)
          ·
            refine ⟨2359567941573161668703915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6292181177528431116543773 2359567941573161668703915)
            ·
              refine ⟨3539351912359742503055873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359567941573161668703915 3539351912359742503055873)
              ·
                refine ⟨2654513934269806877291905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3539351912359742503055873 2654513934269806877291905)
                ·
                  refine ⟨1990885450702355157968929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654513934269806877291905 1990885450702355157968929)
                  ·
                    refine ⟨1493164088026766368476697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990885450702355157968929 1493164088026766368476697)
                    ·
                      refine ⟨1119873066020074776357523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493164088026766368476697 1119873066020074776357523)
                      ·
                        rfl

theorem cell23_2180945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_2180945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180945 prefixEnd_2180945 := by exact prefixLift 2180945
  have htrace : WordTrace (prefixWord ++ tailWord_2180945) baseStart_2180945 baseEnd_2180945 := by
    simpa [prefixWord, tailWord_2180945, baseEnd_2180945] using wordTrace_append hprefix tailTrace_2180945
  have hstable : (prefixWord ++ tailWord_2180945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180945).length < 2 ^ (prefixWord ++ tailWord_2180945).sum := by decide
  have hdescent : baseEnd_2180945 < baseStart_2180945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180962 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2180962 : Nat := 118140960795 + 2180962 * 2 ^ 59
def prefixEnd_2180962 : Nat := 4983230072969 + 3 ^ 40 * 2180962 * 2
def baseEnd_2180962 : Nat := 1119881795191201209844945

theorem tailTrace_2180962 : CollatzResearch.WordTrace tailWord_2180962 prefixEnd_2180962 1119881795191201209844945 := by
  unfold tailWord_2180962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19886554781188656875042285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53030812749836418333446093 19886554781188656875042285)
  ·
    refine ⟨7457458042945746328140857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19886554781188656875042285 7457458042945746328140857)
    ·
      refine ⟨5593093532209309746105643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457458042945746328140857 5593093532209309746105643)
      ·
        refine ⟨8389640298313964619158465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5593093532209309746105643 8389640298313964619158465)
        ·
          refine ⟨6292230223735473464368849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8389640298313964619158465 6292230223735473464368849)
          ·
            refine ⟨4719172667801605098276637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6292230223735473464368849 4719172667801605098276637)
            ·
              refine ⟨1769689750425601911853739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4719172667801605098276637 1769689750425601911853739)
              ·
                refine ⟨2654534625638402867780609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769689750425601911853739 2654534625638402867780609)
                ·
                  refine ⟨1990900969228802150835457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654534625638402867780609 1990900969228802150835457)
                  ·
                    refine ⟨1493175726921601613126593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990900969228802150835457 1493175726921601613126593)
                    ·
                      refine ⟨1119881795191201209844945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493175726921601613126593 1119881795191201209844945)
                      ·
                        rfl

theorem cell23_2180962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2180962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180962 prefixEnd_2180962 := by exact prefixLift 2180962
  have htrace : WordTrace (prefixWord ++ tailWord_2180962) baseStart_2180962 baseEnd_2180962 := by
    simpa [prefixWord, tailWord_2180962, baseEnd_2180962] using wordTrace_append hprefix tailTrace_2180962
  have hstable : (prefixWord ++ tailWord_2180962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180962).length < 2 ^ (prefixWord ++ tailWord_2180962).sum := by decide
  have hdescent : baseEnd_2180962 < baseStart_2180962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180977 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2180977 : Nat := 118140960795 + 2180977 * 2 ^ 59
def prefixEnd_2180977 : Nat := 4983230072969 + 3 ^ 40 * 2180977 * 2
def baseEnd_2180977 : Nat := 373296499133672883719125

theorem tailTrace_2180977 : CollatzResearch.WordTrace tailWord_2180977 prefixEnd_2180977 373296499133672883719125 := by
  unfold tailWord_2180977
  simp only [CollatzResearch.WordTrace]
  refine ⟨79546766219700285061965185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53031177479800190041310123 79546766219700285061965185)
  ·
    refine ⟨59660074664775213796473889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79546766219700285061965185 59660074664775213796473889)
    ·
      refine ⟨44745055998581410347355417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59660074664775213796473889 44745055998581410347355417)
      ·
        refine ⟨33558791998936057760516563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44745055998581410347355417 33558791998936057760516563)
        ·
          refine ⟨50338187998404086640774845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33558791998936057760516563 50338187998404086640774845)
          ·
            refine ⟨18876820499401532490290567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50338187998404086640774845 18876820499401532490290567)
            ·
              refine ⟨28315230749102298735435851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18876820499401532490290567 28315230749102298735435851)
              ·
                refine ⟨42472846123653448103153777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28315230749102298735435851 42472846123653448103153777)
                ·
                  refine ⟨31854634592740086077365333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42472846123653448103153777 31854634592740086077365333)
                  ·
                    refine ⟨373296499133672883719125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31854634592740086077365333 373296499133672883719125)
                    ·
                      rfl

theorem cell23_2180977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2180977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180977 prefixEnd_2180977 := by exact prefixLift 2180977
  have htrace : WordTrace (prefixWord ++ tailWord_2180977) baseStart_2180977 baseEnd_2180977 := by
    simpa [prefixWord, tailWord_2180977, baseEnd_2180977] using wordTrace_append hprefix tailTrace_2180977
  have hstable : (prefixWord ++ tailWord_2180977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180977).length < 2 ^ (prefixWord ++ tailWord_2180977).sum := by decide
  have hdescent : baseEnd_2180977 < baseStart_2180977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180987 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_2180987 : Nat := 118140960795 + 2180987 * 2 ^ 59
def prefixEnd_2180987 : Nat := 4983230072969 + 3 ^ 40 * 2180987 * 2
def baseEnd_2180987 : Nat := 1119894632207563612032329

theorem tailTrace_2180987 : CollatzResearch.WordTrace tailWord_2180987 prefixEnd_2180987 1119894632207563612032329 := by
  unfold tailWord_2180987
  simp only [CollatzResearch.WordTrace]
  refine ⟨79547130949664056769829215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53031420633109371179886143 79547130949664056769829215)
  ·
    refine ⟨119320696424496085154743823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79547130949664056769829215 119320696424496085154743823)
    ·
      refine ⟨178981044636744127732115735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119320696424496085154743823 178981044636744127732115735)
      ·
        refine ⟨268471566955116191598173603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178981044636744127732115735 268471566955116191598173603)
        ·
          refine ⟨402707350432674287397260405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268471566955116191598173603 402707350432674287397260405)
          ·
            refine ⟨37753814103063214443493163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 402707350432674287397260405 37753814103063214443493163)
            ·
              refine ⟨56630721154594821665239745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37753814103063214443493163 56630721154594821665239745)
              ·
                refine ⟨42473040865946116248929809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56630721154594821665239745 42473040865946116248929809)
                ·
                  refine ⟨31854780649459587186697357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42473040865946116248929809 31854780649459587186697357)
                  ·
                    refine ⟨11945542743547345195011509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31854780649459587186697357 11945542743547345195011509)
                    ·
                      refine ⟨1119894632207563612032329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11945542743547345195011509 1119894632207563612032329)
                      ·
                        rfl

theorem cell23_2180987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_2180987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2180987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2180987 prefixEnd_2180987 := by exact prefixLift 2180987
  have htrace : WordTrace (prefixWord ++ tailWord_2180987) baseStart_2180987 baseEnd_2180987 := by
    simpa [prefixWord, tailWord_2180987, baseEnd_2180987] using wordTrace_append hprefix tailTrace_2180987
  have hstable : (prefixWord ++ tailWord_2180987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180987).length < 2 ^ (prefixWord ++ tailWord_2180987).sum := by decide
  have hdescent : baseEnd_2180987 < baseStart_2180987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_2181061 : Nat := 118140960795 + 2181061 * 2 ^ 59
def prefixEnd_2181061 : Nat := 4983230072969 + 3 ^ 40 * 2181061 * 2
def baseEnd_2181061 : Nat := 1119932629775996322506989

theorem tailTrace_2181061 : CollatzResearch.WordTrace tailWord_2181061 prefixEnd_2181061 1119932629775996322506989 := by
  unfold tailWord_2181061
  simp only [CollatzResearch.WordTrace]
  refine ⟨79549829951395967408023037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53033219967597311605348691 79549829951395967408023037)
  ·
    refine ⟨29831186231773487778008639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79549829951395967408023037 29831186231773487778008639)
    ·
      refine ⟨44746779347660231667012959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29831186231773487778008639 44746779347660231667012959)
      ·
        refine ⟨67120169021490347500519439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44746779347660231667012959 67120169021490347500519439)
        ·
          refine ⟨100680253532235521250779159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67120169021490347500519439 100680253532235521250779159)
          ·
            refine ⟨151020380298353281876168739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100680253532235521250779159 151020380298353281876168739)
            ·
              refine ⟨226530570447529922814253109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151020380298353281876168739 226530570447529922814253109)
              ·
                refine ⟨21237240979455930263836229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226530570447529922814253109 21237240979455930263836229)
                ·
                  refine ⟨3981982683647986924469293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21237240979455930263836229 3981982683647986924469293)
                  ·
                    refine ⟨1493243506367995096675985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3981982683647986924469293 1493243506367995096675985)
                    ·
                      refine ⟨1119932629775996322506989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493243506367995096675985 1119932629775996322506989)
                      ·
                        rfl

theorem cell23_2181061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_2181061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181061 prefixEnd_2181061 := by exact prefixLift 2181061
  have htrace : WordTrace (prefixWord ++ tailWord_2181061) baseStart_2181061 baseEnd_2181061 := by
    simpa [prefixWord, tailWord_2181061, baseEnd_2181061] using wordTrace_append hprefix tailTrace_2181061
  have hstable : (prefixWord ++ tailWord_2181061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181061).length < 2 ^ (prefixWord ++ tailWord_2181061).sum := by decide
  have hdescent : baseEnd_2181061 < baseStart_2181061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181085 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2181085 : Nat := 118140960795 + 2181085 * 2 ^ 59
def prefixEnd_2181085 : Nat := 4983230072969 + 3 ^ 40 * 2181085 * 2
def baseEnd_2181085 : Nat := 1119944953311704228606879

theorem tailTrace_2181085 : CollatzResearch.WordTrace tailWord_2181085 prefixEnd_2181085 1119944953311704228606879 := by
  unfold tailWord_2181085
  simp only [CollatzResearch.WordTrace]
  refine ⟨79550705303309019506896709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53033803535539346337931139 79550705303309019506896709)
  ·
    refine ⟨14915757244370441157543133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79550705303309019506896709 14915757244370441157543133)
    ·
      refine ⟨5593408966638915434078675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14915757244370441157543133 5593408966638915434078675)
      ·
        refine ⟨8390113449958373151118013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5593408966638915434078675 8390113449958373151118013)
        ·
          refine ⟨3146292543734389931669255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8390113449958373151118013 3146292543734389931669255)
          ·
            refine ⟨4719438815601584897503883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146292543734389931669255 4719438815601584897503883)
            ·
              refine ⟨7079158223402377346255825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4719438815601584897503883 7079158223402377346255825)
              ·
                refine ⟨5309368667551783009691869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7079158223402377346255825 5309368667551783009691869)
                ·
                  refine ⟨1991013250331918628634451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5309368667551783009691869 1991013250331918628634451)
                  ·
                    refine ⟨2986519875497877942951677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1991013250331918628634451 2986519875497877942951677)
                    ·
                      refine ⟨1119944953311704228606879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2986519875497877942951677 1119944953311704228606879)
                      ·
                        rfl

theorem cell23_2181085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2181085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181085 prefixEnd_2181085 := by exact prefixLift 2181085
  have htrace : WordTrace (prefixWord ++ tailWord_2181085) baseStart_2181085 baseEnd_2181085 := by
    simpa [prefixWord, tailWord_2181085, baseEnd_2181085] using wordTrace_append hprefix tailTrace_2181085
  have hstable : (prefixWord ++ tailWord_2181085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181085).length < 2 ^ (prefixWord ++ tailWord_2181085).sum := by decide
  have hdescent : baseEnd_2181085 < baseStart_2181085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181091 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2181091 : Nat := 118140960795 + 2181091 * 2 ^ 59
def prefixEnd_2181091 : Nat := 4983230072969 + 3 ^ 40 * 2181091 * 2
def baseEnd_2181091 : Nat := 1119948034195631205131851

theorem tailTrace_2181091 : CollatzResearch.WordTrace tailWord_2181091 prefixEnd_2181091 1119948034195631205131851 := by
  unfold tailWord_2181091
  simp only [CollatzResearch.WordTrace]
  refine ⟨79550924141287282531615127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53033949427524855021076751 79550924141287282531615127)
  ·
    refine ⟨119326386211930923797422691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79550924141287282531615127 119326386211930923797422691)
    ·
      refine ⟨178989579317896385696134037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119326386211930923797422691 178989579317896385696134037)
      ·
        refine ⟨8390136530526393079506283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 178989579317896385696134037 8390136530526393079506283)
        ·
          refine ⟨12585204795789589619259425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8390136530526393079506283 12585204795789589619259425)
          ·
            refine ⟨9438903596842192214444569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12585204795789589619259425 9438903596842192214444569)
            ·
              refine ⟨7079177697631644160833427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9438903596842192214444569 7079177697631644160833427)
              ·
                refine ⟨10618766546447466241250141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7079177697631644160833427 10618766546447466241250141)
                ·
                  refine ⟨3982037454917799840468803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10618766546447466241250141 3982037454917799840468803)
                  ·
                    refine ⟨5973056182376699760703205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3982037454917799840468803 5973056182376699760703205)
                    ·
                      refine ⟨1119948034195631205131851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5973056182376699760703205 1119948034195631205131851)
                      ·
                        rfl

theorem cell23_2181091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2181091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181091 prefixEnd_2181091 := by exact prefixLift 2181091
  have htrace : WordTrace (prefixWord ++ tailWord_2181091) baseStart_2181091 baseEnd_2181091 := by
    simpa [prefixWord, tailWord_2181091, baseEnd_2181091] using wordTrace_append hprefix tailTrace_2181091
  have hstable : (prefixWord ++ tailWord_2181091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181091).length < 2 ^ (prefixWord ++ tailWord_2181091).sum := by decide
  have hdescent : baseEnd_2181091 < baseStart_2181091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181102 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_2181102 : Nat := 118140960795 + 2181102 * 2 ^ 59
def prefixEnd_2181102 : Nat := 4983230072969 + 3 ^ 40 * 2181102 * 2
def baseEnd_2181102 : Nat := 1119953682482830662094301

theorem tailTrace_2181102 : CollatzResearch.WordTrace tailWord_2181102 prefixEnd_2181102 1119953682482830662094301 := by
  unfold tailWord_2181102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943915668030928926283195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53034216896164954273510373 9943915668030928926283195)
  ·
    refine ⟨14915873502046393389424793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9943915668030928926283195 14915873502046393389424793)
    ·
      refine ⟨11186905126534795042068595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14915873502046393389424793 11186905126534795042068595)
      ·
        refine ⟨16780357689802192563102893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11186905126534795042068595 16780357689802192563102893)
        ·
          refine ⟨6292634133675822211163585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16780357689802192563102893 6292634133675822211163585)
          ·
            refine ⟨4719475600256866658372689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6292634133675822211163585 4719475600256866658372689)
            ·
              refine ⟨3539606700192649993779517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4719475600256866658372689 3539606700192649993779517)
              ·
                refine ⟨1327352512572243747667319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3539606700192649993779517 1327352512572243747667319)
                ·
                  refine ⟨1991028768858365621500979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327352512572243747667319 1991028768858365621500979)
                  ·
                    refine ⟨2986543153287548432251469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1991028768858365621500979 2986543153287548432251469)
                    ·
                      refine ⟨1119953682482830662094301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2986543153287548432251469 1119953682482830662094301)
                      ·
                        rfl

theorem cell23_2181102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_2181102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181102 prefixEnd_2181102 := by exact prefixLift 2181102
  have htrace : WordTrace (prefixWord ++ tailWord_2181102) baseStart_2181102 baseEnd_2181102 := by
    simpa [prefixWord, tailWord_2181102, baseEnd_2181102] using wordTrace_append hprefix tailTrace_2181102
  have hstable : (prefixWord ++ tailWord_2181102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181102).length < 2 ^ (prefixWord ++ tailWord_2181102).sum := by decide
  have hdescent : baseEnd_2181102 < baseStart_2181102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181105 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 1, 5]
def baseStart_2181105 : Nat := 118140960795 + 2181105 * 2 ^ 59
def prefixEnd_2181105 : Nat := 4983230072969 + 3 ^ 40 * 2181105 * 2
def baseEnd_2181105 : Nat := 373318407641598050118929

theorem tailTrace_2181105 : CollatzResearch.WordTrace tailWord_2181105 prefixEnd_2181105 373318407641598050118929 := by
  unfold tailWord_2181105
  simp only [CollatzResearch.WordTrace]
  refine ⟨79551434763236562922624769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53034289842157708615083179 79551434763236562922624769)
  ·
    refine ⟨59663576072427422191968577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79551434763236562922624769 59663576072427422191968577)
    ·
      refine ⟨44747682054320566643976433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59663576072427422191968577 44747682054320566643976433)
      ·
        refine ⟨33560761540740424982982325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44747682054320566643976433 33560761540740424982982325)
        ·
          refine ⟨3146321394444414842154593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33560761540740424982982325 3146321394444414842154593)
          ·
            refine ⟨2359741045833311131615945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3146321394444414842154593 2359741045833311131615945)
            ·
              refine ⟨1769805784374983348711959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359741045833311131615945 1769805784374983348711959)
              ·
                refine ⟨2654708676562475023067939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769805784374983348711959 2654708676562475023067939)
                ·
                  refine ⟨3982063014843712534601909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654708676562475023067939 3982063014843712534601909)
                  ·
                    refine ⟨373318407641598050118929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3982063014843712534601909 373318407641598050118929)
                    ·
                      rfl

theorem cell23_2181105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_2181105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181105 prefixEnd_2181105 := by exact prefixLift 2181105
  have htrace : WordTrace (prefixWord ++ tailWord_2181105) baseStart_2181105 baseEnd_2181105 := by
    simpa [prefixWord, tailWord_2181105, baseEnd_2181105] using wordTrace_append hprefix tailTrace_2181105
  have hstable : (prefixWord ++ tailWord_2181105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181105).length < 2 ^ (prefixWord ++ tailWord_2181105).sum := by decide
  have hdescent : baseEnd_2181105 < baseStart_2181105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181125 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_2181125 : Nat := 118140960795 + 2181125 * 2 ^ 59
def prefixEnd_2181125 : Nat := 4983230072969 + 3 ^ 40 * 2181125 * 2
def baseEnd_2181125 : Nat := 1119965492537884072106695

theorem tailTrace_2181125 : CollatzResearch.WordTrace tailWord_2181125 prefixEnd_2181125 1119965492537884072106695 := by
  unfold tailWord_2181125
  simp only [CollatzResearch.WordTrace]
  refine ⟨79552164223164106338352829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53034776148776070892235219 79552164223164106338352829)
  ·
    refine ⟨29832061583686539876882311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79552164223164106338352829 29832061583686539876882311)
    ·
      refine ⟨44748092375529809815323467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29832061583686539876882311 44748092375529809815323467)
      ·
        refine ⟨67122138563294714722985201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44748092375529809815323467 67122138563294714722985201)
        ·
          refine ⟨50341603922471036042238901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67122138563294714722985201 50341603922471036042238901)
          ·
            refine ⟨4719525367731659628959897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50341603922471036042238901 4719525367731659628959897)
            ·
              refine ⟨3539644025798744721719923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4719525367731659628959897 3539644025798744721719923)
              ·
                refine ⟨5309466038698117082579885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539644025798744721719923 5309466038698117082579885)
                ·
                  refine ⟨1991049764511793905967457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5309466038698117082579885 1991049764511793905967457)
                  ·
                    refine ⟨1493287323383845429475593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1991049764511793905967457 1493287323383845429475593)
                    ·
                      refine ⟨1119965492537884072106695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493287323383845429475593 1119965492537884072106695)
                      ·
                        rfl

theorem cell23_2181125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_2181125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181125 prefixEnd_2181125 := by exact prefixLift 2181125
  have htrace : WordTrace (prefixWord ++ tailWord_2181125) baseStart_2181125 baseEnd_2181125 := by
    simpa [prefixWord, tailWord_2181125, baseEnd_2181125] using wordTrace_append hprefix tailTrace_2181125
  have hstable : (prefixWord ++ tailWord_2181125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181125).length < 2 ^ (prefixWord ++ tailWord_2181125).sum := by decide
  have hdescent : baseEnd_2181125 < baseStart_2181125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181148 : List Nat := [2, 2, 3, 1, 3, 3, 2, 7]
def baseStart_2181148 : Nat := 118140960795 + 2181148 * 2 ^ 59
def prefixEnd_2181148 : Nat := 4983230072969 + 3 ^ 40 * 2181148 * 2
def baseEnd_2181148 : Nat := 41480640836775462300707

theorem tailTrace_2181148 : CollatzResearch.WordTrace tailWord_2181148 prefixEnd_2181148 41480640836775462300707 := by
  unfold tailWord_2181148
  simp only [CollatzResearch.WordTrace]
  refine ⟨39776501551040390633220049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53035335401387187510960065 39776501551040390633220049)
  ·
    refine ⟨29832376163280292974915037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39776501551040390633220049 29832376163280292974915037)
    ·
      refine ⟨11187141061230109865593139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29832376163280292974915037 11187141061230109865593139)
      ·
        refine ⟨16780711591845164798389709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11187141061230109865593139 16780711591845164798389709)
        ·
          refine ⟨6292766846941936799396141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16780711591845164798389709 6292766846941936799396141)
          ·
            refine ⟨2359787567603226299773553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6292766846941936799396141 2359787567603226299773553)
            ·
              refine ⟨1769840675702419724830165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359787567603226299773553 1769840675702419724830165)
              ·
                refine ⟨41480640836775462300707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1769840675702419724830165 41480640836775462300707)
                ·
                  rfl

theorem cell23_2181148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 7].length) (baseStart_2181148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181148 prefixEnd_2181148 := by exact prefixLift 2181148
  have htrace : WordTrace (prefixWord ++ tailWord_2181148) baseStart_2181148 baseEnd_2181148 := by
    simpa [prefixWord, tailWord_2181148, baseEnd_2181148] using wordTrace_append hprefix tailTrace_2181148
  have hstable : (prefixWord ++ tailWord_2181148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181148).length < 2 ^ (prefixWord ++ tailWord_2181148).sum := by decide
  have hdescent : baseEnd_2181148 < baseStart_2181148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181181 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2181181 : Nat := 118140960795 + 2181181 * 2 ^ 59
def prefixEnd_2181181 : Nat := 4983230072969 + 3 ^ 40 * 2181181 * 2
def baseEnd_2181181 : Nat := 1119994247454535853006437

theorem tailTrace_2181181 : CollatzResearch.WordTrace tailWord_2181181 prefixEnd_2181181 1119994247454535853006437 := by
  unfold tailWord_2181181
  simp only [CollatzResearch.WordTrace]
  refine ⟨79554206710961227902391397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53036137807307485268260931 79554206710961227902391397)
  ·
    refine ⟨14916413758305230231698387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79554206710961227902391397 14916413758305230231698387)
    ·
      refine ⟨22374620637457845347547581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14916413758305230231698387 22374620637457845347547581)
      ·
        refine ⟨8390482739046692005330343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22374620637457845347547581 8390482739046692005330343)
        ·
          refine ⟨12585724108570038007995515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8390482739046692005330343 12585724108570038007995515)
          ·
            refine ⟨18878586162855057011993273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12585724108570038007995515 18878586162855057011993273)
            ·
              refine ⟨14158939622141292758994955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18878586162855057011993273 14158939622141292758994955)
              ·
                refine ⟨21238409433211939138492433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14158939622141292758994955 21238409433211939138492433)
                ·
                  refine ⟨15928807074908954353869325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21238409433211939138492433 15928807074908954353869325)
                  ·
                    refine ⟨5973302653090857882700997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15928807074908954353869325 5973302653090857882700997)
                    ·
                      refine ⟨1119994247454535853006437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5973302653090857882700997 1119994247454535853006437)
                      ·
                        rfl

theorem cell23_2181181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2181181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181181 prefixEnd_2181181 := by exact prefixLift 2181181
  have htrace : WordTrace (prefixWord ++ tailWord_2181181) baseStart_2181181 baseEnd_2181181 := by
    simpa [prefixWord, tailWord_2181181, baseEnd_2181181] using wordTrace_append hprefix tailTrace_2181181
  have hstable : (prefixWord ++ tailWord_2181181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181181).length < 2 ^ (prefixWord ++ tailWord_2181181).sum := by decide
  have hdescent : baseEnd_2181181 < baseStart_2181181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181232 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2]
def baseStart_2181232 : Nat := 118140960795 + 2181232 * 2 ^ 59
def prefixEnd_2181232 : Nat := 4983230072969 + 3 ^ 40 * 2181232 * 2
def baseEnd_2181232 : Nat := 1120020434967915153468703

theorem tailTrace_2181232 : CollatzResearch.WordTrace tailWord_2181232 prefixEnd_2181232 1120020434967915153468703 := by
  unfold tailWord_2181232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39778033416888231806248975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53037377889184309074998633 39778033416888231806248975)
  ·
    refine ⟨59667050125332347709373463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39778033416888231806248975 59667050125332347709373463)
    ·
      refine ⟨89500575187998521564060195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59667050125332347709373463 89500575187998521564060195)
      ·
        refine ⟨134250862781997782346090293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89500575187998521564060195 134250862781997782346090293)
        ·
          refine ⟨12586018385812292094945965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134250862781997782346090293 12586018385812292094945965)
          ·
            refine ⟨4719756894679609535604737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12586018385812292094945965 4719756894679609535604737)
            ·
              refine ⟨3539817671009707151703553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4719756894679609535604737 3539817671009707151703553)
              ·
                refine ⟨2654863253257280363777665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3539817671009707151703553 2654863253257280363777665)
                ·
                  refine ⟨1991147439942960272833249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654863253257280363777665 1991147439942960272833249)
                  ·
                    refine ⟨1493360579957220204624937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1991147439942960272833249 1493360579957220204624937)
                    ·
                      refine ⟨1120020434967915153468703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493360579957220204624937 1120020434967915153468703)
                      ·
                        rfl

theorem cell23_2181232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2].length) (baseStart_2181232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181232 prefixEnd_2181232 := by exact prefixLift 2181232
  have htrace : WordTrace (prefixWord ++ tailWord_2181232) baseStart_2181232 baseEnd_2181232 := by
    simpa [prefixWord, tailWord_2181232, baseEnd_2181232] using wordTrace_append hprefix tailTrace_2181232
  have hstable : (prefixWord ++ tailWord_2181232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181232).length < 2 ^ (prefixWord ++ tailWord_2181232).sum := by decide
  have hdescent : baseEnd_2181232 < baseStart_2181232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181300 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2181300 : Nat := 118140960795 + 2181300 * 2 ^ 59
def prefixEnd_2181300 : Nat := 4983230072969 + 3 ^ 40 * 2181300 * 2
def baseEnd_2181300 : Nat := 1120055351652420887418391

theorem tailTrace_2181300 : CollatzResearch.WordTrace tailWord_2181300 prefixEnd_2181300 1120055351652420887418391 := by
  unfold tailWord_2181300
  simp only [CollatzResearch.WordTrace]
  refine ⟨39779273498765055612986677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53039031331686740817315569 39779273498765055612986677)
  ·
    refine ⟨3729306890509223963717501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39779273498765055612986677 3729306890509223963717501)
    ·
      refine ⟨1398490083940958986394063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3729306890509223963717501 1398490083940958986394063)
      ·
        refine ⟨2097735125911438479591095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398490083940958986394063 2097735125911438479591095)
        ·
          refine ⟨3146602688867157719386643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097735125911438479591095 3146602688867157719386643)
          ·
            refine ⟨4719904033300736579079965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146602688867157719386643 4719904033300736579079965)
            ·
              refine ⟨1769964012487776217154987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4719904033300736579079965 1769964012487776217154987)
              ·
                refine ⟨2654946018731664325732481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769964012487776217154987 2654946018731664325732481)
                ·
                  refine ⟨1991209514048748244299361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654946018731664325732481 1991209514048748244299361)
                  ·
                    refine ⟨1493407135536561183224521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1991209514048748244299361 1493407135536561183224521)
                    ·
                      refine ⟨1120055351652420887418391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493407135536561183224521 1120055351652420887418391)
                      ·
                        rfl

theorem cell23_2181300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2181300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181300 prefixEnd_2181300 := by exact prefixLift 2181300
  have htrace : WordTrace (prefixWord ++ tailWord_2181300) baseStart_2181300 baseEnd_2181300 := by
    simpa [prefixWord, tailWord_2181300, baseEnd_2181300] using wordTrace_append hprefix tailTrace_2181300
  have hstable : (prefixWord ++ tailWord_2181300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181300).length < 2 ^ (prefixWord ++ tailWord_2181300).sum := by decide
  have hdescent : baseEnd_2181300 < baseStart_2181300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181349 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_2181349 : Nat := 118140960795 + 2181349 * 2 ^ 59
def prefixEnd_2181349 : Nat := 4983230072969 + 3 ^ 40 * 2181349 * 2
def baseEnd_2181349 : Nat := 373360170734830398568555

theorem tailTrace_2181349 : CollatzResearch.WordTrace tailWord_2181349 prefixEnd_2181349 373360170734830398568555 := by
  unfold tailWord_2181349
  simp only [CollatzResearch.WordTrace]
  refine ⟨79560334174352592594507101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53040222782901728396338067 79560334174352592594507101)
  ·
    refine ⟨29835125315382222222940163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79560334174352592594507101 29835125315382222222940163)
    ·
      refine ⟨44752687973073333334410245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29835125315382222222940163 44752687973073333334410245)
      ·
        refine ⟨8391128994951250000201921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44752687973073333334410245 8391128994951250000201921)
        ·
          refine ⟨6293346746213437500151441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8391128994951250000201921 6293346746213437500151441)
          ·
            refine ⟨4720010059660078125113581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6293346746213437500151441 4720010059660078125113581)
            ·
              refine ⟨1770003772372529296917593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4720010059660078125113581 1770003772372529296917593)
              ·
                refine ⟨1327502829279396972688195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770003772372529296917593 1327502829279396972688195)
                ·
                  refine ⟨1991254243919095459032293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327502829279396972688195 1991254243919095459032293)
                  ·
                    refine ⟨373360170734830398568555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991254243919095459032293 373360170734830398568555)
                    ·
                      rfl

theorem cell23_2181349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_2181349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181349 prefixEnd_2181349 := by exact prefixLift 2181349
  have htrace : WordTrace (prefixWord ++ tailWord_2181349) baseStart_2181349 baseEnd_2181349 := by
    simpa [prefixWord, tailWord_2181349, baseEnd_2181349] using wordTrace_append hprefix tailTrace_2181349
  have hstable : (prefixWord ++ tailWord_2181349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181349).length < 2 ^ (prefixWord ++ tailWord_2181349).sum := by decide
  have hdescent : baseEnd_2181349 < baseStart_2181349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181358 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2181358 : Nat := 118140960795 + 2181358 * 2 ^ 59
def prefixEnd_2181358 : Nat := 4983230072969 + 3 ^ 40 * 2181358 * 2
def baseEnd_2181358 : Nat := 373361711176793886831041

theorem tailTrace_2181358 : CollatzResearch.WordTrace tailWord_2181358 prefixEnd_2181358 373361711176793886831041 := by
  unfold tailWord_2181358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9945082803914998391448091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53040441620879991421056485 9945082803914998391448091)
  ·
    refine ⟨14917624205872497587172137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9945082803914998391448091 14917624205872497587172137)
    ·
      refine ⟨11188218154404373190379103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14917624205872497587172137 11188218154404373190379103)
      ·
        refine ⟨16782327231606559785568655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11188218154404373190379103 16782327231606559785568655)
        ·
          refine ⟨25173490847409839678352983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16782327231606559785568655 25173490847409839678352983)
          ·
            refine ⟨37760236271114759517529475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25173490847409839678352983 37760236271114759517529475)
            ·
              refine ⟨56640354406672139276294213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37760236271114759517529475 56640354406672139276294213)
              ·
                refine ⟨10620066451251026114305165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56640354406672139276294213 10620066451251026114305165)
                ·
                  refine ⟨3982524919219134792864437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10620066451251026114305165 3982524919219134792864437)
                  ·
                    refine ⟨373361711176793886831041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3982524919219134792864437 373361711176793886831041)
                    ·
                      rfl

theorem cell23_2181358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2181358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181358 prefixEnd_2181358 := by exact prefixLift 2181358
  have htrace : WordTrace (prefixWord ++ tailWord_2181358) baseStart_2181358 baseEnd_2181358 := by
    simpa [prefixWord, tailWord_2181358, baseEnd_2181358] using wordTrace_append hprefix tailTrace_2181358
  have hstable : (prefixWord ++ tailWord_2181358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181358).length < 2 ^ (prefixWord ++ tailWord_2181358).sum := by decide
  have hdescent : baseEnd_2181358 < baseStart_2181358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181362 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_2181362 : Nat := 118140960795 + 2181362 * 2 ^ 59
def prefixEnd_2181362 : Nat := 4983230072969 + 3 ^ 40 * 2181362 * 2
def baseEnd_2181362 : Nat := 124454131939222182760345

theorem tailTrace_2181362 : CollatzResearch.WordTrace tailWord_2181362 prefixEnd_2181362 124454131939222182760345 := by
  unfold tailWord_2181362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19890202080826373953682585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53040538882203663876486893 19890202080826373953682585)
  ·
    refine ⟨14917651560619780465261939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19890202080826373953682585 14917651560619780465261939)
    ·
      refine ⟨22376477340929670697892909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14917651560619780465261939 22376477340929670697892909)
      ·
        refine ⟨8391179002848626511709841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22376477340929670697892909 8391179002848626511709841)
        ·
          refine ⟨6293384252136469883782381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8391179002848626511709841 6293384252136469883782381)
          ·
            refine ⟨2360019094551176206418393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6293384252136469883782381 2360019094551176206418393)
            ·
              refine ⟨1770014320913382154813795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360019094551176206418393 1770014320913382154813795)
              ·
                refine ⟨2655021481370073232220693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770014320913382154813795 2655021481370073232220693)
                ·
                  refine ⟨124454131939222182760345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2655021481370073232220693 124454131939222182760345)
                  ·
                    rfl

theorem cell23_2181362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_2181362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181362 prefixEnd_2181362 := by exact prefixLift 2181362
  have htrace : WordTrace (prefixWord ++ tailWord_2181362) baseStart_2181362 baseEnd_2181362 := by
    simpa [prefixWord, tailWord_2181362, baseEnd_2181362] using wordTrace_append hprefix tailTrace_2181362
  have hstable : (prefixWord ++ tailWord_2181362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181362).length < 2 ^ (prefixWord ++ tailWord_2181362).sum := by decide
  have hdescent : baseEnd_2181362 < baseStart_2181362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181371 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 7, 6]
def baseStart_2181371 : Nat := 118140960795 + 2181371 * 2 ^ 59
def prefixEnd_2181371 : Nat := 4983230072969 + 3 ^ 40 * 2181371 * 2
def baseEnd_2181371 : Nat := 373363936259630036543521

theorem tailTrace_2181371 : CollatzResearch.WordTrace tailWord_2181371 prefixEnd_2181371 373363936259630036543521 := by
  unfold tailWord_2181371
  simp only [CollatzResearch.WordTrace]
  refine ⟨79561136580272890351807967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53040757720181926901205311 79561136580272890351807967)
  ·
    refine ⟨119341704870409335527711951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79561136580272890351807967 119341704870409335527711951)
    ·
      refine ⟨179012557305614003291567927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119341704870409335527711951 179012557305614003291567927)
      ·
        refine ⟨268518835958421004937351891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179012557305614003291567927 268518835958421004937351891)
        ·
          refine ⟨402778253937631507406027837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268518835958421004937351891 402778253937631507406027837)
          ·
            refine ⟨151041845226611815277260439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402778253937631507406027837 151041845226611815277260439)
            ·
              refine ⟨226562767839917722915890659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151041845226611815277260439 226562767839917722915890659)
              ·
                refine ⟨339844151759876584373835989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226562767839917722915890659 339844151759876584373835989)
                ·
                  refine ⟨7965097306872107446261781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 339844151759876584373835989 7965097306872107446261781)
                  ·
                    refine ⟨373363936259630036543521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7965097306872107446261781 373363936259630036543521)
                    ·
                      rfl

theorem cell23_2181371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_2181371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181371 prefixEnd_2181371 := by exact prefixLift 2181371
  have htrace : WordTrace (prefixWord ++ tailWord_2181371) baseStart_2181371 baseEnd_2181371 := by
    simpa [prefixWord, tailWord_2181371, baseEnd_2181371] using wordTrace_append hprefix tailTrace_2181371
  have hstable : (prefixWord ++ tailWord_2181371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181371).length < 2 ^ (prefixWord ++ tailWord_2181371).sum := by decide
  have hdescent : baseEnd_2181371 < baseStart_2181371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181388 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_2181388 : Nat := 118140960795 + 2181388 * 2 ^ 59
def prefixEnd_2181388 : Nat := 4983230072969 + 3 ^ 40 * 2181388 * 2
def baseEnd_2181388 : Nat := 373366845983338847705995

theorem tailTrace_2181388 : CollatzResearch.WordTrace tailWord_2181388 prefixEnd_2181388 373366845983338847705995 := by
  unfold tailWord_2181388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39780878310605651127588409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53041171080807534836784545 39780878310605651127588409)
  ·
    refine ⟨29835658732954238345691307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39780878310605651127588409 29835658732954238345691307)
    ·
      refine ⟨44753488099431357518536961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29835658732954238345691307 44753488099431357518536961)
      ·
        refine ⟨33565116074573518138902721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44753488099431357518536961 33565116074573518138902721)
        ·
          refine ⟨25173837055930138604177041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33565116074573518138902721 25173837055930138604177041)
          ·
            refine ⟨18880377791947603953132781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25173837055930138604177041 18880377791947603953132781)
            ·
              refine ⟨7080141671980351482424793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18880377791947603953132781 7080141671980351482424793)
              ·
                refine ⟨5310106253985263611818595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7080141671980351482424793 5310106253985263611818595)
                ·
                  refine ⟨7965159380977895417727893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310106253985263611818595 7965159380977895417727893)
                  ·
                    refine ⟨373366845983338847705995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7965159380977895417727893 373366845983338847705995)
                    ·
                      rfl

theorem cell23_2181388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_2181388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181388 prefixEnd_2181388 := by exact prefixLift 2181388
  have htrace : WordTrace (prefixWord ++ tailWord_2181388) baseStart_2181388 baseEnd_2181388 := by
    simpa [prefixWord, tailWord_2181388, baseEnd_2181388] using wordTrace_append hprefix tailTrace_2181388
  have hstable : (prefixWord ++ tailWord_2181388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181388).length < 2 ^ (prefixWord ++ tailWord_2181388).sum := by decide
  have hdescent : baseEnd_2181388 < baseStart_2181388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181455 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 5, 3, 2]
def baseStart_2181455 : Nat := 118140960795 + 2181455 * 2 ^ 59
def prefixEnd_2181455 : Nat := 4983230072969 + 3 ^ 40 * 2181455 * 2
def baseEnd_2181455 : Nat := 1120134941153867780980177

theorem tailTrace_2181455 : CollatzResearch.WordTrace tailWord_2181455 prefixEnd_2181455 1120134941153867780980177 := by
  unfold tailWord_2181455
  simp only [CollatzResearch.WordTrace]
  refine ⟨79564200311968572697865819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53042800207979048465243879 79564200311968572697865819)
  ·
    refine ⟨119346300467952859046798729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79564200311968572697865819 119346300467952859046798729)
    ·
      refine ⟨89509725350964644285099047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119346300467952859046798729 89509725350964644285099047)
      ·
        refine ⟨134264588026446966427648571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89509725350964644285099047 134264588026446966427648571)
        ·
          refine ⟨201396882039670449641472857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134264588026446966427648571 201396882039670449641472857)
          ·
            refine ⟨151047661529752837231104643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201396882039670449641472857 151047661529752837231104643)
            ·
              refine ⟨226571492294629255846656965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151047661529752837231104643 226571492294629255846656965)
              ·
                refine ⟨42482154805242985471248181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226571492294629255846656965 42482154805242985471248181)
                ·
                  refine ⟨3982702012991529887929517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42482154805242985471248181 3982702012991529887929517)
                  ·
                    refine ⟨1493513254871823707973569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3982702012991529887929517 1493513254871823707973569)
                    ·
                      refine ⟨1120134941153867780980177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493513254871823707973569 1120134941153867780980177)
                      ·
                        rfl

theorem cell23_2181455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3, 2].length) (baseStart_2181455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181455 prefixEnd_2181455 := by exact prefixLift 2181455
  have htrace : WordTrace (prefixWord ++ tailWord_2181455) baseStart_2181455 baseEnd_2181455 := by
    simpa [prefixWord, tailWord_2181455, baseEnd_2181455] using wordTrace_append hprefix tailTrace_2181455
  have hstable : (prefixWord ++ tailWord_2181455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181455).length < 2 ^ (prefixWord ++ tailWord_2181455).sum := by decide
  have hdescent : baseEnd_2181455 < baseStart_2181455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181505 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2181505 : Nat := 118140960795 + 2181505 * 2 ^ 59
def prefixEnd_2181505 : Nat := 4983230072969 + 3 ^ 40 * 2181505 * 2
def baseEnd_2181505 : Nat := 1120160615186592585354947

theorem tailTrace_2181505 : CollatzResearch.WordTrace tailWord_2181505 prefixEnd_2181505 1120160615186592585354947 := by
  unfold tailWord_2181505
  simp only [CollatzResearch.WordTrace]
  refine ⟨79566023961787431237185969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53044015974524954158123979 79566023961787431237185969)
  ·
    refine ⟨59674517971340573427889477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79566023961787431237185969 59674517971340573427889477)
    ·
      refine ⟨11188972119626357517729277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59674517971340573427889477 11188972119626357517729277)
      ·
        refine ⟨4195864544859884069148479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11188972119626357517729277 4195864544859884069148479)
        ·
          refine ⟨6293796817289826103722719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195864544859884069148479 6293796817289826103722719)
          ·
            refine ⟨9440695225934739155584079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293796817289826103722719 9440695225934739155584079)
            ·
              refine ⟨14161042838902108733376119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9440695225934739155584079 14161042838902108733376119)
              ·
                refine ⟨21241564258353163100064179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14161042838902108733376119 21241564258353163100064179)
                ·
                  refine ⟨31862346387529744650096269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21241564258353163100064179 31862346387529744650096269)
                  ·
                    refine ⟨11948379895323654243786101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31862346387529744650096269 11948379895323654243786101)
                    ·
                      refine ⟨1120160615186592585354947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11948379895323654243786101 1120160615186592585354947)
                      ·
                        rfl

theorem cell23_2181505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2181505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181505 prefixEnd_2181505 := by exact prefixLift 2181505
  have htrace : WordTrace (prefixWord ++ tailWord_2181505) baseStart_2181505 baseEnd_2181505 := by
    simpa [prefixWord, tailWord_2181505, baseEnd_2181505] using wordTrace_append hprefix tailTrace_2181505
  have hstable : (prefixWord ++ tailWord_2181505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181505).length < 2 ^ (prefixWord ++ tailWord_2181505).sum := by decide
  have hdescent : baseEnd_2181505 < baseStart_2181505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181535 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2181535 : Nat := 118140960795 + 2181535 * 2 ^ 59
def prefixEnd_2181535 : Nat := 4983230072969 + 3 ^ 40 * 2181535 * 2
def baseEnd_2181535 : Nat := 1120176019606227467979809

theorem tailTrace_2181535 : CollatzResearch.WordTrace tailWord_2181535 prefixEnd_2181535 1120176019606227467979809 := by
  unfold tailWord_2181535
  simp only [CollatzResearch.WordTrace]
  refine ⟨79567118151678746360778059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53044745434452497573852039 79567118151678746360778059)
  ·
    refine ⟨119350677227518119541167089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79567118151678746360778059 119350677227518119541167089)
    ·
      refine ⟨89513007920638589655875317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119350677227518119541167089 89513007920638589655875317)
      ·
        refine ⟨8391844492559867780238311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89513007920638589655875317 8391844492559867780238311)
        ·
          refine ⟨12587766738839801670357467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8391844492559867780238311 12587766738839801670357467)
          ·
            refine ⟨18881650108259702505536201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12587766738839801670357467 18881650108259702505536201)
            ·
              refine ⟨14161237581194776879152151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18881650108259702505536201 14161237581194776879152151)
              ·
                refine ⟨21241856371792165318728227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14161237581194776879152151 21241856371792165318728227)
                ·
                  refine ⟨31862784557688247978092341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21241856371792165318728227 31862784557688247978092341)
                  ·
                    refine ⟨2987136052283273247946157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31862784557688247978092341 2987136052283273247946157)
                    ·
                      refine ⟨1120176019606227467979809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2987136052283273247946157 1120176019606227467979809)
                      ·
                        rfl

theorem cell23_2181535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2181535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181535 prefixEnd_2181535 := by exact prefixLift 2181535
  have htrace : WordTrace (prefixWord ++ tailWord_2181535) baseStart_2181535 baseEnd_2181535 := by
    simpa [prefixWord, tailWord_2181535, baseEnd_2181535] using wordTrace_append hprefix tailTrace_2181535
  have hstable : (prefixWord ++ tailWord_2181535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181535).length < 2 ^ (prefixWord ++ tailWord_2181535).sum := by decide
  have hdescent : baseEnd_2181535 < baseStart_2181535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181536 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2]
def baseStart_2181536 : Nat := 118140960795 + 2181536 * 2 ^ 59
def prefixEnd_2181536 : Nat := 4983230072969 + 3 ^ 40 * 2181536 * 2
def baseEnd_2181536 : Nat := 1120176533086881964067305

theorem tailTrace_2181536 : CollatzResearch.WordTrace tailWord_2181536 prefixEnd_2181536 1120176533086881964067305 := by
  unfold tailWord_2181536
  simp only [CollatzResearch.WordTrace]
  refine ⟨39783577312337561765782231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53044769749783415687709641 39783577312337561765782231)
  ·
    refine ⟨59675365968506342648673347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39783577312337561765782231 59675365968506342648673347)
    ·
      refine ⟨89513048952759513973010021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59675365968506342648673347 89513048952759513973010021)
      ·
        refine ⟨16783696678642408869939379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89513048952759513973010021 16783696678642408869939379)
        ·
          refine ⟨25175545017963613304909069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16783696678642408869939379 25175545017963613304909069)
          ·
            refine ⟨9440829381736354989340901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25175545017963613304909069 9440829381736354989340901)
            ·
              refine ⟨1770155509075566560501419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9440829381736354989340901 1770155509075566560501419)
              ·
                refine ⟨2655233263613349840752129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770155509075566560501419 2655233263613349840752129)
                ·
                  refine ⟨1991424947710012380564097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2655233263613349840752129 1991424947710012380564097)
                  ·
                    refine ⟨1493568710782509285423073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1991424947710012380564097 1493568710782509285423073)
                    ·
                      refine ⟨1120176533086881964067305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493568710782509285423073 1120176533086881964067305)
                      ·
                        rfl

theorem cell23_2181536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_2181536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181536 prefixEnd_2181536 := by exact prefixLift 2181536
  have htrace : WordTrace (prefixWord ++ tailWord_2181536) baseStart_2181536 baseEnd_2181536 := by
    simpa [prefixWord, tailWord_2181536, baseEnd_2181536] using wordTrace_append hprefix tailTrace_2181536
  have hstable : (prefixWord ++ tailWord_2181536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181536).length < 2 ^ (prefixWord ++ tailWord_2181536).sum := by decide
  have hdescent : baseEnd_2181536 < baseStart_2181536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181548 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_2181548 : Nat := 118140960795 + 2181548 * 2 ^ 59
def prefixEnd_2181548 : Nat := 4983230072969 + 3 ^ 40 * 2181548 * 2
def baseEnd_2181548 : Nat := 1120182694854735917117249

theorem tailTrace_2181548 : CollatzResearch.WordTrace tailWord_2181548 prefixEnd_2181548 1120182694854735917117249 := by
  unfold tailWord_2181548
  simp only [CollatzResearch.WordTrace]
  refine ⟨39783796150315824790500649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53045061533754433054000865 39783796150315824790500649)
  ·
    refine ⟨29837847112736868592875487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39783796150315824790500649 29837847112736868592875487)
    ·
      refine ⟨44756770669105302889313231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29837847112736868592875487 44756770669105302889313231)
      ·
        refine ⟨67135156003657954333969847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44756770669105302889313231 67135156003657954333969847)
        ·
          refine ⟨100702734005486931500954771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67135156003657954333969847 100702734005486931500954771)
          ·
            refine ⟨151054101008230397251432157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100702734005486931500954771 151054101008230397251432157)
            ·
              refine ⟨56645287878086398969287059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151054101008230397251432157 56645287878086398969287059)
              ·
                refine ⟨84967931817129598453930589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56645287878086398969287059 84967931817129598453930589)
                ·
                  refine ⟨31862974431423599420223971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84967931817129598453930589 31862974431423599420223971)
                  ·
                    refine ⟨47794461647135399130335957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31862974431423599420223971 47794461647135399130335957)
                    ·
                      refine ⟨1120182694854735917117249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47794461647135399130335957 1120182694854735917117249)
                      ·
                        rfl

theorem cell23_2181548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_2181548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181548 prefixEnd_2181548 := by exact prefixLift 2181548
  have htrace : WordTrace (prefixWord ++ tailWord_2181548) baseStart_2181548 baseEnd_2181548 := by
    simpa [prefixWord, tailWord_2181548, baseEnd_2181548] using wordTrace_append hprefix tailTrace_2181548
  have hstable : (prefixWord ++ tailWord_2181548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181548).length < 2 ^ (prefixWord ++ tailWord_2181548).sum := by decide
  have hdescent : baseEnd_2181548 < baseStart_2181548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181565 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2181565 : Nat := 118140960795 + 2181565 * 2 ^ 59
def prefixEnd_2181565 : Nat := 4983230072969 + 3 ^ 40 * 2181565 * 2
def baseEnd_2181565 : Nat := 1120191424025862350604671

theorem tailTrace_2181565 : CollatzResearch.WordTrace tailWord_2181565 prefixEnd_2181565 1120191424025862350604671 := by
  unfold tailWord_2181565
  simp only [CollatzResearch.WordTrace]
  refine ⟨79568212341570061484370149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53045474894380040989580099 79568212341570061484370149)
  ·
    refine ⟨14919039814044386528319403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79568212341570061484370149 14919039814044386528319403)
    ·
      refine ⟨22378559721066579792479105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14919039814044386528319403 22378559721066579792479105)
      ·
        refine ⟨16783919790799934844359329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22378559721066579792479105 16783919790799934844359329)
        ·
          refine ⟨12587939843099951133269497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16783919790799934844359329 12587939843099951133269497)
          ·
            refine ⟨9440954882324963349952123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12587939843099951133269497 9440954882324963349952123)
            ·
              refine ⟨14161432323487445024928185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9440954882324963349952123 14161432323487445024928185)
              ·
                refine ⟨10621074242615583768696139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14161432323487445024928185 10621074242615583768696139)
                ·
                  refine ⟨15931611363923375653044209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10621074242615583768696139 15931611363923375653044209)
                  ·
                    refine ⟨11948708522942531739783157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15931611363923375653044209 11948708522942531739783157)
                    ·
                      refine ⟨1120191424025862350604671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11948708522942531739783157 1120191424025862350604671)
                      ·
                        rfl

theorem cell23_2181565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2181565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181565 prefixEnd_2181565 := by exact prefixLift 2181565
  have htrace : WordTrace (prefixWord ++ tailWord_2181565) baseStart_2181565 baseEnd_2181565 := by
    simpa [prefixWord, tailWord_2181565, baseEnd_2181565] using wordTrace_append hprefix tailTrace_2181565
  have hstable : (prefixWord ++ tailWord_2181565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181565).length < 2 ^ (prefixWord ++ tailWord_2181565).sum := by decide
  have hdescent : baseEnd_2181565 < baseStart_2181565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181585 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_2181585 : Nat := 118140960795 + 2181585 * 2 ^ 59
def prefixEnd_2181585 : Nat := 4983230072969 + 3 ^ 40 * 2181585 * 2
def baseEnd_2181585 : Nat := 373400564546317424118193

theorem tailTrace_2181585 : CollatzResearch.WordTrace tailWord_2181585 prefixEnd_2181585 373400564546317424118193 := by
  unfold tailWord_2181585
  simp only [CollatzResearch.WordTrace]
  refine ⟨79568941801497604900098209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53045961200998403266732139 79568941801497604900098209)
  ·
    refine ⟨59676706351123203675073657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79568941801497604900098209 59676706351123203675073657)
    ·
      refine ⟨44757529763342402756305243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59676706351123203675073657 44757529763342402756305243)
      ·
        refine ⟨67136294645013604134457865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44757529763342402756305243 67136294645013604134457865)
        ·
          refine ⟨50352220983760203100843399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67136294645013604134457865 50352220983760203100843399)
          ·
            refine ⟨75528331475640304651265099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50352220983760203100843399 75528331475640304651265099)
            ·
              refine ⟨113292497213460456976897649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75528331475640304651265099 113292497213460456976897649)
              ·
                refine ⟨84969372910095342732673237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113292497213460456976897649 84969372910095342732673237)
                ·
                  refine ⟨1991469677580359595297029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 84969372910095342732673237 1991469677580359595297029)
                  ·
                    refine ⟨373400564546317424118193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991469677580359595297029 373400564546317424118193)
                    ·
                      rfl

theorem cell23_2181585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_2181585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181585 prefixEnd_2181585 := by exact prefixLift 2181585
  have htrace : WordTrace (prefixWord ++ tailWord_2181585) baseStart_2181585 baseEnd_2181585 := by
    simpa [prefixWord, tailWord_2181585, baseEnd_2181585] using wordTrace_append hprefix tailTrace_2181585
  have hstable : (prefixWord ++ tailWord_2181585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181585).length < 2 ^ (prefixWord ++ tailWord_2181585).sum := by decide
  have hdescent : baseEnd_2181585 < baseStart_2181585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181619 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 1, 4]
def baseStart_2181619 : Nat := 118140960795 + 2181619 * 2 ^ 59
def prefixEnd_2181619 : Nat := 4983230072969 + 3 ^ 40 * 2181619 * 2
def baseEnd_2181619 : Nat := 373406383993735046443141

theorem tailTrace_2181619 : CollatzResearch.WordTrace tailWord_2181619 prefixEnd_2181619 373406383993735046443141 := by
  unfold tailWord_2181619
  simp only [CollatzResearch.WordTrace]
  refine ⟨79570181883374428706835911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53046787922249619137890607 79570181883374428706835911)
  ·
    refine ⟨119355272825061643060253867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79570181883374428706835911 119355272825061643060253867)
    ·
      refine ⟨179032909237592464590380801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119355272825061643060253867 179032909237592464590380801)
      ·
        refine ⟨134274681928194348442785601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179032909237592464590380801 134274681928194348442785601)
        ·
          refine ⟨100706011446145761332089201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134274681928194348442785601 100706011446145761332089201)
          ·
            refine ⟨75529508584609320999066901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100706011446145761332089201 75529508584609320999066901)
            ·
              refine ⟨3540445714903561921831261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75529508584609320999066901 3540445714903561921831261)
              ·
                refine ⟨1327667143088835720686723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3540445714903561921831261 1327667143088835720686723)
                ·
                  refine ⟨1991500714633253581030085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327667143088835720686723 1991500714633253581030085)
                  ·
                    refine ⟨373406383993735046443141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991500714633253581030085 373406383993735046443141)
                    ·
                      rfl

theorem cell23_2181619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 4].length) (baseStart_2181619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181619 prefixEnd_2181619 := by exact prefixLift 2181619
  have htrace : WordTrace (prefixWord ++ tailWord_2181619) baseStart_2181619 baseEnd_2181619 := by
    simpa [prefixWord, tailWord_2181619, baseEnd_2181619] using wordTrace_append hprefix tailTrace_2181619
  have hstable : (prefixWord ++ tailWord_2181619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181619).length < 2 ^ (prefixWord ++ tailWord_2181619).sum := by decide
  have hdescent : baseEnd_2181619 < baseStart_2181619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181636 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_2181636 : Nat := 118140960795 + 2181636 * 2 ^ 59
def prefixEnd_2181636 : Nat := 4983230072969 + 3 ^ 40 * 2181636 * 2
def baseEnd_2181636 : Nat := 373409293717443857605615

theorem tailTrace_2181636 : CollatzResearch.WordTrace tailWord_2181636 prefixEnd_2181636 373409293717443857605615 := by
  unfold tailWord_2181636
  simp only [CollatzResearch.WordTrace]
  refine ⟨39785400962156420305102381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53047201282875227073469841 39785400962156420305102381)
  ·
    refine ⟨14919525360808657614413393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39785400962156420305102381 14919525360808657614413393)
    ·
      refine ⟨11189644020606493210810045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14919525360808657614413393 11189644020606493210810045)
      ·
        refine ⟨4196116507727434954053767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11189644020606493210810045 4196116507727434954053767)
        ·
          refine ⟨6294174761591152431080651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196116507727434954053767 6294174761591152431080651)
          ·
            refine ⟨9441262142386728646620977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294174761591152431080651 9441262142386728646620977)
            ·
              refine ⟨7080946606790046484965733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9441262142386728646620977 7080946606790046484965733)
              ·
                refine ⟨1327677488773133715931075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7080946606790046484965733 1327677488773133715931075)
                ·
                  refine ⟨1991516233159700573896613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327677488773133715931075 1991516233159700573896613)
                  ·
                    refine ⟨373409293717443857605615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991516233159700573896613 373409293717443857605615)
                    ·
                      rfl

theorem cell23_2181636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_2181636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181636 prefixEnd_2181636 := by exact prefixLift 2181636
  have htrace : WordTrace (prefixWord ++ tailWord_2181636) baseStart_2181636 baseEnd_2181636 := by
    simpa [prefixWord, tailWord_2181636, baseEnd_2181636] using wordTrace_append hprefix tailTrace_2181636
  have hstable : (prefixWord ++ tailWord_2181636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181636).length < 2 ^ (prefixWord ++ tailWord_2181636).sum := by decide
  have hdescent : baseEnd_2181636 < baseStart_2181636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181675 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 1, 6]
def baseStart_2181675 : Nat := 118140960795 + 2181675 * 2 ^ 59
def prefixEnd_2181675 : Nat := 4983230072969 + 3 ^ 40 * 2181675 * 2
def baseEnd_2181675 : Nat := 373415968965952306743055

theorem tailTrace_2181675 : CollatzResearch.WordTrace tailWord_2181675 prefixEnd_2181675 373415968965952306743055 := by
  unfold tailWord_2181675
  simp only [CollatzResearch.WordTrace]
  refine ⟨79572224371171550270874479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53048149580781033513916319 79572224371171550270874479)
  ·
    refine ⟨119358336556757325406311719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79572224371171550270874479 119358336556757325406311719)
    ·
      refine ⟨179037504835135988109467579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119358336556757325406311719 179037504835135988109467579)
      ·
        refine ⟨268556257252703982164201369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179037504835135988109467579 268556257252703982164201369)
        ·
          refine ⟨201417192939527986623151027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268556257252703982164201369 201417192939527986623151027)
          ·
            refine ⟨302125789409291979934726541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201417192939527986623151027 302125789409291979934726541)
            ·
              refine ⟨113297171028484492475522453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302125789409291979934726541 113297171028484492475522453)
              ·
                refine ⟨5310804891960210584790115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113297171028484492475522453 5310804891960210584790115)
                ·
                  refine ⟨7966207337940315877185173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310804891960210584790115 7966207337940315877185173)
                  ·
                    refine ⟨373415968965952306743055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7966207337940315877185173 373415968965952306743055)
                    ·
                      rfl

theorem cell23_2181675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 6].length) (baseStart_2181675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181675 prefixEnd_2181675 := by exact prefixLift 2181675
  have htrace : WordTrace (prefixWord ++ tailWord_2181675) baseStart_2181675 baseEnd_2181675 := by
    simpa [prefixWord, tailWord_2181675, baseEnd_2181675] using wordTrace_append hprefix tailTrace_2181675
  have hstable : (prefixWord ++ tailWord_2181675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181675).length < 2 ^ (prefixWord ++ tailWord_2181675).sum := by decide
  have hdescent : baseEnd_2181675 < baseStart_2181675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181686 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2181686 : Nat := 118140960795 + 2181686 * 2 ^ 59
def prefixEnd_2181686 : Nat := 4983230072969 + 3 ^ 40 * 2181686 * 2
def baseEnd_2181686 : Nat := 1120253555185056377191615

theorem tailTrace_2181686 : CollatzResearch.WordTrace tailWord_2181686 prefixEnd_2181686 1120253555185056377191615 := by
  unfold tailWord_2181686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973289098383231196845307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53048417049421132766349941 4973289098383231196845307)
  ·
    refine ⟨7459933647574846795267961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4973289098383231196845307 7459933647574846795267961)
    ·
      refine ⟨5594950235681135096450971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7459933647574846795267961 5594950235681135096450971)
      ·
        refine ⟨8392425353521702644676457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594950235681135096450971 8392425353521702644676457)
        ·
          refine ⟨6294319015141276983507343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8392425353521702644676457 6294319015141276983507343)
          ·
            refine ⟨9441478522711915475261015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294319015141276983507343 9441478522711915475261015)
            ·
              refine ⟨14162217784067873212891523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9441478522711915475261015 14162217784067873212891523)
              ·
                refine ⟨21243326676101809819337285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14162217784067873212891523 21243326676101809819337285)
                ·
                  refine ⟨3983123751769089341125741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21243326676101809819337285 3983123751769089341125741)
                  ·
                    refine ⟨1493671406913408502922153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3983123751769089341125741 1493671406913408502922153)
                    ·
                      refine ⟨1120253555185056377191615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493671406913408502922153 1120253555185056377191615)
                      ·
                        rfl

theorem cell23_2181686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2181686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181686 prefixEnd_2181686 := by exact prefixLift 2181686
  have htrace : WordTrace (prefixWord ++ tailWord_2181686) baseStart_2181686 baseEnd_2181686 := by
    simpa [prefixWord, tailWord_2181686, baseEnd_2181686] using wordTrace_append hprefix tailTrace_2181686
  have hstable : (prefixWord ++ tailWord_2181686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181686).length < 2 ^ (prefixWord ++ tailWord_2181686).sum := by decide
  have hdescent : baseEnd_2181686 < baseStart_2181686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181695 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_2181695 : Nat := 118140960795 + 2181695 * 2 ^ 59
def prefixEnd_2181695 : Nat := 4983230072969 + 3 ^ 40 * 2181695 * 2
def baseEnd_2181695 : Nat := 1120258176510946841979073

theorem tailTrace_2181695 : CollatzResearch.WordTrace tailWord_2181695 prefixEnd_2181695 1120258176510946841979073 := by
  unfold tailWord_2181695
  simp only [CollatzResearch.WordTrace]
  refine ⟨79572953831099093686602539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53048635887399395791068359 79572953831099093686602539)
  ·
    refine ⟨119359430746648640529903809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79572953831099093686602539 119359430746648640529903809)
    ·
      refine ⟨89519573059986480397427857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119359430746648640529903809 89519573059986480397427857)
      ·
        refine ⟨67139679794989860298070893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89519573059986480397427857 67139679794989860298070893)
        ·
          refine ⟨25177379923121197611776585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67139679794989860298070893 25177379923121197611776585)
          ·
            refine ⟨18883034942340898208832439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25177379923121197611776585 18883034942340898208832439)
            ·
              refine ⟨28324552413511347313248659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18883034942340898208832439 28324552413511347313248659)
              ·
                refine ⟨42486828620267020969872989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28324552413511347313248659 42486828620267020969872989)
                ·
                  refine ⟨15932560732600132863702371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42486828620267020969872989 15932560732600132863702371)
                  ·
                    refine ⟨23898841098900199295553557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15932560732600132863702371 23898841098900199295553557)
                    ·
                      refine ⟨1120258176510946841979073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23898841098900199295553557 1120258176510946841979073)
                      ·
                        rfl

theorem cell23_2181695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_2181695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181695 prefixEnd_2181695 := by exact prefixLift 2181695
  have htrace : WordTrace (prefixWord ++ tailWord_2181695) baseStart_2181695 baseEnd_2181695 := by
    simpa [prefixWord, tailWord_2181695, baseEnd_2181695] using wordTrace_append hprefix tailTrace_2181695
  have hstable : (prefixWord ++ tailWord_2181695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181695).length < 2 ^ (prefixWord ++ tailWord_2181695).sum := by decide
  have hdescent : baseEnd_2181695 < baseStart_2181695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181700 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 6]
def baseStart_2181700 : Nat := 118140960795 + 2181700 * 2 ^ 59
def prefixEnd_2181700 : Nat := 4983230072969 + 3 ^ 40 * 2181700 * 2
def baseEnd_2181700 : Nat := 124473415990468813601839

theorem tailTrace_2181700 : CollatzResearch.WordTrace tailWord_2181700 prefixEnd_2181700 124473415990468813601839 := by
  unfold tailWord_2181700
  simp only [CollatzResearch.WordTrace]
  refine ⟨39786568098040489770267277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53048757464053986360356369 39786568098040489770267277)
  ·
    refine ⟨14919963036765183663850229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39786568098040489770267277 14919963036765183663850229)
    ·
      refine ⟨1398746534696735968485959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14919963036765183663850229 1398746534696735968485959)
      ·
        refine ⟨2098119802045103952728939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398746534696735968485959 2098119802045103952728939)
        ·
          refine ⟨3147179703067655929093409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098119802045103952728939 3147179703067655929093409)
          ·
            refine ⟨2360384777300741946820057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147179703067655929093409 2360384777300741946820057)
            ·
              refine ⟨1770288582975556460115043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360384777300741946820057 1770288582975556460115043)
              ·
                refine ⟨2655432874463334690172565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770288582975556460115043 2655432874463334690172565)
                ·
                  refine ⟨124473415990468813601839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2655432874463334690172565 124473415990468813601839)
                  ·
                    rfl

theorem cell23_2181700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_2181700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181700 prefixEnd_2181700 := by exact prefixLift 2181700
  have htrace : WordTrace (prefixWord ++ tailWord_2181700) baseStart_2181700 baseEnd_2181700 := by
    simpa [prefixWord, tailWord_2181700, baseEnd_2181700] using wordTrace_append hprefix tailTrace_2181700
  have hstable : (prefixWord ++ tailWord_2181700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181700).length < 2 ^ (prefixWord ++ tailWord_2181700).sum := by decide
  have hdescent : baseEnd_2181700 < baseStart_2181700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181716 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2181716 : Nat := 118140960795 + 2181716 * 2 ^ 59
def prefixEnd_2181716 : Nat := 4983230072969 + 3 ^ 40 * 2181716 * 2
def baseEnd_2181716 : Nat := 1120268959604691259816477

theorem tailTrace_2181716 : CollatzResearch.WordTrace tailWord_2181716 prefixEnd_2181716 1120268959604691259816477 := by
  unfold tailWord_2181716
  simp only [CollatzResearch.WordTrace]
  refine ⟨39786859882011507136558501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53049146509348676182078001 39786859882011507136558501)
  ·
    refine ⟨7460036227877157588104719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39786859882011507136558501 7460036227877157588104719)
    ·
      refine ⟨11190054341815736382157079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460036227877157588104719 11190054341815736382157079)
      ·
        refine ⟨16785081512723604573235619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11190054341815736382157079 16785081512723604573235619)
        ·
          refine ⟨25177622269085406859853429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16785081512723604573235619 25177622269085406859853429)
          ·
            refine ⟨2360402087726756893111259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25177622269085406859853429 2360402087726756893111259)
            ·
              refine ⟨3540603131590135339666889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360402087726756893111259 3540603131590135339666889)
              ·
                refine ⟨2655452348692601504750167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540603131590135339666889 2655452348692601504750167)
                ·
                  refine ⟨3983178523038902257125251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655452348692601504750167 3983178523038902257125251)
                  ·
                    refine ⟨5974767784558353385687877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983178523038902257125251 5974767784558353385687877)
                    ·
                      refine ⟨1120268959604691259816477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5974767784558353385687877 1120268959604691259816477)
                      ·
                        rfl

theorem cell23_2181716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2181716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181716 prefixEnd_2181716 := by exact prefixLift 2181716
  have htrace : WordTrace (prefixWord ++ tailWord_2181716) baseStart_2181716 baseEnd_2181716 := by
    simpa [prefixWord, tailWord_2181716, baseEnd_2181716] using wordTrace_append hprefix tailTrace_2181716
  have hstable : (prefixWord ++ tailWord_2181716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181716).length < 2 ^ (prefixWord ++ tailWord_2181716).sum := by decide
  have hdescent : baseEnd_2181716 < baseStart_2181716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181736 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2181736 : Nat := 118140960795 + 2181736 * 2 ^ 59
def prefixEnd_2181736 : Nat := 4983230072969 + 3 ^ 40 * 2181736 * 2
def baseEnd_2181736 : Nat := 1120279229217781181566385

theorem tailTrace_2181736 : CollatzResearch.WordTrace tailWord_2181736 prefixEnd_2181736 1120279229217781181566385 := by
  unfold tailWord_2181736
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787224611975278844422531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53049632815967038459230041 39787224611975278844422531)
  ·
    refine ⟨59680836917962918266633797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39787224611975278844422531 59680836917962918266633797)
    ·
      refine ⟨11190156922118047174993837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59680836917962918266633797 11190156922118047174993837)
      ·
        refine ⟨4196308845794267690622689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11190156922118047174993837 4196308845794267690622689)
        ·
          refine ⟨3147231634345700767967017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4196308845794267690622689 3147231634345700767967017)
          ·
            refine ⟨2360423725759275575975263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147231634345700767967017 2360423725759275575975263)
            ·
              refine ⟨3540635588638913363962895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360423725759275575975263 3540635588638913363962895)
              ·
                refine ⟨5310953382958370045944343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540635588638913363962895 5310953382958370045944343)
                ·
                  refine ⟨7966430074437555068916515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310953382958370045944343 7966430074437555068916515)
                  ·
                    refine ⟨11949645111656332603374773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7966430074437555068916515 11949645111656332603374773)
                    ·
                      refine ⟨1120279229217781181566385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11949645111656332603374773 1120279229217781181566385)
                      ·
                        rfl

theorem cell23_2181736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2181736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181736 prefixEnd_2181736 := by exact prefixLift 2181736
  have htrace : WordTrace (prefixWord ++ tailWord_2181736) baseStart_2181736 baseEnd_2181736 := by
    simpa [prefixWord, tailWord_2181736, baseEnd_2181736] using wordTrace_append hprefix tailTrace_2181736
  have hstable : (prefixWord ++ tailWord_2181736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181736).length < 2 ^ (prefixWord ++ tailWord_2181736).sum := by decide
  have hdescent : baseEnd_2181736 < baseStart_2181736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181745 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2181745 : Nat := 118140960795 + 2181745 * 2 ^ 59
def prefixEnd_2181745 : Nat := 4983230072969 + 3 ^ 40 * 2181745 * 2
def baseEnd_2181745 : Nat := 1120283850543671646353843

theorem tailTrace_2181745 : CollatzResearch.WordTrace tailWord_2181745 prefixEnd_2181745 1120283850543671646353843 := by
  unfold tailWord_2181745
  simp only [CollatzResearch.WordTrace]
  refine ⟨79574777480917952225922689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53049851653945301483948459 79574777480917952225922689)
  ·
    refine ⟨59681083110688464169442017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79574777480917952225922689 59681083110688464169442017)
    ·
      refine ⟨44760812333016348127081513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59681083110688464169442017 44760812333016348127081513)
      ·
        refine ⟨33570609249762261095311135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44760812333016348127081513 33570609249762261095311135)
        ·
          refine ⟨50355913874643391642966703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33570609249762261095311135 50355913874643391642966703)
          ·
            refine ⟨75533870811965087464450055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50355913874643391642966703 75533870811965087464450055)
            ·
              refine ⟨113300806217947631196675083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75533870811965087464450055 113300806217947631196675083)
              ·
                refine ⟨169951209326921446795012625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113300806217947631196675083 169951209326921446795012625)
                ·
                  refine ⟨127463406995191085096259469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169951209326921446795012625 127463406995191085096259469)
                  ·
                    refine ⟨47798777623196656911097301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127463406995191085096259469 47798777623196656911097301)
                    ·
                      refine ⟨1120283850543671646353843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47798777623196656911097301 1120283850543671646353843)
                      ·
                        rfl

theorem cell23_2181745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2181745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181745 prefixEnd_2181745 := by exact prefixLift 2181745
  have htrace : WordTrace (prefixWord ++ tailWord_2181745) baseStart_2181745 baseEnd_2181745 := by
    simpa [prefixWord, tailWord_2181745, baseEnd_2181745] using wordTrace_append hprefix tailTrace_2181745
  have hstable : (prefixWord ++ tailWord_2181745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181745).length < 2 ^ (prefixWord ++ tailWord_2181745).sum := by decide
  have hdescent : baseEnd_2181745 < baseStart_2181745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181793 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2181793 : Nat := 118140960795 + 2181793 * 2 ^ 59
def prefixEnd_2181793 : Nat := 4983230072969 + 3 ^ 40 * 2181793 * 2
def baseEnd_2181793 : Nat := 1120308497615087458553623

theorem tailTrace_2181793 : CollatzResearch.WordTrace tailWord_2181793 prefixEnd_2181793 1120308497615087458553623 := by
  unfold tailWord_2181793
  simp only [CollatzResearch.WordTrace]
  refine ⟨79576528184744056423670033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53051018789829370949113355 79576528184744056423670033)
  ·
    refine ⟨59682396138558042317752525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79576528184744056423670033 59682396138558042317752525)
    ·
      refine ⟨22380898551959265869157197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59682396138558042317752525 22380898551959265869157197)
      ·
        refine ⟨8392836956984724700933949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22380898551959265869157197 8392836956984724700933949)
        ·
          refine ⟨3147313858869271762850231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8392836956984724700933949 3147313858869271762850231)
          ·
            refine ⟨4720970788303907644275347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147313858869271762850231 4720970788303907644275347)
            ·
              refine ⟨7081456182455861466413021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720970788303907644275347 7081456182455861466413021)
              ·
                refine ⟨2655546068420948049904883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7081456182455861466413021 2655546068420948049904883)
                ·
                  refine ⟨3983319102631422074857325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655546068420948049904883 3983319102631422074857325)
                  ·
                    refine ⟨1493744663486783278071497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3983319102631422074857325 1493744663486783278071497)
                    ·
                      refine ⟨1120308497615087458553623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493744663486783278071497 1120308497615087458553623)
                      ·
                        rfl

theorem cell23_2181793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2181793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181793 prefixEnd_2181793 := by exact prefixLift 2181793
  have htrace : WordTrace (prefixWord ++ tailWord_2181793) baseStart_2181793 baseEnd_2181793 := by
    simpa [prefixWord, tailWord_2181793, baseEnd_2181793] using wordTrace_append hprefix tailTrace_2181793
  have hstable : (prefixWord ++ tailWord_2181793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181793).length < 2 ^ (prefixWord ++ tailWord_2181793).sum := by decide
  have hdescent : baseEnd_2181793 < baseStart_2181793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
