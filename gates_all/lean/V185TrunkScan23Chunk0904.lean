import V185TrunkScan23Chunk0903

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5350729 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_5350729 : Nat := 118140960795 + 5350729 * 2 ^ 59
def prefixEnd_5350729 : Nat := 4983230072969 + 3 ^ 40 * 5350729 * 2
def baseEnd_5350729 : Nat := 2747495828951300981879951

theorem tailTrace_5350729 : CollatzResearch.WordTrace tailWord_5350729 prefixEnd_5350729 2747495828951300981879951 := by
  unfold tailWord_5350729
  simp only [CollatzResearch.WordTrace]
  refine ⟨195157119432230139604447241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130104746288153426402964827 195157119432230139604447241)
  ·
    refine ⟨146367839574172604703335431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195157119432230139604447241 146367839574172604703335431)
    ·
      refine ⟨219551759361258907055003147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146367839574172604703335431 219551759361258907055003147)
      ·
        refine ⟨329327639041888360582504721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219551759361258907055003147 329327639041888360582504721)
        ·
          refine ⟨246995729281416270436878541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329327639041888360582504721 246995729281416270436878541)
          ·
            refine ⟨92623398480531101413829453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246995729281416270436878541 92623398480531101413829453)
            ·
              refine ⟨34733774430199163030186045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92623398480531101413829453 34733774430199163030186045)
              ·
                refine ⟨13025165411324686136319767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34733774430199163030186045 13025165411324686136319767)
                ·
                  refine ⟨19537748116987029204479651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13025165411324686136319767 19537748116987029204479651)
                  ·
                    refine ⟨29306622175480543806719477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19537748116987029204479651 29306622175480543806719477)
                    ·
                      refine ⟨2747495828951300981879951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29306622175480543806719477 2747495828951300981879951)
                      ·
                        rfl

theorem cell23_5350729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_5350729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350729 prefixEnd_5350729 := by exact prefixLift 5350729
  have htrace : WordTrace (prefixWord ++ tailWord_5350729) baseStart_5350729 baseEnd_5350729 := by
    simpa [prefixWord, tailWord_5350729, baseEnd_5350729] using wordTrace_append hprefix tailTrace_5350729
  have hstable : (prefixWord ++ tailWord_5350729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350729).length < 2 ^ (prefixWord ++ tailWord_5350729).sum := by decide
  have hdescent : baseEnd_5350729 < baseStart_5350729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350736 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_5350736 : Nat := 118140960795 + 5350736 * 2 ^ 59
def prefixEnd_5350736 : Nat := 4983230072969 + 3 ^ 40 * 5350736 * 2
def baseEnd_5350736 : Nat := 915833141105294151497473

theorem tailTrace_5350736 : CollatzResearch.WordTrace tailWord_5350736 prefixEnd_5350736 915833141105294151497473 := by
  unfold tailWord_5350736
  simp only [CollatzResearch.WordTrace]
  refine ⟨97578687371602389899976031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130104916495469853199968041 97578687371602389899976031)
  ·
    refine ⟨146368031057403584849964047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97578687371602389899976031 146368031057403584849964047)
    ·
      refine ⟨219552046586105377274946071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146368031057403584849964047 219552046586105377274946071)
      ·
        refine ⟨329328069879158065912419107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219552046586105377274946071 329328069879158065912419107)
        ·
          refine ⟨493992104818737098868628661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329328069879158065912419107 493992104818737098868628661)
          ·
            refine ⟨46311759826756603018933937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 493992104818737098868628661 46311759826756603018933937)
            ·
              refine ⟨34733819870067452264200453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46311759826756603018933937 34733819870067452264200453)
              ·
                refine ⟨6512591225637647299537585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34733819870067452264200453 6512591225637647299537585)
                ·
                  refine ⟨4884443419228235474653189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6512591225637647299537585 4884443419228235474653189)
                  ·
                    refine ⟨915833141105294151497473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4884443419228235474653189 915833141105294151497473)
                    ·
                      rfl

theorem cell23_5350736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_5350736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350736 prefixEnd_5350736 := by exact prefixLift 5350736
  have htrace : WordTrace (prefixWord ++ tailWord_5350736) baseStart_5350736 baseEnd_5350736 := by
    simpa [prefixWord, tailWord_5350736, baseEnd_5350736] using wordTrace_append hprefix tailTrace_5350736
  have hstable : (prefixWord ++ tailWord_5350736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350736).length < 2 ^ (prefixWord ++ tailWord_5350736).sum := by decide
  have hdescent : baseEnd_5350736 < baseStart_5350736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350760 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5350760 : Nat := 118140960795 + 5350760 * 2 ^ 59
def prefixEnd_5350760 : Nat := 4983230072969 + 3 ^ 40 * 5350760 * 2
def baseEnd_5350760 : Nat := 2747511746851590360592309

theorem tailTrace_5350760 : CollatzResearch.WordTrace tailWord_5350760 prefixEnd_5350760 2747511746851590360592309 := by
  unfold tailWord_5350760
  simp only [CollatzResearch.WordTrace]
  refine ⟨97579125047558915949412867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130105500063411887932550489 97579125047558915949412867)
  ·
    refine ⟨146368687571338373924119301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97579125047558915949412867 146368687571338373924119301)
    ·
      refine ⟨27444128919625945110772369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146368687571338373924119301 27444128919625945110772369)
      ·
        refine ⟨20583096689719458833079277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27444128919625945110772369 20583096689719458833079277)
        ·
          refine ⟨7718661258644797062404729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20583096689719458833079277 7718661258644797062404729)
          ·
            refine ⟨5788995943983597796803547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7718661258644797062404729 5788995943983597796803547)
            ·
              refine ⟨8683493915975396695205321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788995943983597796803547 8683493915975396695205321)
              ·
                refine ⟨6512620436981547521403991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8683493915975396695205321 6512620436981547521403991)
                ·
                  refine ⟨9768930655472321282105987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512620436981547521403991 9768930655472321282105987)
                  ·
                    refine ⟨14653395983208481923158981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9768930655472321282105987 14653395983208481923158981)
                    ·
                      refine ⟨2747511746851590360592309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14653395983208481923158981 2747511746851590360592309)
                      ·
                        rfl

theorem cell23_5350760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5350760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350760 prefixEnd_5350760 := by exact prefixLift 5350760
  have htrace : WordTrace (prefixWord ++ tailWord_5350760) baseStart_5350760 baseEnd_5350760 := by
    simpa [prefixWord, tailWord_5350760, baseEnd_5350760] using wordTrace_append hprefix tailTrace_5350760
  have hstable : (prefixWord ++ tailWord_5350760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350760).length < 2 ^ (prefixWord ++ tailWord_5350760).sum := by decide
  have hdescent : baseEnd_5350760 < baseStart_5350760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350773 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5350773 : Nat := 118140960795 + 5350773 * 2 ^ 59
def prefixEnd_5350773 : Nat := 4983230072969 + 3 ^ 40 * 5350773 * 2
def baseEnd_5350773 : Nat := 2747518422100098809729749

theorem tailTrace_5350773 : CollatzResearch.WordTrace tailWord_5350773 prefixEnd_5350773 2747518422100098809729749 := by
  unfold tailWord_5350773
  simp only [CollatzResearch.WordTrace]
  refine ⟨195158724244070735119048973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130105816162713823412699315 195158724244070735119048973)
  ·
    refine ⟨73184521591526525669643365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195158724244070735119048973 73184521591526525669643365)
    ·
      refine ⟨13722097798411223563058131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73184521591526525669643365 13722097798411223563058131)
      ·
        refine ⟨20583146697616835344587197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13722097798411223563058131 20583146697616835344587197)
        ·
          refine ⟨7718680011606313254220199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20583146697616835344587197 7718680011606313254220199)
          ·
            refine ⟨11578020017409469881330299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718680011606313254220199 11578020017409469881330299)
            ·
              refine ⟨17367030026114204821995449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11578020017409469881330299 17367030026114204821995449)
              ·
                refine ⟨13025272519585653616496587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17367030026114204821995449 13025272519585653616496587)
                ·
                  refine ⟨19537908779378480424744881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13025272519585653616496587 19537908779378480424744881)
                  ·
                    refine ⟨14653431584533860318558661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19537908779378480424744881 14653431584533860318558661)
                    ·
                      refine ⟨2747518422100098809729749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14653431584533860318558661 2747518422100098809729749)
                      ·
                        rfl

theorem cell23_5350773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5350773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350773 prefixEnd_5350773 := by exact prefixLift 5350773
  have htrace : WordTrace (prefixWord ++ tailWord_5350773) baseStart_5350773 baseEnd_5350773 := by
    simpa [prefixWord, tailWord_5350773, baseEnd_5350773] using wordTrace_append hprefix tailTrace_5350773
  have hstable : (prefixWord ++ tailWord_5350773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350773).length < 2 ^ (prefixWord ++ tailWord_5350773).sum := by decide
  have hdescent : baseEnd_5350773 < baseStart_5350773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350789 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_5350789 : Nat := 118140960795 + 5350789 * 2 ^ 59
def prefixEnd_5350789 : Nat := 4983230072969 + 3 ^ 40 * 5350789 * 2
def baseEnd_5350789 : Nat := 2747526637790570747129675

theorem tailTrace_5350789 : CollatzResearch.WordTrace tailWord_5350789 prefixEnd_5350789 2747526637790570747129675 := by
  unfold tailWord_5350789
  simp only [CollatzResearch.WordTrace]
  refine ⟨195159307812012769851631421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130106205208008513234420947 195159307812012769851631421)
  ·
    refine ⟨73184740429504788694361783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195159307812012769851631421 73184740429504788694361783)
    ·
      refine ⟨109777110644257183041542675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73184740429504788694361783 109777110644257183041542675)
      ·
        refine ⟨164665665966385774562314013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109777110644257183041542675 164665665966385774562314013)
        ·
          refine ⟨61749624737394665460867755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164665665966385774562314013 61749624737394665460867755)
          ·
            refine ⟨92624437106091998191301633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61749624737394665460867755 92624437106091998191301633)
            ·
              refine ⟨69468327829568998643476225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92624437106091998191301633 69468327829568998643476225)
              ·
                refine ⟨52101245872176748982607169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69468327829568998643476225 52101245872176748982607169)
                ·
                  refine ⟨39075934404132561736955377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52101245872176748982607169 39075934404132561736955377)
                  ·
                    refine ⟨29306950803099421302716533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39075934404132561736955377 29306950803099421302716533)
                    ·
                      refine ⟨2747526637790570747129675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29306950803099421302716533 2747526637790570747129675)
                      ·
                        rfl

theorem cell23_5350789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_5350789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350789 prefixEnd_5350789 := by exact prefixLift 5350789
  have htrace : WordTrace (prefixWord ++ tailWord_5350789) baseStart_5350789 baseEnd_5350789 := by
    simpa [prefixWord, tailWord_5350789, baseEnd_5350789] using wordTrace_append hprefix tailTrace_5350789
  have hstable : (prefixWord ++ tailWord_5350789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350789).length < 2 ^ (prefixWord ++ tailWord_5350789).sum := by decide
  have hdescent : baseEnd_5350789 < baseStart_5350789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350809 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_5350809 : Nat := 118140960795 + 5350809 * 2 ^ 59
def prefixEnd_5350809 : Nat := 4983230072969 + 3 ^ 40 * 5350809 * 2
def baseEnd_5350809 : Nat := 915845635801220222959861

theorem tailTrace_5350809 : CollatzResearch.WordTrace tailWord_5350809 prefixEnd_5350809 915845635801220222959861 := by
  unfold tailWord_5350809
  simp only [CollatzResearch.WordTrace]
  refine ⟨195160037271940313267359481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130106691514626875511572987 195160037271940313267359481)
  ·
    refine ⟨146370027953955234950519611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195160037271940313267359481 146370027953955234950519611)
    ·
      refine ⟨219555041930932852425779417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146370027953955234950519611 219555041930932852425779417)
      ·
        refine ⟨164666281448199639319334563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219555041930932852425779417 164666281448199639319334563)
        ·
          refine ⟨246999422172299458979001845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164666281448199639319334563 246999422172299458979001845)
          ·
            refine ⟨23156195828653074279281423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246999422172299458979001845 23156195828653074279281423)
            ·
              refine ⟨34734293742979611418922135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23156195828653074279281423 34734293742979611418922135)
              ·
                refine ⟨52101440614469417128383203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34734293742979611418922135 52101440614469417128383203)
                ·
                  refine ⟨78152160921704125692574805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52101440614469417128383203 78152160921704125692574805)
                  ·
                    refine ⟨915845635801220222959861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78152160921704125692574805 915845635801220222959861)
                    ·
                      rfl

theorem cell23_5350809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_5350809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350809 prefixEnd_5350809 := by exact prefixLift 5350809
  have htrace : WordTrace (prefixWord ++ tailWord_5350809) baseStart_5350809 baseEnd_5350809 := by
    simpa [prefixWord, tailWord_5350809, baseEnd_5350809] using wordTrace_append hprefix tailTrace_5350809
  have hstable : (prefixWord ++ tailWord_5350809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350809).length < 2 ^ (prefixWord ++ tailWord_5350809).sum := by decide
  have hdescent : baseEnd_5350809 < baseStart_5350809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350833 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5350833 : Nat := 118140960795 + 5350833 * 2 ^ 59
def prefixEnd_5350833 : Nat := 4983230072969 + 3 ^ 40 * 5350833 * 2
def baseEnd_5350833 : Nat := 2747549230939368574979473

theorem tailTrace_5350833 : CollatzResearch.WordTrace tailWord_5350833 prefixEnd_5350833 2747549230939368574979473 := by
  unfold tailWord_5350833
  simp only [CollatzResearch.WordTrace]
  refine ⟨195160912623853365366233153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130107275082568910244155435 195160912623853365366233153)
  ·
    refine ⟨146370684467890024024674865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195160912623853365366233153 146370684467890024024674865)
    ·
      refine ⟨109778013350917518018506149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146370684467890024024674865 109778013350917518018506149)
      ·
        refine ⟨20583377503297034628469903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109778013350917518018506149 20583377503297034628469903)
        ·
          refine ⟨30875066254945551942704855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20583377503297034628469903 30875066254945551942704855)
          ·
            refine ⟨46312599382418327914057283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30875066254945551942704855 46312599382418327914057283)
            ·
              refine ⟨69468899073627491871085925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46312599382418327914057283 69468899073627491871085925)
              ·
                refine ⟨13025418576305154725828611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69468899073627491871085925 13025418576305154725828611)
                ·
                  refine ⟨19538127864457732088742917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13025418576305154725828611 19538127864457732088742917)
                  ·
                    refine ⟨3663398974585824766639297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19538127864457732088742917 3663398974585824766639297)
                    ·
                      refine ⟨2747549230939368574979473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663398974585824766639297 2747549230939368574979473)
                      ·
                        rfl

theorem cell23_5350833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5350833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350833 prefixEnd_5350833 := by exact prefixLift 5350833
  have htrace : WordTrace (prefixWord ++ tailWord_5350833) baseStart_5350833 baseEnd_5350833 := by
    simpa [prefixWord, tailWord_5350833, baseEnd_5350833] using wordTrace_append hprefix tailTrace_5350833
  have hstable : (prefixWord ++ tailWord_5350833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350833).length < 2 ^ (prefixWord ++ tailWord_5350833).sum := by decide
  have hdescent : baseEnd_5350833 < baseStart_5350833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350837 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_5350837 : Nat := 118140960795 + 5350837 * 2 ^ 59
def prefixEnd_5350837 : Nat := 4983230072969 + 3 ^ 40 * 5350837 * 2
def baseEnd_5350837 : Nat := 2747551284861986559329455

theorem tailTrace_5350837 : CollatzResearch.WordTrace tailWord_5350837 prefixEnd_5350837 2747551284861986559329455 := by
  unfold tailWord_5350837
  simp only [CollatzResearch.WordTrace]
  refine ⟨195161058515838874049378765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130107372343892582699585843 195161058515838874049378765)
  ·
    refine ⟨73185396943439577768517037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195161058515838874049378765 73185396943439577768517037)
    ·
      refine ⟨27444523853789841663193889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73185396943439577768517037 27444523853789841663193889)
      ·
        refine ⟨20583392890342381247395417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27444523853789841663193889 20583392890342381247395417)
        ·
          refine ⟨15437544667756785935546563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20583392890342381247395417 15437544667756785935546563)
          ·
            refine ⟨23156317001635178903319845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15437544667756785935546563 23156317001635178903319845)
            ·
              refine ⟨4341809437806596044372471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23156317001635178903319845 4341809437806596044372471)
              ·
                refine ⟨6512714156709894066558707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341809437806596044372471 6512714156709894066558707)
                ·
                  refine ⟨9769071235064841099838061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512714156709894066558707 9769071235064841099838061)
                  ·
                    refine ⟨3663401713149315412439273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9769071235064841099838061 3663401713149315412439273)
                    ·
                      refine ⟨2747551284861986559329455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663401713149315412439273 2747551284861986559329455)
                      ·
                        rfl

theorem cell23_5350837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_5350837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350837 prefixEnd_5350837 := by exact prefixLift 5350837
  have htrace : WordTrace (prefixWord ++ tailWord_5350837) baseStart_5350837 baseEnd_5350837 := by
    simpa [prefixWord, tailWord_5350837, baseEnd_5350837] using wordTrace_append hprefix tailTrace_5350837
  have hstable : (prefixWord ++ tailWord_5350837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350837).length < 2 ^ (prefixWord ++ tailWord_5350837).sum := by decide
  have hdescent : baseEnd_5350837 < baseStart_5350837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350839 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 9]
def baseStart_5350839 : Nat := 118140960795 + 5350839 * 2 ^ 59
def prefixEnd_5350839 : Nat := 4983230072969 + 3 ^ 40 * 5350839 * 2
def baseEnd_5350839 : Nat := 305283590202588394611605

theorem tailTrace_5350839 : CollatzResearch.WordTrace tailWord_5350839 prefixEnd_5350839 305283590202588394611605 := by
  unfold tailWord_5350839
  simp only [CollatzResearch.WordTrace]
  refine ⟨195161131461831628390951571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130107420974554418927301047 195161131461831628390951571)
  ·
    refine ⟨292741697192747442586427357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195161131461831628390951571 292741697192747442586427357)
    ·
      refine ⟨109778136447280290969910259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292741697192747442586427357 109778136447280290969910259)
      ·
        refine ⟨164667204670920436454865389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109778136447280290969910259 164667204670920436454865389)
        ·
          refine ⟨61750201751595163670574521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164667204670920436454865389 61750201751595163670574521)
          ·
            refine ⟨46312651313696372752930891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61750201751595163670574521 46312651313696372752930891)
            ·
              refine ⟨69468976970544559129396337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46312651313696372752930891 69468976970544559129396337)
              ·
                refine ⟨52101732727908419347047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69468976970544559129396337 52101732727908419347047253)
                ·
                  refine ⟨305283590202588394611605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52101732727908419347047253 305283590202588394611605)
                  ·
                    rfl

theorem cell23_5350839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 9].length) (baseStart_5350839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350839 prefixEnd_5350839 := by exact prefixLift 5350839
  have htrace : WordTrace (prefixWord ++ tailWord_5350839) baseStart_5350839 baseEnd_5350839 := by
    simpa [prefixWord, tailWord_5350839, baseEnd_5350839] using wordTrace_append hprefix tailTrace_5350839
  have hstable : (prefixWord ++ tailWord_5350839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350839).length < 2 ^ (prefixWord ++ tailWord_5350839).sum := by decide
  have hdescent : baseEnd_5350839 < baseStart_5350839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350844 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5350844 : Nat := 118140960795 + 5350844 * 2 ^ 59
def prefixEnd_5350844 : Nat := 4983230072969 + 3 ^ 40 * 5350844 * 2
def baseEnd_5350844 : Nat := 2747554879226568031941923

theorem tailTrace_5350844 : CollatzResearch.WordTrace tailWord_5350844 prefixEnd_5350844 2747554879226568031941923 := by
  unfold tailWord_5350844
  simp only [CollatzResearch.WordTrace]
  refine ⟨97580656913406757122441793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130107542551209009496589057 97580656913406757122441793)
  ·
    refine ⟨73185492685055067841831345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97580656913406757122441793 73185492685055067841831345)
    ·
      refine ⟨54889119513791300881373509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73185492685055067841831345 54889119513791300881373509)
      ·
        refine ⟨10291709908835868915257533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54889119513791300881373509 10291709908835868915257533)
        ·
          refine ⟨3859391215813450843221575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10291709908835868915257533 3859391215813450843221575)
          ·
            refine ⟨5789086823720176264832363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859391215813450843221575 5789086823720176264832363)
            ·
              refine ⟨8683630235580264397248545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789086823720176264832363 8683630235580264397248545)
              ·
                refine ⟨6512722676685198297936409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8683630235580264397248545 6512722676685198297936409)
                ·
                  refine ⟨4884542007513898723452307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6512722676685198297936409 4884542007513898723452307)
                  ·
                    refine ⟨7326813011270848085178461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4884542007513898723452307 7326813011270848085178461)
                    ·
                      refine ⟨2747554879226568031941923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326813011270848085178461 2747554879226568031941923)
                      ·
                        rfl

theorem cell23_5350844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5350844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350844 prefixEnd_5350844 := by exact prefixLift 5350844
  have htrace : WordTrace (prefixWord ++ tailWord_5350844) baseStart_5350844 baseEnd_5350844 := by
    simpa [prefixWord, tailWord_5350844, baseEnd_5350844] using wordTrace_append hprefix tailTrace_5350844
  have hstable : (prefixWord ++ tailWord_5350844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350844).length < 2 ^ (prefixWord ++ tailWord_5350844).sum := by decide
  have hdescent : baseEnd_5350844 < baseStart_5350844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350856 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 7]
def baseStart_5350856 : Nat := 118140960795 + 5350856 * 2 ^ 59
def prefixEnd_5350856 : Nat := 4983230072969 + 3 ^ 40 * 5350856 * 2
def baseEnd_5350856 : Nat := 305284560110491331665763

theorem tailTrace_5350856 : CollatzResearch.WordTrace tailWord_5350856 prefixEnd_5350856 305284560110491331665763 := by
  unfold tailWord_5350856
  simp only [CollatzResearch.WordTrace]
  refine ⟨97580875751385020147160211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130107834335180026862880281 97580875751385020147160211)
  ·
    refine ⟨146371313627077530220740317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97580875751385020147160211 146371313627077530220740317)
    ·
      refine ⟨54889242610154073832777619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146371313627077530220740317 54889242610154073832777619)
      ·
        refine ⟨82333863915231110749166429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54889242610154073832777619 82333863915231110749166429)
        ·
          refine ⟨30875198968211666530937411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82333863915231110749166429 30875198968211666530937411)
          ·
            refine ⟨46312798452317499796406117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30875198968211666530937411 46312798452317499796406117)
            ·
              refine ⟨8683649709809531211826147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46312798452317499796406117 8683649709809531211826147)
              ·
                refine ⟨13025474564714296817739221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8683649709809531211826147 13025474564714296817739221)
                ·
                  refine ⟨305284560110491331665763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13025474564714296817739221 305284560110491331665763)
                  ·
                    rfl

theorem cell23_5350856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_5350856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350856 prefixEnd_5350856 := by exact prefixLift 5350856
  have htrace : WordTrace (prefixWord ++ tailWord_5350856) baseStart_5350856 baseEnd_5350856 := by
    simpa [prefixWord, tailWord_5350856, baseEnd_5350856] using wordTrace_append hprefix tailTrace_5350856
  have hstable : (prefixWord ++ tailWord_5350856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350856).length < 2 ^ (prefixWord ++ tailWord_5350856).sum := by decide
  have hdescent : baseEnd_5350856 < baseStart_5350856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350889 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_5350889 : Nat := 118140960795 + 5350889 * 2 ^ 59
def prefixEnd_5350889 : Nat := 4983230072969 + 3 ^ 40 * 5350889 * 2
def baseEnd_5350889 : Nat := 2747577985856020355879215

theorem tailTrace_5350889 : CollatzResearch.WordTrace tailWord_5350889 prefixEnd_5350889 2747577985856020355879215 := by
  unfold tailWord_5350889
  simp only [CollatzResearch.WordTrace]
  refine ⟨195162955111650486930271721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130108636741100324620181147 195162955111650486930271721)
  ·
    refine ⟨146372216333737865197703791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195162955111650486930271721 146372216333737865197703791)
    ·
      refine ⟨219558324500606797796555687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146372216333737865197703791 219558324500606797796555687)
      ·
        refine ⟨329337486750910196694833531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219558324500606797796555687 329337486750910196694833531)
        ·
          refine ⟨494006230126365295042250297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329337486750910196694833531 494006230126365295042250297)
          ·
            refine ⟨370504672594773971281687723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494006230126365295042250297 370504672594773971281687723)
            ·
              refine ⟨555757008892160956922531585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370504672594773971281687723 555757008892160956922531585)
              ·
                refine ⟨416817756669120717691898689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555757008892160956922531585 416817756669120717691898689)
                ·
                  refine ⟨312613317501840538268924017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416817756669120717691898689 312613317501840538268924017)
                  ·
                    refine ⟨234459988126380403701693013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312613317501840538268924017 234459988126380403701693013)
                    ·
                      refine ⟨2747577985856020355879215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 234459988126380403701693013 2747577985856020355879215)
                      ·
                        rfl

theorem cell23_5350889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_5350889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350889 prefixEnd_5350889 := by exact prefixLift 5350889
  have htrace : WordTrace (prefixWord ++ tailWord_5350889) baseStart_5350889 baseEnd_5350889 := by
    simpa [prefixWord, tailWord_5350889, baseEnd_5350889] using wordTrace_append hprefix tailTrace_5350889
  have hstable : (prefixWord ++ tailWord_5350889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350889).length < 2 ^ (prefixWord ++ tailWord_5350889).sum := by decide
  have hdescent : baseEnd_5350889 < baseStart_5350889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350913 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_5350913 : Nat := 118140960795 + 5350913 * 2 ^ 59
def prefixEnd_5350913 : Nat := 4983230072969 + 3 ^ 40 * 5350913 * 2
def baseEnd_5350913 : Nat := 2747590309391728261979105

theorem tailTrace_5350913 : CollatzResearch.WordTrace tailWord_5350913 prefixEnd_5350913 2747590309391728261979105 := by
  unfold tailWord_5350913
  simp only [CollatzResearch.WordTrace]
  refine ⟨195163830463563539029145393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130109220309042359352763595 195163830463563539029145393)
  ·
    refine ⟨146372872847672654271859045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195163830463563539029145393 146372872847672654271859045)
    ·
      refine ⟨27444913658938622675973571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146372872847672654271859045 27444913658938622675973571)
      ·
        refine ⟨41167370488407934013960357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27444913658938622675973571 41167370488407934013960357)
        ·
          refine ⟨7718881966576487627617567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41167370488407934013960357 7718881966576487627617567)
          ·
            refine ⟨11578322949864731441426351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718881966576487627617567 11578322949864731441426351)
            ·
              refine ⟨17367484424797097162139527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11578322949864731441426351 17367484424797097162139527)
              ·
                refine ⟨26051226637195645743209291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17367484424797097162139527 26051226637195645743209291)
                ·
                  refine ⟨39076839955793468614813937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26051226637195645743209291 39076839955793468614813937)
                  ·
                    refine ⟨29307629966845101461110453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39076839955793468614813937 29307629966845101461110453)
                    ·
                      refine ⟨2747590309391728261979105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29307629966845101461110453 2747590309391728261979105)
                      ·
                        rfl

theorem cell23_5350913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_5350913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350913 prefixEnd_5350913 := by exact prefixLift 5350913
  have htrace : WordTrace (prefixWord ++ tailWord_5350913) baseStart_5350913 baseEnd_5350913 := by
    simpa [prefixWord, tailWord_5350913, baseEnd_5350913] using wordTrace_append hprefix tailTrace_5350913
  have hstable : (prefixWord ++ tailWord_5350913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350913).length < 2 ^ (prefixWord ++ tailWord_5350913).sum := by decide
  have hdescent : baseEnd_5350913 < baseStart_5350913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350918 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5350918 : Nat := 118140960795 + 5350918 * 2 ^ 59
def prefixEnd_5350918 : Nat := 4983230072969 + 3 ^ 40 * 5350918 * 2
def baseEnd_5350918 : Nat := 2747592876795000742416583

theorem tailTrace_5350918 : CollatzResearch.WordTrace tailWord_5350918 prefixEnd_5350918 2747592876795000742416583 := by
  unfold tailWord_5350918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098875400892044527596169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130109341885696949922051605 6098875400892044527596169)
  ·
    refine ⟨4574156550669033395697127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6098875400892044527596169 4574156550669033395697127)
    ·
      refine ⟨6861234826003550093545691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574156550669033395697127 6861234826003550093545691)
      ·
        refine ⟨10291852239005325140318537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6861234826003550093545691 10291852239005325140318537)
        ·
          refine ⟨7718889179253993855238903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10291852239005325140318537 7718889179253993855238903)
          ·
            refine ⟨11578333768880990782858355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718889179253993855238903 11578333768880990782858355)
            ·
              refine ⟨17367500653321486174287533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11578333768880990782858355 17367500653321486174287533)
              ·
                refine ⟨6512812744995557315357825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17367500653321486174287533 6512812744995557315357825)
                ·
                  refine ⟨4884609558746667986518369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6512812744995557315357825 4884609558746667986518369)
                  ·
                    refine ⟨3663457169060000989888777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4884609558746667986518369 3663457169060000989888777)
                    ·
                      refine ⟨2747592876795000742416583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663457169060000989888777 2747592876795000742416583)
                      ·
                        rfl

theorem cell23_5350918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5350918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350918 prefixEnd_5350918 := by exact prefixLift 5350918
  have htrace : WordTrace (prefixWord ++ tailWord_5350918) baseStart_5350918 baseEnd_5350918 := by
    simpa [prefixWord, tailWord_5350918, baseEnd_5350918] using wordTrace_append hprefix tailTrace_5350918
  have hstable : (prefixWord ++ tailWord_5350918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350918).length < 2 ^ (prefixWord ++ tailWord_5350918).sum := by decide
  have hdescent : baseEnd_5350918 < baseStart_5350918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350943 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_5350943 : Nat := 118140960795 + 5350943 * 2 ^ 59
def prefixEnd_5350943 : Nat := 4983230072969 + 3 ^ 40 * 5350943 * 2
def baseEnd_5350943 : Nat := 2747605713811363144603967

theorem tailTrace_5350943 : CollatzResearch.WordTrace tailWord_5350943 prefixEnd_5350943 2747605713811363144603967 := by
  unfold tailWord_5350943
  simp only [CollatzResearch.WordTrace]
  refine ⟨195164924653454854152737483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130109949768969902768491655 195164924653454854152737483)
  ·
    refine ⟨292747386980182281229106225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195164924653454854152737483 292747386980182281229106225)
    ·
      refine ⟨219560540235136710921829669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292747386980182281229106225 219560540235136710921829669)
      ·
        refine ⟨41167601294088133297843063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219560540235136710921829669 41167601294088133297843063)
        ·
          refine ⟨61751401941132199946764595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41167601294088133297843063 61751401941132199946764595)
          ·
            refine ⟨92627102911698299920146893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61751401941132199946764595 92627102911698299920146893)
            ·
              refine ⟨34735163591886862470055085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92627102911698299920146893 34735163591886862470055085)
              ·
                refine ⟨13025686346957573426270657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34735163591886862470055085 13025686346957573426270657)
                ·
                  refine ⟨9769264760218180069702993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13025686346957573426270657 9769264760218180069702993)
                  ·
                    refine ⟨7326948570163635052277245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9769264760218180069702993 7326948570163635052277245)
                    ·
                      refine ⟨2747605713811363144603967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326948570163635052277245 2747605713811363144603967)
                      ·
                        rfl

theorem cell23_5350943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_5350943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350943 prefixEnd_5350943 := by exact prefixLift 5350943
  have htrace : WordTrace (prefixWord ++ tailWord_5350943) baseStart_5350943 baseEnd_5350943 := by
    simpa [prefixWord, tailWord_5350943, baseEnd_5350943] using wordTrace_append hprefix tailTrace_5350943
  have hstable : (prefixWord ++ tailWord_5350943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350943).length < 2 ^ (prefixWord ++ tailWord_5350943).sum := by decide
  have hdescent : baseEnd_5350943 < baseStart_5350943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350946 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_5350946 : Nat := 118140960795 + 5350946 * 2 ^ 59
def prefixEnd_5350946 : Nat := 4983230072969 + 3 ^ 40 * 5350946 * 2
def baseEnd_5350946 : Nat := 305289694917036292540717

theorem tailTrace_5350946 : CollatzResearch.WordTrace tailWord_5350946 prefixEnd_5350946 305289694917036292540717 := by
  unfold tailWord_5350946
  simp only [CollatzResearch.WordTrace]
  refine ⟨48791258518110996416274173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130110022714962657110064461 48791258518110996416274173)
  ·
    refine ⟨18296721944291623656102815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48791258518110996416274173 18296721944291623656102815)
    ·
      refine ⟨27445082916437435484154223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18296721944291623656102815 27445082916437435484154223)
      ·
        refine ⟨41167624374656153226231335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27445082916437435484154223 41167624374656153226231335)
        ·
          refine ⟨61751436561984229839347003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41167624374656153226231335 61751436561984229839347003)
          ·
            refine ⟨92627154842976344759020505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61751436561984229839347003 92627154842976344759020505)
            ·
              refine ⟨69470366132232258569265379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92627154842976344759020505 69470366132232258569265379)
              ·
                refine ⟨104205549198348387853898069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69470366132232258569265379 104205549198348387853898069)
                ·
                  refine ⟨305289694917036292540717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 104205549198348387853898069 305289694917036292540717)
                  ·
                    rfl

theorem cell23_5350946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_5350946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350946 prefixEnd_5350946 := by exact prefixLift 5350946
  have htrace : WordTrace (prefixWord ++ tailWord_5350946) baseStart_5350946 baseEnd_5350946 := by
    simpa [prefixWord, tailWord_5350946, baseEnd_5350946] using wordTrace_append hprefix tailTrace_5350946
  have hstable : (prefixWord ++ tailWord_5350946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350946).length < 2 ^ (prefixWord ++ tailWord_5350946).sum := by decide
  have hdescent : baseEnd_5350946 < baseStart_5350946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350963 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 6]
def baseStart_5350963 : Nat := 118140960795 + 5350963 * 2 ^ 59
def prefixEnd_5350963 : Nat := 4983230072969 + 3 ^ 40 * 5350963 * 2
def baseEnd_5350963 : Nat := 305290664824939229594875

theorem tailTrace_5350963 : CollatzResearch.WordTrace tailWord_5350963 prefixEnd_5350963 305290664824939229594875 := by
  unfold tailWord_5350963
  simp only [CollatzResearch.WordTrace]
  refine ⟨195165654113382397568465543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130110436075588265045643695 195165654113382397568465543)
  ·
    refine ⟨292748481170073596352698315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195165654113382397568465543 292748481170073596352698315)
    ·
      refine ⟨439122721755110394529047473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292748481170073596352698315 439122721755110394529047473)
      ·
        refine ⟨329342041316332795896785605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439122721755110394529047473 329342041316332795896785605)
        ·
          refine ⟨61751632746812399230647301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329342041316332795896785605 61751632746812399230647301)
          ·
            refine ⟨11578431140027324855746369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61751632746812399230647301 11578431140027324855746369)
            ·
              refine ⟨8683823355020493641809777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11578431140027324855746369 8683823355020493641809777)
              ·
                refine ⟨6512867516265370231357333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8683823355020493641809777 6512867516265370231357333)
                ·
                  refine ⟨305290664824939229594875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6512867516265370231357333 305290664824939229594875)
                  ·
                    rfl

theorem cell23_5350963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 6].length) (baseStart_5350963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350963 prefixEnd_5350963 := by exact prefixLift 5350963
  have htrace : WordTrace (prefixWord ++ tailWord_5350963) baseStart_5350963 baseEnd_5350963 := by
    simpa [prefixWord, tailWord_5350963, baseEnd_5350963] using wordTrace_append hprefix tailTrace_5350963
  have hstable : (prefixWord ++ tailWord_5350963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350963).length < 2 ^ (prefixWord ++ tailWord_5350963).sum := by decide
  have hdescent : baseEnd_5350963 < baseStart_5350963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350967 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 1, 4]
def baseStart_5350967 : Nat := 118140960795 + 5350967 * 2 ^ 59
def prefixEnd_5350967 : Nat := 4983230072969 + 3 ^ 40 * 5350967 * 2
def baseEnd_5350967 : Nat := 915872679115690350234619

theorem tailTrace_5350967 : CollatzResearch.WordTrace tailWord_5350967 prefixEnd_5350967 915872679115690350234619 := by
  unfold tailWord_5350967
  simp only [CollatzResearch.WordTrace]
  refine ⟨195165800005367906251611155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130110533336911937501074103 195165800005367906251611155)
  ·
    refine ⟨292748700008051859377416733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195165800005367906251611155 292748700008051859377416733)
    ·
      refine ⟨109780762503019447266531275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292748700008051859377416733 109780762503019447266531275)
      ·
        refine ⟨164671143754529170899796913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109780762503019447266531275 164671143754529170899796913)
        ·
          refine ⟨123503357815896878174847685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164671143754529170899796913 123503357815896878174847685)
          ·
            refine ⟨23156879590480664657783941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123503357815896878174847685 23156879590480664657783941)
            ·
              refine ⟨4341914923215124623334489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23156879590480664657783941 4341914923215124623334489)
              ·
                refine ⟨3256436192411343467500867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341914923215124623334489 3256436192411343467500867)
                ·
                  refine ⟨4884654288617015201251301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256436192411343467500867 4884654288617015201251301)
                  ·
                    refine ⟨915872679115690350234619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4884654288617015201251301 915872679115690350234619)
                    ·
                      rfl

theorem cell23_5350967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_5350967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350967 prefixEnd_5350967 := by exact prefixLift 5350967
  have htrace : WordTrace (prefixWord ++ tailWord_5350967) baseStart_5350967 baseEnd_5350967 := by
    simpa [prefixWord, tailWord_5350967, baseEnd_5350967] using wordTrace_append hprefix tailTrace_5350967
  have hstable : (prefixWord ++ tailWord_5350967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350967).length < 2 ^ (prefixWord ++ tailWord_5350967).sum := by decide
  have hdescent : baseEnd_5350967 < baseStart_5350967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350986 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_5350986 : Nat := 118140960795 + 5350986 * 2 ^ 59
def prefixEnd_5350986 : Nat := 4983230072969 + 3 ^ 40 * 5350986 * 2
def baseEnd_5350986 : Nat := 2747627793479506476366269

theorem tailTrace_5350986 : CollatzResearch.WordTrace tailWord_5350986 prefixEnd_5350986 2747627793479506476366269 := by
  unfold tailWord_5350986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48791623248074768124138203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130110995328199381664368541 48791623248074768124138203)
  ·
    refine ⟨73187434872112152186207305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48791623248074768124138203 73187434872112152186207305)
    ·
      refine ⟨54890576154084114139655479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73187434872112152186207305 54890576154084114139655479)
      ·
        refine ⟨82335864231126171209483219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54890576154084114139655479 82335864231126171209483219)
        ·
          refine ⟨123503796346689256814224829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82335864231126171209483219 123503796346689256814224829)
          ·
            refine ⟨46313923630008471305334311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123503796346689256814224829 46313923630008471305334311)
            ·
              refine ⟨69470885445012706958001467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46313923630008471305334311 69470885445012706958001467)
              ·
                refine ⟨104206328167519060437002201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69470885445012706958001467 104206328167519060437002201)
                ·
                  refine ⟨78154746125639295327751651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104206328167519060437002201 78154746125639295327751651)
                  ·
                    refine ⟨117232119188458942991627477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78154746125639295327751651 117232119188458942991627477)
                    ·
                      refine ⟨2747627793479506476366269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117232119188458942991627477 2747627793479506476366269)
                      ·
                        rfl

theorem cell23_5350986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_5350986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350986 prefixEnd_5350986 := by exact prefixLift 5350986
  have htrace : WordTrace (prefixWord ++ tailWord_5350986) baseStart_5350986 baseEnd_5350986 := by
    simpa [prefixWord, tailWord_5350986, baseEnd_5350986] using wordTrace_append hprefix tailTrace_5350986
  have hstable : (prefixWord ++ tailWord_5350986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350986).length < 2 ^ (prefixWord ++ tailWord_5350986).sum := by decide
  have hdescent : baseEnd_5350986 < baseStart_5350986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350993 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_5350993 : Nat := 118140960795 + 5350993 * 2 ^ 59
def prefixEnd_5350993 : Nat := 4983230072969 + 3 ^ 40 * 5350993 * 2
def baseEnd_5350993 : Nat := 915877129281362649659579

theorem tailTrace_5350993 : CollatzResearch.WordTrace tailWord_5350993 prefixEnd_5350993 915877129281362649659579 := by
  unfold tailWord_5350993
  simp only [CollatzResearch.WordTrace]
  refine ⟨195166748303273712692057633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130111165535515808461371755 195166748303273712692057633)
  ·
    refine ⟨146375061227455284519043225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195166748303273712692057633 146375061227455284519043225)
    ·
      refine ⟨109781295920591463389282419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146375061227455284519043225 109781295920591463389282419)
      ·
        refine ⟨164671943880887195083923629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109781295920591463389282419 164671943880887195083923629)
        ·
          refine ⟨61751978955332698156471361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164671943880887195083923629 61751978955332698156471361)
          ·
            refine ⟨46313984216499523617353521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61751978955332698156471361 46313984216499523617353521)
            ·
              refine ⟨34735488162374642713015141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46313984216499523617353521 34735488162374642713015141)
              ·
                refine ⟨6512904030445245508690339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34735488162374642713015141 6512904030445245508690339)
                ·
                  refine ⟨9769356045667868263035509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512904030445245508690339 9769356045667868263035509)
                  ·
                    refine ⟨915877129281362649659579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9769356045667868263035509 915877129281362649659579)
                    ·
                      rfl

theorem cell23_5350993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_5350993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350993 prefixEnd_5350993 := by exact prefixLift 5350993
  have htrace : WordTrace (prefixWord ++ tailWord_5350993) baseStart_5350993 baseEnd_5350993 := by
    simpa [prefixWord, tailWord_5350993, baseEnd_5350993] using wordTrace_append hprefix tailTrace_5350993
  have hstable : (prefixWord ++ tailWord_5350993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350993).length < 2 ^ (prefixWord ++ tailWord_5350993).sum := by decide
  have hdescent : baseEnd_5350993 < baseStart_5350993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351033 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_5351033 : Nat := 118140960795 + 5351033 * 2 ^ 59
def prefixEnd_5351033 : Nat := 4983230072969 + 3 ^ 40 * 5351033 * 2
def baseEnd_5351033 : Nat := 2747651927070267792478553

theorem tailTrace_5351033 : CollatzResearch.WordTrace tailWord_5351033 prefixEnd_5351033 2747651927070267792478553 := by
  unfold tailWord_5351033
  simp only [CollatzResearch.WordTrace]
  refine ⟨195168207223128799523513753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130112138148752533015675835 195168207223128799523513753)
  ·
    refine ⟨146376155417346599642635315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195168207223128799523513753 146376155417346599642635315)
    ·
      refine ⟨219564233126019899463952973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146376155417346599642635315 219564233126019899463952973)
      ·
        refine ⟨82336587422257462298982365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219564233126019899463952973 82336587422257462298982365)
        ·
          refine ⟨30876220283346548362118387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82336587422257462298982365 30876220283346548362118387)
          ·
            refine ⟨46314330425019822543177581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30876220283346548362118387 46314330425019822543177581)
            ·
              refine ⟨17367873909382433453691593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46314330425019822543177581 17367873909382433453691593)
              ·
                refine ⟨13025905432036825090268695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17367873909382433453691593 13025905432036825090268695)
                ·
                  refine ⟨19538858148055237635403043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13025905432036825090268695 19538858148055237635403043)
                  ·
                    refine ⟨29308287222082856453104565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19538858148055237635403043 29308287222082856453104565)
                    ·
                      refine ⟨2747651927070267792478553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29308287222082856453104565 2747651927070267792478553)
                      ·
                        rfl

theorem cell23_5351033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_5351033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351033 prefixEnd_5351033 := by exact prefixLift 5351033
  have htrace : WordTrace (prefixWord ++ tailWord_5351033) baseStart_5351033 baseEnd_5351033 := by
    simpa [prefixWord, tailWord_5351033, baseEnd_5351033] using wordTrace_append hprefix tailTrace_5351033
  have hstable : (prefixWord ++ tailWord_5351033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351033).length < 2 ^ (prefixWord ++ tailWord_5351033).sum := by decide
  have hdescent : baseEnd_5351033 < baseStart_5351033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351036 : List Nat := [2, 2, 2, 1, 1, 2, 1, 12]
def baseStart_5351036 : Nat := 118140960795 + 5351036 * 2 ^ 59
def prefixEnd_5351036 : Nat := 4983230072969 + 3 ^ 40 * 5351036 * 2
def baseEnd_5351036 : Nat := 101764943241193751138557

theorem tailTrace_5351036 : CollatzResearch.WordTrace tailWord_5351036 prefixEnd_5351036 101764943241193751138557 := by
  unfold tailWord_5351036
  simp only [CollatzResearch.WordTrace]
  refine ⟨97584158321058965517936481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130112211094745287357248641 97584158321058965517936481)
  ·
    refine ⟨73188118740794224138452361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97584158321058965517936481 73188118740794224138452361)
    ·
      refine ⟨54891089055595668103839271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73188118740794224138452361 54891089055595668103839271)
      ·
        refine ⟨82336633583393502155758907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54891089055595668103839271 82336633583393502155758907)
        ·
          refine ⟨123504950375090253233638361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82336633583393502155758907 123504950375090253233638361)
          ·
            refine ⟨92628712781317689925228771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123504950375090253233638361 92628712781317689925228771)
            ·
              refine ⟨138943069171976534887843157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92628712781317689925228771 138943069171976534887843157)
              ·
                refine ⟨101764943241193751138557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 138943069171976534887843157 101764943241193751138557)
                ·
                  rfl

theorem cell23_5351036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 12].length) (baseStart_5351036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351036 prefixEnd_5351036 := by exact prefixLift 5351036
  have htrace : WordTrace (prefixWord ++ tailWord_5351036) baseStart_5351036 baseEnd_5351036 := by
    simpa [prefixWord, tailWord_5351036, baseEnd_5351036] using wordTrace_append hprefix tailTrace_5351036
  have hstable : (prefixWord ++ tailWord_5351036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351036).length < 2 ^ (prefixWord ++ tailWord_5351036).sum := by decide
  have hdescent : baseEnd_5351036 < baseStart_5351036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351047 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_5351047 : Nat := 118140960795 + 5351047 * 2 ^ 59
def prefixEnd_5351047 : Nat := 4983230072969 + 3 ^ 40 * 5351047 * 2
def baseEnd_5351047 : Nat := 2747659115799430737703489

theorem tailTrace_5351047 : CollatzResearch.WordTrace tailWord_5351047 prefixEnd_5351047 2747659115799430737703489 := by
  unfold tailWord_5351047
  simp only [CollatzResearch.WordTrace]
  refine ⟨195168717845078079914523395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130112478563385386609682263 195168717845078079914523395)
  ·
    refine ⟨292753076767617119871785093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195168717845078079914523395 292753076767617119871785093)
    ·
      refine ⟨54891201893928209975959705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292753076767617119871785093 54891201893928209975959705)
      ·
        refine ⟨41168401420446157481969779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54891201893928209975959705 41168401420446157481969779)
        ·
          refine ⟨61752602130669236222954669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41168401420446157481969779 61752602130669236222954669)
          ·
            refine ⟨23157225799000963583608001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61752602130669236222954669 23157225799000963583608001)
            ·
              refine ⟨17367919349250722687706001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23157225799000963583608001 17367919349250722687706001)
              ·
                refine ⟨13025939511938042015779501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17367919349250722687706001 13025939511938042015779501)
                ·
                  refine ⟨4884727316976765755917313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13025939511938042015779501 4884727316976765755917313)
                  ·
                    refine ⟨3663545487732574316937985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4884727316976765755917313 3663545487732574316937985)
                    ·
                      refine ⟨2747659115799430737703489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663545487732574316937985 2747659115799430737703489)
                      ·
                        rfl

theorem cell23_5351047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_5351047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351047 prefixEnd_5351047 := by exact prefixLift 5351047
  have htrace : WordTrace (prefixWord ++ tailWord_5351047) baseStart_5351047 baseEnd_5351047 := by
    simpa [prefixWord, tailWord_5351047, baseEnd_5351047] using wordTrace_append hprefix tailTrace_5351047
  have hstable : (prefixWord ++ tailWord_5351047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351047).length < 2 ^ (prefixWord ++ tailWord_5351047).sum := by decide
  have hdescent : baseEnd_5351047 < baseStart_5351047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351056 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_5351056 : Nat := 118140960795 + 5351056 * 2 ^ 59
def prefixEnd_5351056 : Nat := 4983230072969 + 3 ^ 40 * 5351056 * 2
def baseEnd_5351056 : Nat := 2747663737125321202490947

theorem tailTrace_5351056 : CollatzResearch.WordTrace tailWord_5351056 prefixEnd_5351056 2747663737125321202490947 := by
  unfold tailWord_5351056
  simp only [CollatzResearch.WordTrace]
  refine ⟨97584523051022737225800511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130112697401363649634400681 97584523051022737225800511)
  ·
    refine ⟨146376784576534105838700767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97584523051022737225800511 146376784576534105838700767)
    ·
      refine ⟨219565176864801158758051151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146376784576534105838700767 219565176864801158758051151)
      ·
        refine ⟨329347765297201738137076727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219565176864801158758051151 329347765297201738137076727)
        ·
          refine ⟨494021647945802607205615091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329347765297201738137076727 494021647945802607205615091)
          ·
            refine ⟨741032471918703910808422637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494021647945802607205615091 741032471918703910808422637)
            ·
              refine ⟨277887176969513966553158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 741032471918703910808422637 277887176969513966553158489)
              ·
                refine ⟨208415382727135474914868867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277887176969513966553158489 208415382727135474914868867)
                ·
                  refine ⟨312623074090703212372303301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208415382727135474914868867 312623074090703212372303301)
                  ·
                    refine ⟨58616826392006852319806869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312623074090703212372303301 58616826392006852319806869)
                    ·
                      refine ⟨2747663737125321202490947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58616826392006852319806869 2747663737125321202490947)
                      ·
                        rfl

theorem cell23_5351056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_5351056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351056 prefixEnd_5351056 := by exact prefixLift 5351056
  have htrace : WordTrace (prefixWord ++ tailWord_5351056) baseStart_5351056 baseEnd_5351056 := by
    simpa [prefixWord, tailWord_5351056, baseEnd_5351056] using wordTrace_append hprefix tailTrace_5351056
  have hstable : (prefixWord ++ tailWord_5351056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351056).length < 2 ^ (prefixWord ++ tailWord_5351056).sum := by decide
  have hdescent : baseEnd_5351056 < baseStart_5351056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351058 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_5351058 : Nat := 118140960795 + 5351058 * 2 ^ 59
def prefixEnd_5351058 : Nat := 4983230072969 + 3 ^ 40 * 5351058 * 2
def baseEnd_5351058 : Nat := 2747664764086630194665939

theorem tailTrace_5351058 : CollatzResearch.WordTrace tailWord_5351058 prefixEnd_5351058 2747664764086630194665939 := by
  unfold tailWord_5351058
  simp only [CollatzResearch.WordTrace]
  refine ⟨48792279762009557198293457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130112746032025485862115885 48792279762009557198293457)
  ·
    refine ⟨36594209821507167898720093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48792279762009557198293457 36594209821507167898720093)
    ·
      refine ⟨13722828683065187962020035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36594209821507167898720093 13722828683065187962020035)
      ·
        refine ⟨20584243024597781943030053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13722828683065187962020035 20584243024597781943030053)
        ·
          refine ⟨3859545567112084114318135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20584243024597781943030053 3859545567112084114318135)
          ·
            refine ⟨5789318350668126171477203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859545567112084114318135 5789318350668126171477203)
            ·
              refine ⟨8683977526002189257215805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789318350668126171477203 8683977526002189257215805)
              ·
                refine ⟨3256491572250820971455927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8683977526002189257215805 3256491572250820971455927)
                ·
                  refine ⟨4884737358376231457183891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256491572250820971455927 4884737358376231457183891)
                  ·
                    refine ⟨7327106037564347185775837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4884737358376231457183891 7327106037564347185775837)
                    ·
                      refine ⟨2747664764086630194665939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7327106037564347185775837 2747664764086630194665939)
                      ·
                        rfl

theorem cell23_5351058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_5351058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351058 prefixEnd_5351058 := by exact prefixLift 5351058
  have htrace : WordTrace (prefixWord ++ tailWord_5351058) baseStart_5351058 baseEnd_5351058 := by
    simpa [prefixWord, tailWord_5351058, baseEnd_5351058] using wordTrace_append hprefix tailTrace_5351058
  have hstable : (prefixWord ++ tailWord_5351058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351058).length < 2 ^ (prefixWord ++ tailWord_5351058).sum := by decide
  have hdescent : baseEnd_5351058 < baseStart_5351058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351070 : List Nat := [4, 3, 1, 1, 1, 4, 9]
def baseStart_5351070 : Nat := 118140960795 + 5351070 * 2 ^ 59
def prefixEnd_5351070 : Nat := 4983230072969 + 3 ^ 40 * 5351070 * 2
def baseEnd_5351070 : Nat := 33921863282154125280443

theorem tailTrace_5351070 : CollatzResearch.WordTrace tailWord_5351070 prefixEnd_5351070 33921863282154125280443 := by
  unfold tailWord_5351070
  simp only [CollatzResearch.WordTrace]
  refine ⟨24396194590499344355326333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130113037815996503228407109 24396194590499344355326333)
  ·
    refine ⟨9148572971437254133247375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24396194590499344355326333 9148572971437254133247375)
    ·
      refine ⟨13722859457155881199871063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9148572971437254133247375 13722859457155881199871063)
      ·
        refine ⟨20584289185733821799806595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13722859457155881199871063 20584289185733821799806595)
        ·
          refine ⟨30876433778600732699709893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20584289185733821799806595 30876433778600732699709893)
          ·
            refine ⟨5789331333487637381195605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30876433778600732699709893 5789331333487637381195605)
            ·
              refine ⟨33921863282154125280443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5789331333487637381195605 33921863282154125280443)
              ·
                rfl

theorem cell23_5351070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 9].length) (baseStart_5351070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351070 prefixEnd_5351070 := by exact prefixLift 5351070
  have htrace : WordTrace (prefixWord ++ tailWord_5351070) baseStart_5351070 baseEnd_5351070 := by
    simpa [prefixWord, tailWord_5351070, baseEnd_5351070] using wordTrace_append hprefix tailTrace_5351070
  have hstable : (prefixWord ++ tailWord_5351070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351070).length < 2 ^ (prefixWord ++ tailWord_5351070).sum := by decide
  have hdescent : baseEnd_5351070 < baseStart_5351070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351132 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5351132 : Nat := 118140960795 + 5351132 * 2 ^ 59
def prefixEnd_5351132 : Nat := 4983230072969 + 3 ^ 40 * 5351132 * 2
def baseEnd_5351132 : Nat := 2747702761655062905140599

theorem tailTrace_5351132 : CollatzResearch.WordTrace tailWord_5351132 prefixEnd_5351132 2747702761655062905140599 := by
  unfold tailWord_5351132
  simp only [CollatzResearch.WordTrace]
  refine ⟨97585909024885069715683825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130114545366513426287578433 97585909024885069715683825)
  ·
    refine ⟨73189431768663802286762869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97585909024885069715683825 73189431768663802286762869)
    ·
      refine ⟨6861509228312231464384019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73189431768663802286762869 6861509228312231464384019)
      ·
        refine ⟨10292263842468347196576029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6861509228312231464384019 10292263842468347196576029)
        ·
          refine ⟨3859598940925630198716011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10292263842468347196576029 3859598940925630198716011)
          ·
            refine ⟨5789398411388445298074017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859598940925630198716011 5789398411388445298074017)
            ·
              refine ⟨4342048808541333973555513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5789398411388445298074017 4342048808541333973555513)
              ·
                refine ⟨3256536606406000480166635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342048808541333973555513 3256536606406000480166635)
                ·
                  refine ⟨4884804909609000720249953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256536606406000480166635 4884804909609000720249953)
                  ·
                    refine ⟨3663603682206750540187465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4884804909609000720249953 3663603682206750540187465)
                    ·
                      refine ⟨2747702761655062905140599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663603682206750540187465 2747702761655062905140599)
                      ·
                        rfl

theorem cell23_5351132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5351132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351132 prefixEnd_5351132 := by exact prefixLift 5351132
  have htrace : WordTrace (prefixWord ++ tailWord_5351132) baseStart_5351132 baseEnd_5351132 := by
    simpa [prefixWord, tailWord_5351132, baseEnd_5351132] using wordTrace_append hprefix tailTrace_5351132
  have hstable : (prefixWord ++ tailWord_5351132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351132).length < 2 ^ (prefixWord ++ tailWord_5351132).sum := by decide
  have hdescent : baseEnd_5351132 < baseStart_5351132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351150 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_5351150 : Nat := 118140960795 + 5351150 * 2 ^ 59
def prefixEnd_5351150 : Nat := 4983230072969 + 3 ^ 40 * 5351150 * 2
def baseEnd_5351150 : Nat := 2747712004306843834715515

theorem tailTrace_5351150 : CollatzResearch.WordTrace tailWord_5351150 prefixEnd_5351150 2747712004306843834715515 := by
  unfold tailWord_5351150
  simp only [CollatzResearch.WordTrace]
  refine ⟨24396559320463116063190363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130114983042469952337015269 24396559320463116063190363)
  ·
    refine ⟨36594838980694674094785545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24396559320463116063190363 36594838980694674094785545)
    ·
      refine ⟨27446129235521005571089159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36594838980694674094785545 27446129235521005571089159)
      ·
        refine ⟨41169193853281508356633739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27446129235521005571089159 41169193853281508356633739)
        ·
          refine ⟨61753790779922262534950609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41169193853281508356633739 61753790779922262534950609)
          ·
            refine ⟨46315343084941696901212957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61753790779922262534950609 46315343084941696901212957)
            ·
              refine ⟨17368253656853136337954859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46315343084941696901212957 17368253656853136337954859)
              ·
                refine ⟨26052380485279704506932289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17368253656853136337954859 26052380485279704506932289)
                ·
                  refine ⟨19539285363959778380199217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26052380485279704506932289 19539285363959778380199217)
                  ·
                    refine ⟨14654464022969833785149413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19539285363959778380199217 14654464022969833785149413)
                    ·
                      refine ⟨2747712004306843834715515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14654464022969833785149413 2747712004306843834715515)
                      ·
                        rfl

theorem cell23_5351150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_5351150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351150 prefixEnd_5351150 := by exact prefixLift 5351150
  have htrace : WordTrace (prefixWord ++ tailWord_5351150) baseStart_5351150 baseEnd_5351150 := by
    simpa [prefixWord, tailWord_5351150, baseEnd_5351150] using wordTrace_append hprefix tailTrace_5351150
  have hstable : (prefixWord ++ tailWord_5351150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351150).length < 2 ^ (prefixWord ++ tailWord_5351150).sum := by decide
  have hdescent : baseEnd_5351150 < baseStart_5351150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351154 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5351154 : Nat := 118140960795 + 5351154 * 2 ^ 59
def prefixEnd_5351154 : Nat := 4983230072969 + 3 ^ 40 * 5351154 * 2
def baseEnd_5351154 : Nat := 2747714058229461819065497

theorem tailTrace_5351154 : CollatzResearch.WordTrace tailWord_5351154 prefixEnd_5351154 2747714058229461819065497 := by
  unfold tailWord_5351154
  simp only [CollatzResearch.WordTrace]
  refine ⟨48793155113922609297167129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130115080303793624792445677 48793155113922609297167129)
  ·
    refine ⟨36594866335441956972875347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48793155113922609297167129 36594866335441956972875347)
    ·
      refine ⟨54892299503162935459313021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36594866335441956972875347 54892299503162935459313021)
      ·
        refine ⟨20584612313686100797242383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54892299503162935459313021 20584612313686100797242383)
        ·
          refine ⟨30876918470529151195863575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20584612313686100797242383 30876918470529151195863575)
          ·
            refine ⟨46315377705793726793795363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30876918470529151195863575 46315377705793726793795363)
            ·
              refine ⟨69473066558690590190693045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46315377705793726793795363 69473066558690590190693045)
              ·
                refine ⟨6513099989877242830377473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69473066558690590190693045 6513099989877242830377473)
                ·
                  refine ⟨4884824992407932122783105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6513099989877242830377473 4884824992407932122783105)
                  ·
                    refine ⟨3663618744305949092087329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4884824992407932122783105 3663618744305949092087329)
                    ·
                      refine ⟨2747714058229461819065497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663618744305949092087329 2747714058229461819065497)
                      ·
                        rfl

theorem cell23_5351154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5351154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351154 prefixEnd_5351154 := by exact prefixLift 5351154
  have htrace : WordTrace (prefixWord ++ tailWord_5351154) baseStart_5351154 baseEnd_5351154 := by
    simpa [prefixWord, tailWord_5351154, baseEnd_5351154] using wordTrace_append hprefix tailTrace_5351154
  have hstable : (prefixWord ++ tailWord_5351154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351154).length < 2 ^ (prefixWord ++ tailWord_5351154).sum := by decide
  have hdescent : baseEnd_5351154 < baseStart_5351154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351183 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_5351183 : Nat := 118140960795 + 5351183 * 2 ^ 59
def prefixEnd_5351183 : Nat := 4983230072969 + 3 ^ 40 * 5351183 * 2
def baseEnd_5351183 : Nat := 2747728949168442205602863

theorem tailTrace_5351183 : CollatzResearch.WordTrace tailWord_5351183 prefixEnd_5351183 2747728949168442205602863 := by
  unfold tailWord_5351183
  simp only [CollatzResearch.WordTrace]
  refine ⟨195173678172585375141474203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130115785448390250094316135 195173678172585375141474203)
  ·
    refine ⟨292760517258878062712211305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195173678172585375141474203 292760517258878062712211305)
    ·
      refine ⟨219570387944158547034158479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292760517258878062712211305 219570387944158547034158479)
      ·
        refine ⟨329355581916237820551237719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219570387944158547034158479 329355581916237820551237719)
        ·
          refine ⟨494033372874356730826856579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329355581916237820551237719 494033372874356730826856579)
          ·
            refine ⟨741050059311535096240284869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494033372874356730826856579 741050059311535096240284869)
            ·
              refine ⟨138946886120912830545053413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 741050059311535096240284869 138946886120912830545053413)
              ·
                refine ⟨26052541147671155727197515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138946886120912830545053413 26052541147671155727197515)
                ·
                  refine ⟨39078811721506733590796273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26052541147671155727197515 39078811721506733590796273)
                  ·
                    refine ⟨29309108791130050193097205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39078811721506733590796273 29309108791130050193097205)
                    ·
                      refine ⟨2747728949168442205602863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29309108791130050193097205 2747728949168442205602863)
                      ·
                        rfl

theorem cell23_5351183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_5351183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351183 prefixEnd_5351183 := by exact prefixLift 5351183
  have htrace : WordTrace (prefixWord ++ tailWord_5351183) baseStart_5351183 baseEnd_5351183 := by
    simpa [prefixWord, tailWord_5351183, baseEnd_5351183] using wordTrace_append hprefix tailTrace_5351183
  have hstable : (prefixWord ++ tailWord_5351183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351183).length < 2 ^ (prefixWord ++ tailWord_5351183).sum := by decide
  have hdescent : baseEnd_5351183 < baseStart_5351183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351223 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_5351223 : Nat := 118140960795 + 5351223 * 2 ^ 59
def prefixEnd_5351223 : Nat := 4983230072969 + 3 ^ 40 * 5351223 * 2
def baseEnd_5351223 : Nat := 2747749488394622049102679

theorem tailTrace_5351223 : CollatzResearch.WordTrace tailWord_5351223 prefixEnd_5351223 2747749488394622049102679 := by
  unfold tailWord_5351223
  simp only [CollatzResearch.WordTrace]
  refine ⟨195175137092440461972930323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130116758061626974648620215 195175137092440461972930323)
  ·
    refine ⟨292762705638660692959395485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195175137092440461972930323 292762705638660692959395485)
    ·
      refine ⟨109786014614497759859773307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292762705638660692959395485 109786014614497759859773307)
      ·
        refine ⟨164679021921746639789659961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109786014614497759859773307 164679021921746639789659961)
        ·
          refine ⟨123509266441309979842244971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164679021921746639789659961 123509266441309979842244971)
          ·
            refine ⟨185263899661964969763367457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123509266441309979842244971 185263899661964969763367457)
            ·
              refine ⟨138947924746473727322525593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185263899661964969763367457 138947924746473727322525593)
              ·
                refine ⟨104210943559855295491894195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138947924746473727322525593 104210943559855295491894195)
                ·
                  refine ⟨156316415339782943237841293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104210943559855295491894195 156316415339782943237841293)
                  ·
                    refine ⟨58618655752418603714190485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156316415339782943237841293 58618655752418603714190485)
                    ·
                      refine ⟨2747749488394622049102679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58618655752418603714190485 2747749488394622049102679)
                      ·
                        rfl

theorem cell23_5351223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_5351223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351223 prefixEnd_5351223 := by exact prefixLift 5351223
  have htrace : WordTrace (prefixWord ++ tailWord_5351223) baseStart_5351223 baseEnd_5351223 := by
    simpa [prefixWord, tailWord_5351223, baseEnd_5351223] using wordTrace_append hprefix tailTrace_5351223
  have hstable : (prefixWord ++ tailWord_5351223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351223).length < 2 ^ (prefixWord ++ tailWord_5351223).sum := by decide
  have hdescent : baseEnd_5351223 < baseStart_5351223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351250 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_5351250 : Nat := 118140960795 + 5351250 * 2 ^ 59
def prefixEnd_5351250 : Nat := 4983230072969 + 3 ^ 40 * 5351250 * 2
def baseEnd_5351250 : Nat := 305307039152477049273895

theorem tailTrace_5351250 : CollatzResearch.WordTrace tailWord_5351250 prefixEnd_5351250 305307039152477049273895 := by
  unfold tailWord_5351250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48794030465835661396040801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130117414575561763722775469 48794030465835661396040801)
  ·
    refine ⟨36595522849376746047030601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48794030465835661396040801 36595522849376746047030601)
    ·
      refine ⟨27446642137032559535272951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36595522849376746047030601 27446642137032559535272951)
      ·
        refine ⟨41169963205548839302909427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27446642137032559535272951 41169963205548839302909427)
        ·
          refine ⟨61754944808323258954364141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41169963205548839302909427 61754944808323258954364141)
          ·
            refine ⟨23158104303121222107886553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61754944808323258954364141 23158104303121222107886553)
            ·
              refine ⟨17368578227340916580914915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23158104303121222107886553 17368578227340916580914915)
              ·
                refine ⟨26052867341011374871372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17368578227340916580914915 26052867341011374871372373)
                ·
                  refine ⟨305307039152477049273895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26052867341011374871372373 305307039152477049273895)
                  ·
                    rfl

theorem cell23_5351250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_5351250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351250 prefixEnd_5351250 := by exact prefixLift 5351250
  have htrace : WordTrace (prefixWord ++ tailWord_5351250) baseStart_5351250 baseEnd_5351250 := by
    simpa [prefixWord, tailWord_5351250, baseEnd_5351250] using wordTrace_append hprefix tailTrace_5351250
  have hstable : (prefixWord ++ tailWord_5351250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351250).length < 2 ^ (prefixWord ++ tailWord_5351250).sum := by decide
  have hdescent : baseEnd_5351250 < baseStart_5351250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351267 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 6]
def baseStart_5351267 : Nat := 118140960795 + 5351267 * 2 ^ 59
def prefixEnd_5351267 : Nat := 4983230072969 + 3 ^ 40 * 5351267 * 2
def baseEnd_5351267 : Nat := 305308009060379986328053

theorem tailTrace_5351267 : CollatzResearch.WordTrace tailWord_5351267 prefixEnd_5351267 305308009060379986328053 := by
  unfold tailWord_5351267
  simp only [CollatzResearch.WordTrace]
  refine ⟨195176741904281057487532055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130117827936187371658354703 195176741904281057487532055)
  ·
    refine ⟨292765112856421586231298083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195176741904281057487532055 292765112856421586231298083)
    ·
      refine ⟨439147669284632379346947125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292765112856421586231298083 439147669284632379346947125)
      ·
        refine ⟨41170093995434285563776293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 439147669284632379346947125 41170093995434285563776293)
        ·
          refine ⟨7719392624143928543208055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41170093995434285563776293 7719392624143928543208055)
          ·
            refine ⟨11579088936215892814812083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719392624143928543208055 11579088936215892814812083)
            ·
              refine ⟨17368633404323839222218125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11579088936215892814812083 17368633404323839222218125)
              ·
                refine ⟨6513237526621439708331797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17368633404323839222218125 6513237526621439708331797)
                ·
                  refine ⟨305308009060379986328053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6513237526621439708331797 305308009060379986328053)
                  ·
                    rfl

theorem cell23_5351267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 6].length) (baseStart_5351267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351267 prefixEnd_5351267 := by exact prefixLift 5351267
  have htrace : WordTrace (prefixWord ++ tailWord_5351267) baseStart_5351267 baseEnd_5351267 := by
    simpa [prefixWord, tailWord_5351267, baseEnd_5351267] using wordTrace_append hprefix tailTrace_5351267
  have hstable : (prefixWord ++ tailWord_5351267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351267).length < 2 ^ (prefixWord ++ tailWord_5351267).sum := by decide
  have hdescent : baseEnd_5351267 < baseStart_5351267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351368 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_5351368 : Nat := 118140960795 + 5351368 * 2 ^ 59
def prefixEnd_5351368 : Nat := 4983230072969 + 3 ^ 40 * 5351368 * 2
def baseEnd_5351368 : Nat := 2747823943089523981789513

theorem tailTrace_5351368 : CollatzResearch.WordTrace tailWord_5351368 prefixEnd_5351368 2747823943089523981789513 := by
  unfold tailWord_5351368
  simp only [CollatzResearch.WordTrace]
  refine ⟨97590212838457575868479379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130120283784610101157972505 97590212838457575868479379)
  ·
    refine ⟨146385319257686363802719069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97590212838457575868479379 146385319257686363802719069)
    ·
      refine ⟨54894494721632386426019651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146385319257686363802719069 54894494721632386426019651)
      ·
        refine ⟨82341742082448579639029477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54894494721632386426019651 82341742082448579639029477)
        ·
          refine ⟨15439076640459108682318027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82341742082448579639029477 15439076640459108682318027)
          ·
            refine ⟨23158614960688663023477041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15439076640459108682318027 23158614960688663023477041)
            ·
              refine ⟨17368961220516497267607781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23158614960688663023477041 17368961220516497267607781)
              ·
                refine ⟨3256680228846843237676459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17368961220516497267607781 3256680228846843237676459)
                ·
                  refine ⟨4885020343270264856514689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256680228846843237676459 4885020343270264856514689)
                  ·
                    refine ⟨3663765257452698642386017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4885020343270264856514689 3663765257452698642386017)
                    ·
                      refine ⟨2747823943089523981789513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663765257452698642386017 2747823943089523981789513)
                      ·
                        rfl

theorem cell23_5351368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_5351368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351368 prefixEnd_5351368 := by exact prefixLift 5351368
  have htrace : WordTrace (prefixWord ++ tailWord_5351368) baseStart_5351368 baseEnd_5351368 := by
    simpa [prefixWord, tailWord_5351368, baseEnd_5351368] using wordTrace_append hprefix tailTrace_5351368
  have hstable : (prefixWord ++ tailWord_5351368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351368).length < 2 ^ (prefixWord ++ tailWord_5351368).sum := by decide
  have hdescent : baseEnd_5351368 < baseStart_5351368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351370 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_5351370 : Nat := 118140960795 + 5351370 * 2 ^ 59
def prefixEnd_5351370 : Nat := 4983230072969 + 3 ^ 40 * 5351370 * 2
def baseEnd_5351370 : Nat := 915941656683610991321501

theorem tailTrace_5351370 : CollatzResearch.WordTrace tailWord_5351370 prefixEnd_5351370 915941656683610991321501 := by
  unfold tailWord_5351370
  simp only [CollatzResearch.WordTrace]
  refine ⟨48795124655726976519632891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130120332415271937385687709 48795124655726976519632891)
  ·
    refine ⟨73192686983590464779449337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48795124655726976519632891 73192686983590464779449337)
    ·
      refine ⟨54894515237692848584587003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73192686983590464779449337 54894515237692848584587003)
      ·
        refine ⟨82341772856539272876880505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54894515237692848584587003 82341772856539272876880505)
        ·
          refine ⟨61756329642404454657660379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82341772856539272876880505 61756329642404454657660379)
          ·
            refine ⟨92634494463606681986490569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61756329642404454657660379 92634494463606681986490569)
            ·
              refine ⟨69475870847705011489867927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92634494463606681986490569 69475870847705011489867927)
              ·
                refine ⟨104213806271557517234801891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69475870847705011489867927 104213806271557517234801891)
                ·
                  refine ⟨156320709407336275852202837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104213806271557517234801891 156320709407336275852202837)
                  ·
                    refine ⟨915941656683610991321501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156320709407336275852202837 915941656683610991321501)
                    ·
                      rfl

theorem cell23_5351370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_5351370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351370 prefixEnd_5351370 := by exact prefixLift 5351370
  have htrace : WordTrace (prefixWord ++ tailWord_5351370) baseStart_5351370 baseEnd_5351370 := by
    simpa [prefixWord, tailWord_5351370, baseEnd_5351370] using wordTrace_append hprefix tailTrace_5351370
  have hstable : (prefixWord ++ tailWord_5351370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351370).length < 2 ^ (prefixWord ++ tailWord_5351370).sum := by decide
  have hdescent : baseEnd_5351370 < baseStart_5351370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351377 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_5351377 : Nat := 118140960795 + 5351377 * 2 ^ 59
def prefixEnd_5351377 : Nat := 4983230072969 + 3 ^ 40 * 5351377 * 2
def baseEnd_5351377 : Nat := 2747828564415414446576971

theorem tailTrace_5351377 : CollatzResearch.WordTrace tailWord_5351377 prefixEnd_5351377 2747828564415414446576971 := by
  unfold tailWord_5351377
  simp only [CollatzResearch.WordTrace]
  refine ⟨195180753933882546274036385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130120502622588364182690923 195180753933882546274036385)
  ·
    refine ⟨146385565450411909705527289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195180753933882546274036385 146385565450411909705527289)
    ·
      refine ⟨109789174087808932279145467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146385565450411909705527289 109789174087808932279145467)
      ·
        refine ⟨164683761131713398418718201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109789174087808932279145467 164683761131713398418718201)
        ·
          refine ⟨123512820848785048814038651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164683761131713398418718201 123512820848785048814038651)
          ·
            refine ⟨185269231273177573221057977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123512820848785048814038651 185269231273177573221057977)
            ·
              refine ⟨138951923454883179915793483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185269231273177573221057977 138951923454883179915793483)
              ·
                refine ⟨208427885182324769873690225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138951923454883179915793483 208427885182324769873690225)
                ·
                  refine ⟨156320913886743577405267669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208427885182324769873690225 156320913886743577405267669)
                  ·
                    refine ⟨3663771419220552595435961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 156320913886743577405267669 3663771419220552595435961)
                    ·
                      refine ⟨2747828564415414446576971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663771419220552595435961 2747828564415414446576971)
                      ·
                        rfl

theorem cell23_5351377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_5351377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351377 prefixEnd_5351377 := by exact prefixLift 5351377
  have htrace : WordTrace (prefixWord ++ tailWord_5351377) baseStart_5351377 baseEnd_5351377 := by
    simpa [prefixWord, tailWord_5351377, baseEnd_5351377] using wordTrace_append hprefix tailTrace_5351377
  have hstable : (prefixWord ++ tailWord_5351377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351377).length < 2 ^ (prefixWord ++ tailWord_5351377).sum := by decide
  have hdescent : baseEnd_5351377 < baseStart_5351377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351378 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_5351378 : Nat := 118140960795 + 5351378 * 2 ^ 59
def prefixEnd_5351378 : Nat := 4983230072969 + 3 ^ 40 * 5351378 * 2
def baseEnd_5351378 : Nat := 915943025965356314221489

theorem tailTrace_5351378 : CollatzResearch.WordTrace tailWord_5351378 prefixEnd_5351378 915943025965356314221489 := by
  unfold tailWord_5351378
  simp only [CollatzResearch.WordTrace]
  refine ⟨48795197601719730861205697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130120526937919282296548525 48795197601719730861205697)
  ·
    refine ⟨36596398201289798145904273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48795197601719730861205697 36596398201289798145904273)
    ·
      refine ⟨27447298650967348609428205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36596398201289798145904273 27447298650967348609428205)
      ·
        refine ⟨10292736994112755728535577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27447298650967348609428205 10292736994112755728535577)
        ·
          refine ⟨7719552745584566796401683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10292736994112755728535577 7719552745584566796401683)
          ·
            refine ⟨11579329118376850194602525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719552745584566796401683 11579329118376850194602525)
            ·
              refine ⟨4342248419391318822975947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11579329118376850194602525 4342248419391318822975947)
              ·
                refine ⟨6513372629086978234463921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342248419391318822975947 6513372629086978234463921)
                ·
                  refine ⟨4885029471815233675847941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6513372629086978234463921 4885029471815233675847941)
                  ·
                    refine ⟨915943025965356314221489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4885029471815233675847941 915943025965356314221489)
                    ·
                      rfl

theorem cell23_5351378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_5351378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351378 prefixEnd_5351378 := by exact prefixLift 5351378
  have htrace : WordTrace (prefixWord ++ tailWord_5351378) baseStart_5351378 baseEnd_5351378 := by
    simpa [prefixWord, tailWord_5351378, baseEnd_5351378] using wordTrace_append hprefix tailTrace_5351378
  have hstable : (prefixWord ++ tailWord_5351378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351378).length < 2 ^ (prefixWord ++ tailWord_5351378).sum := by decide
  have hdescent : baseEnd_5351378 < baseStart_5351378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351440 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_5351440 : Nat := 118140960795 + 5351440 * 2 ^ 59
def prefixEnd_5351440 : Nat := 4983230072969 + 3 ^ 40 * 5351440 * 2
def baseEnd_5351440 : Nat := 2747860913696647700089181

theorem tailTrace_5351440 : CollatzResearch.WordTrace tailWord_5351440 prefixEnd_5351440 2747860913696647700089181 := by
  unfold tailWord_5351440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97591525866327154016789887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130122034488436205355719849 97591525866327154016789887)
  ·
    refine ⟨146387288799490731025184831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97591525866327154016789887 146387288799490731025184831)
    ·
      refine ⟨219580933199236096537777247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146387288799490731025184831 219580933199236096537777247)
      ·
        refine ⟨329371399798854144806665871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219580933199236096537777247 329371399798854144806665871)
        ·
          refine ⟨494057099698281217209998807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329371399798854144806665871 494057099698281217209998807)
          ·
            refine ⟨741085649547421825814998211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494057099698281217209998807 741085649547421825814998211)
            ·
              refine ⟨1111628474321132738722497317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741085649547421825814998211 1111628474321132738722497317)
              ·
                refine ⟨208430338935212388510468247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1111628474321132738722497317 208430338935212388510468247)
                ·
                  refine ⟨312645508402818582765702371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208430338935212388510468247 312645508402818582765702371)
                  ·
                    refine ⟨468968262604227874148553557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 312645508402818582765702371 468968262604227874148553557)
                    ·
                      refine ⟨2747860913696647700089181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 468968262604227874148553557 2747860913696647700089181)
                      ·
                        rfl

theorem cell23_5351440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_5351440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351440 prefixEnd_5351440 := by exact prefixLift 5351440
  have htrace : WordTrace (prefixWord ++ tailWord_5351440) baseStart_5351440 baseEnd_5351440 := by
    simpa [prefixWord, tailWord_5351440, baseEnd_5351440] using wordTrace_append hprefix tailTrace_5351440
  have hstable : (prefixWord ++ tailWord_5351440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351440).length < 2 ^ (prefixWord ++ tailWord_5351440).sum := by decide
  have hdescent : baseEnd_5351440 < baseStart_5351440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351445 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_5351445 : Nat := 118140960795 + 5351445 * 2 ^ 59
def prefixEnd_5351445 : Nat := 4983230072969 + 3 ^ 40 * 5351445 * 2
def baseEnd_5351445 : Nat := 2747863481099920180526659

theorem tailTrace_5351445 : CollatzResearch.WordTrace tailWord_5351445 prefixEnd_5351445 2747863481099920180526659 := by
  unfold tailWord_5351445
  simp only [CollatzResearch.WordTrace]
  refine ⟨195183234097636193887511789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130122156065090795925007859 195183234097636193887511789)
  ·
    refine ⟨73193712786613572707816921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195183234097636193887511789 73193712786613572707816921)
    ·
      refine ⟨54895284589960179530862691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73193712786613572707816921 54895284589960179530862691)
      ·
        refine ⟨82342926884940269296294037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54895284589960179530862691 82342926884940269296294037)
        ·
          refine ⟨3859824697731575123263783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82342926884940269296294037 3859824697731575123263783)
          ·
            refine ⟨5789737046597362684895675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859824697731575123263783 5789737046597362684895675)
            ·
              refine ⟨8684605569896044027343513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789737046597362684895675 8684605569896044027343513)
              ·
                refine ⟨6513454177422033020507635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8684605569896044027343513 6513454177422033020507635)
                ·
                  refine ⟨9770181266133049530761453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513454177422033020507635 9770181266133049530761453)
                  ·
                    refine ⟨3663817974799893574035545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9770181266133049530761453 3663817974799893574035545)
                    ·
                      refine ⟨2747863481099920180526659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663817974799893574035545 2747863481099920180526659)
                      ·
                        rfl

theorem cell23_5351445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_5351445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351445 prefixEnd_5351445 := by exact prefixLift 5351445
  have htrace : WordTrace (prefixWord ++ tailWord_5351445) baseStart_5351445 baseEnd_5351445 := by
    simpa [prefixWord, tailWord_5351445, baseEnd_5351445] using wordTrace_append hprefix tailTrace_5351445
  have hstable : (prefixWord ++ tailWord_5351445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351445).length < 2 ^ (prefixWord ++ tailWord_5351445).sum := by decide
  have hdescent : baseEnd_5351445 < baseStart_5351445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351481 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 5]
def baseStart_5351481 : Nat := 118140960795 + 5351481 * 2 ^ 59
def prefixEnd_5351481 : Nat := 4983230072969 + 3 ^ 40 * 5351481 * 2
def baseEnd_5351481 : Nat := 305320218489275782186277

theorem tailTrace_5351481 : CollatzResearch.WordTrace tailWord_5351481 prefixEnd_5351481 305320218489275782186277 := by
  unfold tailWord_5351481
  simp only [CollatzResearch.WordTrace]
  refine ⟨195184547125505772035822297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130123031417003848023881531 195184547125505772035822297)
  ·
    refine ⟨146388410344129329026866723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195184547125505772035822297 146388410344129329026866723)
    ·
      refine ⟨219582615516193993540300085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146388410344129329026866723 219582615516193993540300085)
      ·
        refine ⟨20585870204643186894403133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219582615516193993540300085 20585870204643186894403133)
        ·
          refine ⟨7719701326741195085401175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20585870204643186894403133 7719701326741195085401175)
          ·
            refine ⟨11579551990111792628101763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719701326741195085401175 11579551990111792628101763)
            ·
              refine ⟨17369327985167688942152645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11579551990111792628101763 17369327985167688942152645)
              ·
                refine ⟨3256748997218941676653621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17369327985167688942152645 3256748997218941676653621)
                ·
                  refine ⟨305320218489275782186277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3256748997218941676653621 305320218489275782186277)
                  ·
                    rfl

theorem cell23_5351481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 5].length) (baseStart_5351481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351481 prefixEnd_5351481 := by exact prefixLift 5351481
  have htrace : WordTrace (prefixWord ++ tailWord_5351481) baseStart_5351481 baseEnd_5351481 := by
    simpa [prefixWord, tailWord_5351481, baseEnd_5351481] using wordTrace_append hprefix tailTrace_5351481
  have hstable : (prefixWord ++ tailWord_5351481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351481).length < 2 ^ (prefixWord ++ tailWord_5351481).sum := by decide
  have hdescent : baseEnd_5351481 < baseStart_5351481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351484 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_5351484 : Nat := 118140960795 + 5351484 * 2 ^ 59
def prefixEnd_5351484 : Nat := 4983230072969 + 3 ^ 40 * 5351484 * 2
def baseEnd_5351484 : Nat := 2747883506845445527938979

theorem tailTrace_5351484 : CollatzResearch.WordTrace tailWord_5351484 prefixEnd_5351484 2747883506845445527938979 := by
  unfold tailWord_5351484
  simp only [CollatzResearch.WordTrace]
  refine ⟨97592328272247451774090753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130123104362996602365454337 97592328272247451774090753)
  ·
    refine ⟨73194246204185588830568065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97592328272247451774090753 73194246204185588830568065)
    ·
      refine ⟨54895684653139191622926049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73194246204185588830568065 54895684653139191622926049)
      ·
        refine ⟨41171763489854393717194537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54895684653139191622926049 41171763489854393717194537)
        ·
          refine ⟨30878822617390795287895903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41171763489854393717194537 30878822617390795287895903)
          ·
            refine ⟨46318233926086192931843855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30878822617390795287895903 46318233926086192931843855)
            ·
              refine ⟨69477350889129289397765783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46318233926086192931843855 69477350889129289397765783)
              ·
                refine ⟨104216026333693934096648675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69477350889129289397765783 104216026333693934096648675)
                ·
                  refine ⟨156324039500540901144973013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104216026333693934096648675 156324039500540901144973013)
                  ·
                    refine ⟨3663844675793927370585305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 156324039500540901144973013 3663844675793927370585305)
                    ·
                      refine ⟨2747883506845445527938979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663844675793927370585305 2747883506845445527938979)
                      ·
                        rfl

theorem cell23_5351484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_5351484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351484 prefixEnd_5351484 := by exact prefixLift 5351484
  have htrace : WordTrace (prefixWord ++ tailWord_5351484) baseStart_5351484 baseEnd_5351484 := by
    simpa [prefixWord, tailWord_5351484, baseEnd_5351484] using wordTrace_append hprefix tailTrace_5351484
  have hstable : (prefixWord ++ tailWord_5351484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351484).length < 2 ^ (prefixWord ++ tailWord_5351484).sum := by decide
  have hdescent : baseEnd_5351484 < baseStart_5351484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351487 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_5351487 : Nat := 118140960795 + 5351487 * 2 ^ 59
def prefixEnd_5351487 : Nat := 4983230072969 + 3 ^ 40 * 5351487 * 2
def baseEnd_5351487 : Nat := 2747885047287409016201465

theorem tailTrace_5351487 : CollatzResearch.WordTrace tailWord_5351487 prefixEnd_5351487 2747885047287409016201465 := by
  unfold tailWord_5351487
  simp only [CollatzResearch.WordTrace]
  refine ⟨195184765963484035060540715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130123177308989356707027143 195184765963484035060540715)
  ·
    refine ⟨292777148945226052590811073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195184765963484035060540715 292777148945226052590811073)
    ·
      refine ⟨219582861708919539443108305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292777148945226052590811073 219582861708919539443108305)
      ·
        refine ⟨164687146281689654582331229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219582861708919539443108305 164687146281689654582331229)
        ·
          refine ⟨61757679855633620468374211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164687146281689654582331229 61757679855633620468374211)
          ·
            refine ⟨92636519783450430702561317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61757679855633620468374211 92636519783450430702561317)
            ·
              refine ⟨17369347459396955756730247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92636519783450430702561317 17369347459396955756730247)
              ·
                refine ⟨26054021189095433635095371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17369347459396955756730247 26054021189095433635095371)
                ·
                  refine ⟨39081031783643150452643057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26054021189095433635095371 39081031783643150452643057)
                  ·
                    refine ⟨29310773837732362839482293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39081031783643150452643057 29310773837732362839482293)
                    ·
                      refine ⟨2747885047287409016201465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29310773837732362839482293 2747885047287409016201465)
                      ·
                        rfl

theorem cell23_5351487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_5351487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351487 prefixEnd_5351487 := by exact prefixLift 5351487
  have htrace : WordTrace (prefixWord ++ tailWord_5351487) baseStart_5351487 baseEnd_5351487 := by
    simpa [prefixWord, tailWord_5351487, baseEnd_5351487] using wordTrace_append hprefix tailTrace_5351487
  have hstable : (prefixWord ++ tailWord_5351487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351487).length < 2 ^ (prefixWord ++ tailWord_5351487).sum := by decide
  have hdescent : baseEnd_5351487 < baseStart_5351487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351497 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_5351497 : Nat := 118140960795 + 5351497 * 2 ^ 59
def prefixEnd_5351497 : Nat := 4983230072969 + 3 ^ 40 * 5351497 * 2
def baseEnd_5351497 : Nat := 2747890182093953977076419

theorem tailTrace_5351497 : CollatzResearch.WordTrace tailWord_5351497 prefixEnd_5351497 2747890182093953977076419 := by
  unfold tailWord_5351497
  simp only [CollatzResearch.WordTrace]
  refine ⟨195185130693447806768404745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130123420462298537845603163 195185130693447806768404745)
  ·
    refine ⟨146388848020085855076303559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195185130693447806768404745 146388848020085855076303559)
    ·
      refine ⟨219583272030128782614455339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146388848020085855076303559 219583272030128782614455339)
      ·
        refine ⟨329374908045193173921683009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219583272030128782614455339 329374908045193173921683009)
        ·
          refine ⟨247031181033894880441262257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329374908045193173921683009 247031181033894880441262257)
          ·
            refine ⟨185273385775421160330946693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247031181033894880441262257 185273385775421160330946693)
            ·
              refine ⟨34738759832891467562052505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185273385775421160330946693 34738759832891467562052505)
              ·
                refine ⟨26054069874668600671539379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34738759832891467562052505 26054069874668600671539379)
                ·
                  refine ⟨39081104812002901007309069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26054069874668600671539379 39081104812002901007309069)
                  ·
                    refine ⟨14655414304501087877740901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39081104812002901007309069 14655414304501087877740901)
                    ·
                      refine ⟨2747890182093953977076419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14655414304501087877740901 2747890182093953977076419)
                      ·
                        rfl

theorem cell23_5351497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_5351497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351497 prefixEnd_5351497 := by exact prefixLift 5351497
  have htrace : WordTrace (prefixWord ++ tailWord_5351497) baseStart_5351497 baseEnd_5351497 := by
    simpa [prefixWord, tailWord_5351497, baseEnd_5351497] using wordTrace_append hprefix tailTrace_5351497
  have hstable : (prefixWord ++ tailWord_5351497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351497).length < 2 ^ (prefixWord ++ tailWord_5351497).sum := by decide
  have hdescent : baseEnd_5351497 < baseStart_5351497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351501 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5351501 : Nat := 118140960795 + 5351501 * 2 ^ 59
def prefixEnd_5351501 : Nat := 4983230072969 + 3 ^ 40 * 5351501 * 2
def baseEnd_5351501 : Nat := 2747892236016571961426401

theorem tailTrace_5351501 : CollatzResearch.WordTrace tailWord_5351501 prefixEnd_5351501 2747892236016571961426401 := by
  unfold tailWord_5351501
  simp only [CollatzResearch.WordTrace]
  refine ⟨195185276585433315451550357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130123517723622210301033571 195185276585433315451550357)
  ·
    refine ⟨9149309839942186661791423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195185276585433315451550357 9149309839942186661791423)
    ·
      refine ⟨13723964759913279992687135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149309839942186661791423 13723964759913279992687135)
      ·
        refine ⟨20585947139869919989030703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13723964759913279992687135 20585947139869919989030703)
        ·
          refine ⟨30878920709804879983546055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20585947139869919989030703 30878920709804879983546055)
          ·
            refine ⟨46318381064707319975319083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30878920709804879983546055 46318381064707319975319083)
            ·
              refine ⟨69477571597060979962978625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46318381064707319975319083 69477571597060979962978625)
              ·
                refine ⟨52108178697795734972233969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69477571597060979962978625 52108178697795734972233969)
                ·
                  refine ⟨39081134023346801229175477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52108178697795734972233969 39081134023346801229175477)
                  ·
                    refine ⟨3663856314688762615235201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39081134023346801229175477 3663856314688762615235201)
                    ·
                      refine ⟨2747892236016571961426401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663856314688762615235201 2747892236016571961426401)
                      ·
                        rfl

theorem cell23_5351501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5351501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351501 prefixEnd_5351501 := by exact prefixLift 5351501
  have htrace : WordTrace (prefixWord ++ tailWord_5351501) baseStart_5351501 baseEnd_5351501 := by
    simpa [prefixWord, tailWord_5351501, baseEnd_5351501] using wordTrace_append hprefix tailTrace_5351501
  have hstable : (prefixWord ++ tailWord_5351501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351501).length < 2 ^ (prefixWord ++ tailWord_5351501).sum := by decide
  have hdescent : baseEnd_5351501 < baseStart_5351501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351514 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_5351514 : Nat := 118140960795 + 5351514 * 2 ^ 59
def prefixEnd_5351514 : Nat := 4983230072969 + 3 ^ 40 * 5351514 * 2
def baseEnd_5351514 : Nat := 2747898911265080410563841

theorem tailTrace_5351514 : CollatzResearch.WordTrace tailWord_5351514 prefixEnd_5351514 2747898911265080410563841 := by
  unfold tailWord_5351514
  simp only [CollatzResearch.WordTrace]
  refine ⟨48796437683596554667943399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130123833822924145781182397 48796437683596554667943399)
  ·
    refine ⟨73194656525394832001915099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48796437683596554667943399 73194656525394832001915099)
    ·
      refine ⟨109791984788092248002872649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73194656525394832001915099 109791984788092248002872649)
      ·
        refine ⟨82343988591069186002154487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109791984788092248002872649 82343988591069186002154487)
        ·
          refine ⟨123515982886603779003231731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82343988591069186002154487 123515982886603779003231731)
          ·
            refine ⟨185273974329905668504847597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123515982886603779003231731 185273974329905668504847597)
            ·
              refine ⟨69477740373714625689317849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185273974329905668504847597 69477740373714625689317849)
              ·
                refine ⟨52108305280285969266988387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69477740373714625689317849 52108305280285969266988387)
                ·
                  refine ⟨78162457920428953900482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52108305280285969266988387 78162457920428953900482581)
                  ·
                    refine ⟨3663865215020107214085121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78162457920428953900482581 3663865215020107214085121)
                    ·
                      refine ⟨2747898911265080410563841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663865215020107214085121 2747898911265080410563841)
                      ·
                        rfl

theorem cell23_5351514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_5351514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351514 prefixEnd_5351514 := by exact prefixLift 5351514
  have htrace : WordTrace (prefixWord ++ tailWord_5351514) baseStart_5351514 baseEnd_5351514 := by
    simpa [prefixWord, tailWord_5351514, baseEnd_5351514] using wordTrace_append hprefix tailTrace_5351514
  have hstable : (prefixWord ++ tailWord_5351514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351514).length < 2 ^ (prefixWord ++ tailWord_5351514).sum := by decide
  have hdescent : baseEnd_5351514 < baseStart_5351514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351527 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5351527 : Nat := 118140960795 + 5351527 * 2 ^ 59
def prefixEnd_5351527 : Nat := 4983230072969 + 3 ^ 40 * 5351527 * 2
def baseEnd_5351527 : Nat := 2747905586513588859701281

theorem tailTrace_5351527 : CollatzResearch.WordTrace tailWord_5351527 prefixEnd_5351527 2747905586513588859701281 := by
  unfold tailWord_5351527
  simp only [CollatzResearch.WordTrace]
  refine ⟨195186224883339121891996835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130124149922226081261331223 195186224883339121891996835)
  ·
    refine ⟨292779337325008682837995253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195186224883339121891996835 292779337325008682837995253)
    ·
      refine ⟨27448062874219564016062055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 292779337325008682837995253 27448062874219564016062055)
      ·
        refine ⟨41172094311329346024093083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27448062874219564016062055 41172094311329346024093083)
        ·
          refine ⟨61758141466994019036139625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41172094311329346024093083 61758141466994019036139625)
          ·
            refine ⟨46318606100245514277104719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61758141466994019036139625 46318606100245514277104719)
            ·
              refine ⟨69477909150368271415657079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46318606100245514277104719 69477909150368271415657079)
              ·
                refine ⟨104216863725552407123485619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69477909150368271415657079 104216863725552407123485619)
                ·
                  refine ⟨156325295588328610685228429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104216863725552407123485619 156325295588328610685228429)
                  ·
                    refine ⟨58621985845623229006960661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156325295588328610685228429 58621985845623229006960661)
                    ·
                      refine ⟨2747905586513588859701281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58621985845623229006960661 2747905586513588859701281)
                      ·
                        rfl

theorem cell23_5351527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5351527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351527 prefixEnd_5351527 := by exact prefixLift 5351527
  have htrace : WordTrace (prefixWord ++ tailWord_5351527) baseStart_5351527 baseEnd_5351527 := by
    simpa [prefixWord, tailWord_5351527, baseEnd_5351527] using wordTrace_append hprefix tailTrace_5351527
  have hstable : (prefixWord ++ tailWord_5351527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351527).length < 2 ^ (prefixWord ++ tailWord_5351527).sum := by decide
  have hdescent : baseEnd_5351527 < baseStart_5351527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351537 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 8]
def baseStart_5351537 : Nat := 118140960795 + 5351537 * 2 ^ 59
def prefixEnd_5351537 : Nat := 4983230072969 + 3 ^ 40 * 5351537 * 2
def baseEnd_5351537 : Nat := 305323413480014868952915

theorem tailTrace_5351537 : CollatzResearch.WordTrace tailWord_5351537 prefixEnd_5351537 305323413480014868952915 := by
  unfold tailWord_5351537
  simp only [CollatzResearch.WordTrace]
  refine ⟨195186589613302893599860865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130124393075535262399907243 195186589613302893599860865)
  ·
    refine ⟨146389942209977170199895649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195186589613302893599860865 146389942209977170199895649)
    ·
      refine ⟨109792456657482877649921737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146389942209977170199895649 109792456657482877649921737)
      ·
        refine ⟨82344342493112158237441303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109792456657482877649921737 82344342493112158237441303)
        ·
          refine ⟨123516513739668237356161955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82344342493112158237441303 123516513739668237356161955)
          ·
            refine ⟨185274770609502356034242933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123516513739668237356161955 185274770609502356034242933)
            ·
              refine ⟨17369509744640845878210275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185274770609502356034242933 17369509744640845878210275)
              ·
                refine ⟨26054264616961268817315413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17369509744640845878210275 26054264616961268817315413)
                ·
                  refine ⟨305323413480014868952915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26054264616961268817315413 305323413480014868952915)
                  ·
                    rfl

theorem cell23_5351537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_5351537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351537 prefixEnd_5351537 := by exact prefixLift 5351537
  have htrace : WordTrace (prefixWord ++ tailWord_5351537) baseStart_5351537 baseEnd_5351537 := by
    simpa [prefixWord, tailWord_5351537, baseEnd_5351537] using wordTrace_append hprefix tailTrace_5351537
  have hstable : (prefixWord ++ tailWord_5351537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351537).length < 2 ^ (prefixWord ++ tailWord_5351537).sum := by decide
  have hdescent : baseEnd_5351537 < baseStart_5351537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351575 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 1, 4]
def baseStart_5351575 : Nat := 118140960795 + 5351575 * 2 ^ 59
def prefixEnd_5351575 : Nat := 4983230072969 + 3 ^ 40 * 5351575 * 2
def baseEnd_5351575 : Nat := 915976744528334890633687

theorem tailTrace_5351575 : CollatzResearch.WordTrace tailWord_5351575 prefixEnd_5351575 915976744528334890633687 := by
  unfold tailWord_5351575
  simp only [CollatzResearch.WordTrace]
  refine ⟨195187975587165226089744179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130125317058110150726496119 195187975587165226089744179)
  ·
    refine ⟨292781963380747839134616269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195187975587165226089744179 292781963380747839134616269)
    ·
      refine ⟨109793236267780439675481101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292781963380747839134616269 109793236267780439675481101)
      ·
        refine ⟨41172463600417664878305413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109793236267780439675481101 41172463600417664878305413)
        ·
          refine ⟨7719836925078312164682265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41172463600417664878305413 7719836925078312164682265)
          ·
            refine ⟨5789877693808734123511699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7719836925078312164682265 5789877693808734123511699)
            ·
              refine ⟨8684816540713101185267549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789877693808734123511699 8684816540713101185267549)
              ·
                refine ⟨3256806202767412944475331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8684816540713101185267549 3256806202767412944475331)
                ·
                  refine ⟨4885209304151119416712997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256806202767412944475331 4885209304151119416712997)
                  ·
                    refine ⟨915976744528334890633687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4885209304151119416712997 915976744528334890633687)
                    ·
                      rfl

theorem cell23_5351575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_5351575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351575 prefixEnd_5351575 := by exact prefixLift 5351575
  have htrace : WordTrace (prefixWord ++ tailWord_5351575) baseStart_5351575 baseEnd_5351575 := by
    simpa [prefixWord, tailWord_5351575, baseEnd_5351575] using wordTrace_append hprefix tailTrace_5351575
  have hstable : (prefixWord ++ tailWord_5351575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351575).length < 2 ^ (prefixWord ++ tailWord_5351575).sum := by decide
  have hdescent : baseEnd_5351575 < baseStart_5351575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351605 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 6]
def baseStart_5351605 : Nat := 118140960795 + 5351605 * 2 ^ 59
def prefixEnd_5351605 : Nat := 4983230072969 + 3 ^ 40 * 5351605 * 2
def baseEnd_5351605 : Nat := 305327293111626617169547

theorem tailTrace_5351605 : CollatzResearch.WordTrace tailWord_5351605 prefixEnd_5351605 305327293111626617169547 := by
  unfold tailWord_5351605
  simp only [CollatzResearch.WordTrace]
  refine ⟨195189069777056541213336269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130126046518037694142224179 195189069777056541213336269)
  ·
    refine ⟨73195901166396202955001101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195189069777056541213336269 73195901166396202955001101)
    ·
      refine ⟨27448462937398576108125413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73195901166396202955001101 27448462937398576108125413)
      ·
        refine ⟨5146586800762233020273515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27448462937398576108125413 5146586800762233020273515)
        ·
          refine ⟨7719880201143349530410273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146586800762233020273515 7719880201143349530410273)
          ·
            refine ⟨5789910150857512147807705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7719880201143349530410273 5789910150857512147807705)
            ·
              refine ⟨4342432613143134110855779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5789910150857512147807705 4342432613143134110855779)
              ·
                refine ⟨6513648919714701166283669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342432613143134110855779 6513648919714701166283669)
                ·
                  refine ⟨305327293111626617169547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6513648919714701166283669 305327293111626617169547)
                  ·
                    rfl

theorem cell23_5351605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_5351605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351605 prefixEnd_5351605 := by exact prefixLift 5351605
  have htrace : WordTrace (prefixWord ++ tailWord_5351605) baseStart_5351605 baseEnd_5351605 := by
    simpa [prefixWord, tailWord_5351605, baseEnd_5351605] using wordTrace_append hprefix tailTrace_5351605
  have hstable : (prefixWord ++ tailWord_5351605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351605).length < 2 ^ (prefixWord ++ tailWord_5351605).sum := by decide
  have hdescent : baseEnd_5351605 < baseStart_5351605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351621 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_5351621 : Nat := 118140960795 + 5351621 * 2 ^ 59
def prefixEnd_5351621 : Nat := 4983230072969 + 3 ^ 40 * 5351621 * 2
def baseEnd_5351621 : Nat := 2747953853695111491925849

theorem tailTrace_5351621 : CollatzResearch.WordTrace tailWord_5351621 prefixEnd_5351621 2747953853695111491925849 := by
  unfold tailWord_5351621
  simp only [CollatzResearch.WordTrace]
  refine ⟨195189653344998575945918717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130126435563332383963945811 195189653344998575945918717)
  ·
    refine ⟨73196120004374465979719519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195189653344998575945918717 73196120004374465979719519)
    ·
      refine ⟨109794180006561698969579279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73196120004374465979719519 109794180006561698969579279)
      ·
        refine ⟨164691270009842548454368919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109794180006561698969579279 164691270009842548454368919)
        ·
          refine ⟨247036905014763822681553379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164691270009842548454368919 247036905014763822681553379)
          ·
            refine ⟨370555357522145734022330069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247036905014763822681553379 370555357522145734022330069)
            ·
              refine ⟨8684891191925290641148361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 370555357522145734022330069 8684891191925290641148361)
              ·
                refine ⟨6513668393943967980861271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8684891191925290641148361 6513668393943967980861271)
                ·
                  refine ⟨9770502590915951971291907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513668393943967980861271 9770502590915951971291907)
                  ·
                    refine ⟨14655753886373927956937861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9770502590915951971291907 14655753886373927956937861)
                    ·
                      refine ⟨2747953853695111491925849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14655753886373927956937861 2747953853695111491925849)
                      ·
                        rfl

theorem cell23_5351621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_5351621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351621 prefixEnd_5351621 := by exact prefixLift 5351621
  have htrace : WordTrace (prefixWord ++ tailWord_5351621) baseStart_5351621 baseEnd_5351621 := by
    simpa [prefixWord, tailWord_5351621, baseEnd_5351621] using wordTrace_append hprefix tailTrace_5351621
  have hstable : (prefixWord ++ tailWord_5351621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351621).length < 2 ^ (prefixWord ++ tailWord_5351621).sum := by decide
  have hdescent : baseEnd_5351621 < baseStart_5351621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351627 : List Nat := [1, 1, 1, 1, 3, 2, 3, 11]
def baseStart_5351627 : Nat := 118140960795 + 5351627 * 2 ^ 59
def prefixEnd_5351627 : Nat := 4983230072969 + 3 ^ 40 * 5351627 * 2
def baseEnd_5351627 : Nat := 101776182762186609942623

theorem tailTrace_5351627 : CollatzResearch.WordTrace tailWord_5351627 prefixEnd_5351627 101776182762186609942623 := by
  unfold tailWord_5351627
  simp only [CollatzResearch.WordTrace]
  refine ⟨195189872182976838970637135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130126581455317892647091423 195189872182976838970637135)
  ·
    refine ⟨292784808274465258455955703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195189872182976838970637135 292784808274465258455955703)
    ·
      refine ⟨439177212411697887683933555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292784808274465258455955703 439177212411697887683933555)
      ·
        refine ⟨658765818617546831525900333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439177212411697887683933555 658765818617546831525900333)
        ·
          refine ⟨247037181981580061822212625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 658765818617546831525900333 247037181981580061822212625)
          ·
            refine ⟨185277886486185046366659469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247037181981580061822212625 185277886486185046366659469)
            ·
              refine ⟨69479207432319392387497301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185277886486185046366659469 69479207432319392387497301)
              ·
                refine ⟨101776182762186609942623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69479207432319392387497301 101776182762186609942623)
                ·
                  rfl

theorem cell23_5351627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 11].length) (baseStart_5351627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351627 prefixEnd_5351627 := by exact prefixLift 5351627
  have htrace : WordTrace (prefixWord ++ tailWord_5351627) baseStart_5351627 baseEnd_5351627 := by
    simpa [prefixWord, tailWord_5351627, baseEnd_5351627] using wordTrace_append hprefix tailTrace_5351627
  have hstable : (prefixWord ++ tailWord_5351627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351627).length < 2 ^ (prefixWord ++ tailWord_5351627).sum := by decide
  have hdescent : baseEnd_5351627 < baseStart_5351627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351641 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_5351641 : Nat := 118140960795 + 5351641 * 2 ^ 59
def prefixEnd_5351641 : Nat := 4983230072969 + 3 ^ 40 * 5351641 * 2
def baseEnd_5351641 : Nat := 2747964123308201413675757

theorem tailTrace_5351641 : CollatzResearch.WordTrace tailWord_5351641 prefixEnd_5351641 2747964123308201413675757 := by
  unfold tailWord_5351641
  simp only [CollatzResearch.WordTrace]
  refine ⟨195190382804926119361646777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130126921869950746241097851 195190382804926119361646777)
  ·
    refine ⟨146392787103694589521235083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195190382804926119361646777 146392787103694589521235083)
    ·
      refine ⟨219589180655541884281852625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146392787103694589521235083 219589180655541884281852625)
      ·
        refine ⟨164691885491656413211389469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219589180655541884281852625 164691885491656413211389469)
        ·
          refine ⟨61759457059371154954271051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164691885491656413211389469 61759457059371154954271051)
          ·
            refine ⟨92639185589056732431406577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61759457059371154954271051 92639185589056732431406577)
            ·
              refine ⟨69479389191792549323554933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92639185589056732431406577 69479389191792549323554933)
              ·
                refine ⟨6513692736730551499083275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69479389191792549323554933 6513692736730551499083275)
                ·
                  refine ⟨9770539105095827248624913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513692736730551499083275 9770539105095827248624913)
                  ·
                    refine ⟨7327904328821870436468685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9770539105095827248624913 7327904328821870436468685)
                    ·
                      refine ⟨2747964123308201413675757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7327904328821870436468685 2747964123308201413675757)
                      ·
                        rfl

theorem cell23_5351641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_5351641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351641 prefixEnd_5351641 := by exact prefixLift 5351641
  have htrace : WordTrace (prefixWord ++ tailWord_5351641) baseStart_5351641 baseEnd_5351641 := by
    simpa [prefixWord, tailWord_5351641, baseEnd_5351641] using wordTrace_append hprefix tailTrace_5351641
  have hstable : (prefixWord ++ tailWord_5351641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351641).length < 2 ^ (prefixWord ++ tailWord_5351641).sum := by decide
  have hdescent : baseEnd_5351641 < baseStart_5351641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351704 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_5351704 : Nat := 118140960795 + 5351704 * 2 ^ 59
def prefixEnd_5351704 : Nat := 4983230072969 + 3 ^ 40 * 5351704 * 2
def baseEnd_5351704 : Nat := 915998824196478222395989

theorem tailTrace_5351704 : CollatzResearch.WordTrace tailWord_5351704 prefixEnd_5351704 915998824196478222395989 := by
  unfold tailWord_5351704
  simp only [CollatzResearch.WordTrace]
  refine ⟨97596340301848940560595083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130128453735798587414126777 97596340301848940560595083)
  ·
    refine ⟨146394510452773410840892625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97596340301848940560595083 146394510452773410840892625)
    ·
      refine ⟨109795882839580058130669469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146394510452773410840892625 109795882839580058130669469)
      ·
        refine ⟨41173456064842521799001051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109795882839580058130669469 41173456064842521799001051)
        ·
          refine ⟨61760184097263782698501577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41173456064842521799001051 61760184097263782698501577)
          ·
            refine ⟨46320138072947837023876183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61760184097263782698501577 46320138072947837023876183)
            ·
              refine ⟨69480207109421755535814275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46320138072947837023876183 69480207109421755535814275)
              ·
                refine ⟨104220310664132633303721413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69480207109421755535814275 104220310664132633303721413)
                ·
                  refine ⟨19541308249524868744447765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104220310664132633303721413 19541308249524868744447765)
                  ·
                    refine ⟨915998824196478222395989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19541308249524868744447765 915998824196478222395989)
                    ·
                      rfl

theorem cell23_5351704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_5351704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351704 prefixEnd_5351704 := by exact prefixLift 5351704
  have htrace : WordTrace (prefixWord ++ tailWord_5351704) baseStart_5351704 baseEnd_5351704 := by
    simpa [prefixWord, tailWord_5351704, baseEnd_5351704] using wordTrace_append hprefix tailTrace_5351704
  have hstable : (prefixWord ++ tailWord_5351704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351704).length < 2 ^ (prefixWord ++ tailWord_5351704).sum := by decide
  have hdescent : baseEnd_5351704 < baseStart_5351704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351719 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5351719 : Nat := 118140960795 + 5351719 * 2 ^ 59
def prefixEnd_5351719 : Nat := 4983230072969 + 3 ^ 40 * 5351719 * 2
def baseEnd_5351719 : Nat := 2748004174799252108500399

theorem tailTrace_5351719 : CollatzResearch.WordTrace tailWord_5351719 prefixEnd_5351719 2748004174799252108500399 := by
  unfold tailWord_5351719
  simp only [CollatzResearch.WordTrace]
  refine ⟨195193227698643538682986211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130128818465762359121990807 195193227698643538682986211)
  ·
    refine ⟨292789841547965308024479317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195193227698643538682986211 292789841547965308024479317)
    ·
      refine ⟨3431130955640218453411867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 292789841547965308024479317 3431130955640218453411867)
      ·
        refine ⟨5146696433460327680117801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431130955640218453411867 5146696433460327680117801)
        ·
          refine ⟨3860022325095245760088351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5146696433460327680117801 3860022325095245760088351)
          ·
            refine ⟨5790033487642868640132527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860022325095245760088351 5790033487642868640132527)
            ·
              refine ⟨8685050231464302960198791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790033487642868640132527 8685050231464302960198791)
              ·
                refine ⟨13027575347196454440298187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685050231464302960198791 13027575347196454440298187)
                ·
                  refine ⟨19541363020794681660447281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13027575347196454440298187 19541363020794681660447281)
                  ·
                    refine ⟨14656022265596011245335461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19541363020794681660447281 14656022265596011245335461)
                    ·
                      refine ⟨2748004174799252108500399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14656022265596011245335461 2748004174799252108500399)
                      ·
                        rfl

theorem cell23_5351719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5351719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351719 prefixEnd_5351719 := by exact prefixLift 5351719
  have htrace : WordTrace (prefixWord ++ tailWord_5351719) baseStart_5351719 baseEnd_5351719 := by
    simpa [prefixWord, tailWord_5351719, baseEnd_5351719] using wordTrace_append hprefix tailTrace_5351719
  have hstable : (prefixWord ++ tailWord_5351719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351719).length < 2 ^ (prefixWord ++ tailWord_5351719).sum := by decide
  have hdescent : baseEnd_5351719 < baseStart_5351719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351722 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5351722 : Nat := 118140960795 + 5351722 * 2 ^ 59
def prefixEnd_5351722 : Nat := 4983230072969 + 3 ^ 40 * 5351722 * 2
def baseEnd_5351722 : Nat := 2748005715241215596762885

theorem tailTrace_5351722 : CollatzResearch.WordTrace tailWord_5351722 prefixEnd_5351722 2748005715241215596762885 := by
  unfold tailWord_5351722
  simp only [CollatzResearch.WordTrace]
  refine ⟨48798334279408167548836355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130128891411755113463563613 48798334279408167548836355)
  ·
    refine ⟨73197501419112251323254533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48798334279408167548836355 73197501419112251323254533)
    ·
      refine ⟨13724531516083547123110225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73197501419112251323254533 13724531516083547123110225)
      ·
        refine ⟨10293398637062660342332669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13724531516083547123110225 10293398637062660342332669)
        ·
          refine ⟨3860024488898497628374751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10293398637062660342332669 3860024488898497628374751)
          ·
            refine ⟨5790036733347746442562127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860024488898497628374751 5790036733347746442562127)
            ·
              refine ⟨8685055100021619663843191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790036733347746442562127 8685055100021619663843191)
              ·
                refine ⟨13027582650032429495764787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685055100021619663843191 13027582650032429495764787)
                ·
                  refine ⟨19541373975048644243647181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13027582650032429495764787 19541373975048644243647181)
                  ·
                    refine ⟨7328015240643241591367693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19541373975048644243647181 7328015240643241591367693)
                    ·
                      refine ⟨2748005715241215596762885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328015240643241591367693 2748005715241215596762885)
                      ·
                        rfl

theorem cell23_5351722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5351722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351722 prefixEnd_5351722 := by exact prefixLift 5351722
  have htrace : WordTrace (prefixWord ++ tailWord_5351722) baseStart_5351722 baseEnd_5351722 := by
    simpa [prefixWord, tailWord_5351722, baseEnd_5351722] using wordTrace_append hprefix tailTrace_5351722
  have hstable : (prefixWord ++ tailWord_5351722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351722).length < 2 ^ (prefixWord ++ tailWord_5351722).sum := by decide
  have hdescent : baseEnd_5351722 < baseStart_5351722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351732 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_5351732 : Nat := 118140960795 + 5351732 * 2 ^ 59
def prefixEnd_5351732 : Nat := 4983230072969 + 3 ^ 40 * 5351732 * 2
def baseEnd_5351732 : Nat := 2748010850047760557637839

theorem tailTrace_5351732 : CollatzResearch.WordTrace tailWord_5351732 prefixEnd_5351732 2748010850047760557637839 := by
  unfold tailWord_5351732
  simp only [CollatzResearch.WordTrace]
  refine ⟨97596850923798220951604725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130129134565064294602139633 97596850923798220951604725)
  ·
    refine ⟨9149704774106083214212943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97596850923798220951604725 9149704774106083214212943)
    ·
      refine ⟨13724557161159124821319415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149704774106083214212943 13724557161159124821319415)
      ·
        refine ⟨20586835741738687231979123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13724557161159124821319415 20586835741738687231979123)
        ·
          refine ⟨30880253612608030847968685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20586835741738687231979123 30880253612608030847968685)
          ·
            refine ⟨11580095104728011567988257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30880253612608030847968685 11580095104728011567988257)
            ·
              refine ⟨8685071328546008675991193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11580095104728011567988257 8685071328546008675991193)
              ·
                refine ⟨6513803496409506506993395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8685071328546008675991193 6513803496409506506993395)
                ·
                  refine ⟨9770705244614259760490093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513803496409506506993395 9770705244614259760490093)
                  ·
                    refine ⟨3664014466730347410183785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9770705244614259760490093 3664014466730347410183785)
                    ·
                      refine ⟨2748010850047760557637839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664014466730347410183785 2748010850047760557637839)
                      ·
                        rfl

theorem cell23_5351732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_5351732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351732 prefixEnd_5351732 := by exact prefixLift 5351732
  have htrace : WordTrace (prefixWord ++ tailWord_5351732) baseStart_5351732 baseEnd_5351732 := by
    simpa [prefixWord, tailWord_5351732, baseEnd_5351732] using wordTrace_append hprefix tailTrace_5351732
  have hstable : (prefixWord ++ tailWord_5351732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351732).length < 2 ^ (prefixWord ++ tailWord_5351732).sum := by decide
  have hdescent : baseEnd_5351732 < baseStart_5351732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351754 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_5351754 : Nat := 118140960795 + 5351754 * 2 ^ 59
def prefixEnd_5351754 : Nat := 4983230072969 + 3 ^ 40 * 5351754 * 2
def baseEnd_5351754 : Nat := 2748022146622159471562737

theorem tailTrace_5351754 : CollatzResearch.WordTrace tailWord_5351754 prefixEnd_5351754 2748022146622159471562737 := by
  unfold tailWord_5351754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48798626063379184915127579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130129669502344493107006877 48798626063379184915127579)
  ·
    refine ⟨73197939095068777372691369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48798626063379184915127579 73197939095068777372691369)
    ·
      refine ⟨54898454321301583029518527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73197939095068777372691369 54898454321301583029518527)
      ·
        refine ⟨82347681481952374544277791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54898454321301583029518527 82347681481952374544277791)
        ·
          refine ⟨123521522222928561816416687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82347681481952374544277791 123521522222928561816416687)
          ·
            refine ⟨185282283334392842724625031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123521522222928561816416687 185282283334392842724625031)
            ·
              refine ⟨277923425001589264086937547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185282283334392842724625031 277923425001589264086937547)
              ·
                refine ⟨416885137502383896130406321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277923425001589264086937547 416885137502383896130406321)
                ·
                  refine ⟨312663853126787922097804741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416885137502383896130406321 312663853126787922097804741)
                  ·
                    refine ⟨58624472461272735393338389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312663853126787922097804741 58624472461272735393338389)
                    ·
                      refine ⟨2748022146622159471562737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58624472461272735393338389 2748022146622159471562737)
                      ·
                        rfl

theorem cell23_5351754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_5351754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351754 prefixEnd_5351754 := by exact prefixLift 5351754
  have htrace : WordTrace (prefixWord ++ tailWord_5351754) baseStart_5351754 baseEnd_5351754 := by
    simpa [prefixWord, tailWord_5351754, baseEnd_5351754] using wordTrace_append hprefix tailTrace_5351754
  have hstable : (prefixWord ++ tailWord_5351754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351754).length < 2 ^ (prefixWord ++ tailWord_5351754).sum := by decide
  have hdescent : baseEnd_5351754 < baseStart_5351754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351928 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_5351928 : Nat := 118140960795 + 5351928 * 2 ^ 59
def prefixEnd_5351928 : Nat := 4983230072969 + 3 ^ 40 * 5351928 * 2
def baseEnd_5351928 : Nat := 2748111492256041790786937

theorem tailTrace_5351928 : CollatzResearch.WordTrace tailWord_5351928 prefixEnd_5351928 2748111492256041790786937 := by
  unfold tailWord_5351928
  simp only [CollatzResearch.WordTrace]
  refine ⟨97600425277443183688672219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130133900369924244918229625 97600425277443183688672219)
  ·
    refine ⟨146400637916164775533008329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97600425277443183688672219 146400637916164775533008329)
    ·
      refine ⟨109800478437123581649756247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146400637916164775533008329 109800478437123581649756247)
      ·
        refine ⟨164700717655685372474634371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109800478437123581649756247 164700717655685372474634371)
        ·
          refine ⟨247051076483528058711951557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164700717655685372474634371 247051076483528058711951557)
          ·
            refine ⟨46322076840661511008490917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247051076483528058711951557 46322076840661511008490917)
            ·
              refine ⟨8685389407624033314092047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46322076840661511008490917 8685389407624033314092047)
              ·
                refine ⟨13028084111436049971138071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685389407624033314092047 13028084111436049971138071)
                ·
                  refine ⟨19542126167154074956707107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13028084111436049971138071 19542126167154074956707107)
                  ·
                    refine ⟨29313189250731112435060661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19542126167154074956707107 29313189250731112435060661)
                    ·
                      refine ⟨2748111492256041790786937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29313189250731112435060661 2748111492256041790786937)
                      ·
                        rfl

theorem cell23_5351928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_5351928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351928 prefixEnd_5351928 := by exact prefixLift 5351928
  have htrace : WordTrace (prefixWord ++ tailWord_5351928) baseStart_5351928 baseEnd_5351928 := by
    simpa [prefixWord, tailWord_5351928, baseEnd_5351928] using wordTrace_append hprefix tailTrace_5351928
  have hstable : (prefixWord ++ tailWord_5351928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351928).length < 2 ^ (prefixWord ++ tailWord_5351928).sum := by decide
  have hdescent : baseEnd_5351928 < baseStart_5351928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351948 : List Nat := [2, 2, 1, 2, 4, 2, 2, 8]
def baseStart_5351948 : Nat := 118140960795 + 5351948 * 2 ^ 59
def prefixEnd_5351948 : Nat := 4983230072969 + 3 ^ 40 * 5351948 * 2
def baseEnd_5351948 : Nat := 101782287476634507871735

theorem tailTrace_5351948 : CollatzResearch.WordTrace tailWord_5351948 prefixEnd_5351948 101782287476634507871735 := by
  unfold tailWord_5351948
  simp only [CollatzResearch.WordTrace]
  refine ⟨97600790007406955396536249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130134386676542607195381665 97600790007406955396536249)
  ·
    refine ⟨73200592505555216547402187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97600790007406955396536249 73200592505555216547402187)
    ·
      refine ⟨109800888758332824821103281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73200592505555216547402187 109800888758332824821103281)
      ·
        refine ⟨82350666568749618615827461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109800888758332824821103281 82350666568749618615827461)
        ·
          refine ⟨15440749981640553490467649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82350666568749618615827461 15440749981640553490467649)
          ·
            refine ⟨11580562486230415117850737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15440749981640553490467649 11580562486230415117850737)
            ·
              refine ⟨8685421864672811338388053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11580562486230415117850737 8685421864672811338388053)
              ·
                refine ⟨101782287476634507871735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8685421864672811338388053 101782287476634507871735)
                ·
                  rfl

theorem cell23_5351948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 8].length) (baseStart_5351948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351948 prefixEnd_5351948 := by exact prefixLift 5351948
  have htrace : WordTrace (prefixWord ++ tailWord_5351948) baseStart_5351948 baseEnd_5351948 := by
    simpa [prefixWord, tailWord_5351948, baseEnd_5351948] using wordTrace_append hprefix tailTrace_5351948
  have hstable : (prefixWord ++ tailWord_5351948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351948).length < 2 ^ (prefixWord ++ tailWord_5351948).sum := by decide
  have hdescent : baseEnd_5351948 < baseStart_5351948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351959 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5351959 : Nat := 118140960795 + 5351959 * 2 ^ 59
def prefixEnd_5351959 : Nat := 4983230072969 + 3 ^ 40 * 5351959 * 2
def baseEnd_5351959 : Nat := 2748127410156331169499295

theorem tailTrace_5351959 : CollatzResearch.WordTrace tailWord_5351959 prefixEnd_5351959 2748127410156331169499295 := by
  unfold tailWord_5351959
  simp only [CollatzResearch.WordTrace]
  refine ⟨195201981217774059671722931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130134654145182706447815287 195201981217774059671722931)
  ·
    refine ⟨292802971826661089507584397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195201981217774059671722931 292802971826661089507584397)
    ·
      refine ⟨109801114434997908565344149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292802971826661089507584397 109801114434997908565344149)
      ·
        refine ⟨5146927239140526964000507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109801114434997908565344149 5146927239140526964000507)
        ·
          refine ⟨7720390858710790446000761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146927239140526964000507 7720390858710790446000761)
          ·
            refine ⟨5790293144033092834500571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7720390858710790446000761 5790293144033092834500571)
            ·
              refine ⟨8685439716049639251750857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790293144033092834500571 8685439716049639251750857)
              ·
                refine ⟨6514079787037229438813143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8685439716049639251750857 6514079787037229438813143)
                ·
                  refine ⟨9771119680555844158219715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514079787037229438813143 9771119680555844158219715)
                  ·
                    refine ⟨14656679520833766237329573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9771119680555844158219715 14656679520833766237329573)
                    ·
                      refine ⟨2748127410156331169499295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14656679520833766237329573 2748127410156331169499295)
                      ·
                        rfl

theorem cell23_5351959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5351959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351959 prefixEnd_5351959 := by exact prefixLift 5351959
  have htrace : WordTrace (prefixWord ++ tailWord_5351959) baseStart_5351959 baseEnd_5351959 := by
    simpa [prefixWord, tailWord_5351959, baseEnd_5351959] using wordTrace_append hprefix tailTrace_5351959
  have hstable : (prefixWord ++ tailWord_5351959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351959).length < 2 ^ (prefixWord ++ tailWord_5351959).sum := by decide
  have hdescent : baseEnd_5351959 < baseStart_5351959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351961 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_5351961 : Nat := 118140960795 + 5351961 * 2 ^ 59
def prefixEnd_5351961 : Nat := 4983230072969 + 3 ^ 40 * 5351961 * 2
def baseEnd_5351961 : Nat := 916042812372546720558095

theorem tailTrace_5351961 : CollatzResearch.WordTrace tailWord_5351961 prefixEnd_5351961 916042812372546720558095 := by
  unfold tailWord_5351961
  simp only [CollatzResearch.WordTrace]
  refine ⟨195202054163766814013295737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130134702775844542675530491 195202054163766814013295737)
  ·
    refine ⟨146401540622825110509971803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195202054163766814013295737 146401540622825110509971803)
    ·
      refine ⟨219602310934237665764957705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146401540622825110509971803 219602310934237665764957705)
      ·
        refine ⟨164701733200678249323718279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219602310934237665764957705 164701733200678249323718279)
        ·
          refine ⟨247052599801017373985577419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164701733200678249323718279 247052599801017373985577419)
          ·
            refine ⟨370578899701526060978366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247052599801017373985577419 370578899701526060978366129)
            ·
              refine ⟨277934174776144545733774597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370578899701526060978366129 277934174776144545733774597)
              ·
                refine ⟨52112657770527102325082737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277934174776144545733774597 52112657770527102325082737)
                ·
                  refine ⟨39084493327895326743812053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52112657770527102325082737 39084493327895326743812053)
                  ·
                    refine ⟨916042812372546720558095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39084493327895326743812053 916042812372546720558095)
                    ·
                      rfl

theorem cell23_5351961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_5351961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351961 prefixEnd_5351961 := by exact prefixLift 5351961
  have htrace : WordTrace (prefixWord ++ tailWord_5351961) baseStart_5351961 baseEnd_5351961 := by
    simpa [prefixWord, tailWord_5351961, baseEnd_5351961] using wordTrace_append hprefix tailTrace_5351961
  have hstable : (prefixWord ++ tailWord_5351961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351961).length < 2 ^ (prefixWord ++ tailWord_5351961).sum := by decide
  have hdescent : baseEnd_5351961 < baseStart_5351961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351972 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5351972 : Nat := 118140960795 + 5351972 * 2 ^ 59
def prefixEnd_5351972 : Nat := 4983230072969 + 3 ^ 40 * 5351972 * 2
def baseEnd_5351972 : Nat := 2748134085404839618636735

theorem tailTrace_5351972 : CollatzResearch.WordTrace tailWord_5351972 prefixEnd_5351972 2748134085404839618636735 := by
  unfold tailWord_5351972
  simp only [CollatzResearch.WordTrace]
  refine ⟨97601227683363481445973085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130134970244484641927964113 97601227683363481445973085)
  ·
    refine ⟨36600460381261305542239907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97601227683363481445973085 36600460381261305542239907)
    ·
      refine ⟨54900690571891958313359861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36600460381261305542239907 54900690571891958313359861)
      ·
        refine ⟨5146939741114871091877487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54900690571891958313359861 5146939741114871091877487)
        ·
          refine ⟨7720409611672306637816231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146939741114871091877487 7720409611672306637816231)
          ·
            refine ⟨11580614417508459956724347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720409611672306637816231 11580614417508459956724347)
            ·
              refine ⟨17370921626262689935086521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11580614417508459956724347 17370921626262689935086521)
              ·
                refine ⟨13028191219697017451314891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17370921626262689935086521 13028191219697017451314891)
                ·
                  refine ⟨19542286829545526176972337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13028191219697017451314891 19542286829545526176972337)
                  ·
                    refine ⟨14656715122159144632729253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19542286829545526176972337 14656715122159144632729253)
                    ·
                      refine ⟨2748134085404839618636735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14656715122159144632729253 2748134085404839618636735)
                      ·
                        rfl

theorem cell23_5351972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5351972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351972 prefixEnd_5351972 := by exact prefixLift 5351972
  have htrace : WordTrace (prefixWord ++ tailWord_5351972) baseStart_5351972 baseEnd_5351972 := by
    simpa [prefixWord, tailWord_5351972, baseEnd_5351972] using wordTrace_append hprefix tailTrace_5351972
  have hstable : (prefixWord ++ tailWord_5351972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351972).length < 2 ^ (prefixWord ++ tailWord_5351972).sum := by decide
  have hdescent : baseEnd_5351972 < baseStart_5351972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5351992 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_5351992 : Nat := 118140960795 + 5351992 * 2 ^ 59
def prefixEnd_5351992 : Nat := 4983230072969 + 3 ^ 40 * 5351992 * 2
def baseEnd_5351992 : Nat := 2748144355017929540386643

theorem tailTrace_5351992 : CollatzResearch.WordTrace tailWord_5351992 prefixEnd_5351992 2748144355017929540386643 := by
  unfold tailWord_5351992
  simp only [CollatzResearch.WordTrace]
  refine ⟨97601592413327253153837115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130135456551103004205116153 97601592413327253153837115)
  ·
    refine ⟨146402388619990879730755673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97601592413327253153837115 146402388619990879730755673)
    ·
      refine ⟨109801791464993159798066755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146402388619990879730755673 109801791464993159798066755)
      ·
        refine ⟨164702687197489739697100133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109801791464993159798066755 164702687197489739697100133)
        ·
          refine ⟨30881753849529326193206275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164702687197489739697100133 30881753849529326193206275)
          ·
            refine ⟨46322630774293989289809413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30881753849529326193206275 46322630774293989289809413)
            ·
              refine ⟨8685493270180122991839265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46322630774293989289809413 8685493270180122991839265)
              ·
                refine ⟨6514119952635092243879449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8685493270180122991839265 6514119952635092243879449)
                ·
                  refine ⟨4885589964476319182909587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514119952635092243879449 4885589964476319182909587)
                  ·
                    refine ⟨7328384946714478774364381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885589964476319182909587 7328384946714478774364381)
                    ·
                      refine ⟨2748144355017929540386643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328384946714478774364381 2748144355017929540386643)
                      ·
                        rfl

theorem cell23_5351992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_5351992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5351992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5351992 prefixEnd_5351992 := by exact prefixLift 5351992
  have htrace : WordTrace (prefixWord ++ tailWord_5351992) baseStart_5351992 baseEnd_5351992 := by
    simpa [prefixWord, tailWord_5351992, baseEnd_5351992] using wordTrace_append hprefix tailTrace_5351992
  have hstable : (prefixWord ++ tailWord_5351992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5351992).length < 2 ^ (prefixWord ++ tailWord_5351992).sum := by decide
  have hdescent : baseEnd_5351992 < baseStart_5351992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5351992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352015 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 1, 4, 2]
def baseStart_5352015 : Nat := 118140960795 + 5352015 * 2 ^ 59
def prefixEnd_5352015 : Nat := 4983230072969 + 3 ^ 40 * 5352015 * 2
def baseEnd_5352015 : Nat := 2748156165072982950399037

theorem tailTrace_5352015 : CollatzResearch.WordTrace tailWord_5352015 prefixEnd_5352015 2748156165072982950399037 := by
  unfold tailWord_5352015
  simp only [CollatzResearch.WordTrace]
  refine ⟨195204023705571181235761499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130136015803714120823840999 195204023705571181235761499)
  ·
    refine ⟨292806035558356771853642249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195204023705571181235761499 292806035558356771853642249)
    ·
      refine ⟨219604526668767578890231687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292806035558356771853642249 219604526668767578890231687)
      ·
        refine ⟨329406790003151368335347531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219604526668767578890231687 329406790003151368335347531)
        ·
          refine ⟨494110185004727052503021297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329406790003151368335347531 494110185004727052503021297)
          ·
            refine ⟨370582638753545289377265973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494110185004727052503021297 370582638753545289377265973)
            ·
              refine ⟨34742122383144870879118685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370582638753545289377265973 34742122383144870879118685)
              ·
                refine ⟨13028295893679326579669507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34742122383144870879118685 13028295893679326579669507)
                ·
                  refine ⟨19542443840518989869504261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13028295893679326579669507 19542443840518989869504261)
                  ·
                    refine ⟨3664208220097310600532049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19542443840518989869504261 3664208220097310600532049)
                    ·
                      refine ⟨2748156165072982950399037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664208220097310600532049 2748156165072982950399037)
                      ·
                        rfl

theorem cell23_5352015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4, 2].length) (baseStart_5352015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352015 prefixEnd_5352015 := by exact prefixLift 5352015
  have htrace : WordTrace (prefixWord ++ tailWord_5352015) baseStart_5352015 baseEnd_5352015 := by
    simpa [prefixWord, tailWord_5352015, baseEnd_5352015] using wordTrace_append hprefix tailTrace_5352015
  have hstable : (prefixWord ++ tailWord_5352015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352015).length < 2 ^ (prefixWord ++ tailWord_5352015).sum := by decide
  have hdescent : baseEnd_5352015 < baseStart_5352015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352030 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5352030 : Nat := 118140960795 + 5352030 * 2 ^ 59
def prefixEnd_5352030 : Nat := 4983230072969 + 3 ^ 40 * 5352030 * 2
def baseEnd_5352030 : Nat := 2748163867282800391711469

theorem tailTrace_5352030 : CollatzResearch.WordTrace tailWord_5352030 prefixEnd_5352030 2748163867282800391711469 := by
  unfold tailWord_5352030
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400571350064604849694693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130136380533677892531705029 24400571350064604849694693)
  ·
    refine ⟨4575107128137113409317755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24400571350064604849694693 4575107128137113409317755)
    ·
      refine ⟨6862660692205670113976633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4575107128137113409317755 6862660692205670113976633)
      ·
        refine ⟨5146995519154252585482475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862660692205670113976633 5146995519154252585482475)
        ·
          refine ⟨7720493278731378878223713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146995519154252585482475 7720493278731378878223713)
          ·
            refine ⟨5790369959048534158667785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7720493278731378878223713 5790369959048534158667785)
            ·
              refine ⟨4342777469286400619000839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5790369959048534158667785 4342777469286400619000839)
              ·
                refine ⟨6514166203929600928501259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342777469286400619000839 6514166203929600928501259)
                ·
                  refine ⟨9771249305894401392751889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514166203929600928501259 9771249305894401392751889)
                  ·
                    refine ⟨7328436979420801044563917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9771249305894401392751889 7328436979420801044563917)
                    ·
                      refine ⟨2748163867282800391711469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328436979420801044563917 2748163867282800391711469)
                      ·
                        rfl

theorem cell23_5352030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5352030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352030 prefixEnd_5352030 := by exact prefixLift 5352030
  have htrace : WordTrace (prefixWord ++ tailWord_5352030) baseStart_5352030 baseEnd_5352030 := by
    simpa [prefixWord, tailWord_5352030, baseEnd_5352030] using wordTrace_append hprefix tailTrace_5352030
  have hstable : (prefixWord ++ tailWord_5352030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352030).length < 2 ^ (prefixWord ++ tailWord_5352030).sum := by decide
  have hdescent : baseEnd_5352030 < baseStart_5352030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352045 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5352045 : Nat := 118140960795 + 5352045 * 2 ^ 59
def prefixEnd_5352045 : Nat := 4983230072969 + 3 ^ 40 * 5352045 * 2
def baseEnd_5352045 : Nat := 2748171569492617833023899

theorem tailTrace_5352045 : CollatzResearch.WordTrace tailWord_5352045 prefixEnd_5352045 2748171569492617833023899 := by
  unfold tailWord_5352045
  simp only [CollatzResearch.WordTrace]
  refine ⟨195205117895462496359353589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130136745263641664239569059 195205117895462496359353589)
  ·
    refine ⟨18300479802699609033689399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195205117895462496359353589 18300479802699609033689399)
    ·
      refine ⟨27450719704049413550534099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18300479802699609033689399 27450719704049413550534099)
      ·
        refine ⟨41176079556074120325801149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27450719704049413550534099 41176079556074120325801149)
        ·
          refine ⟨15441029833527795122175431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41176079556074120325801149 15441029833527795122175431)
          ·
            refine ⟨23161544750291692683263147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15441029833527795122175431 23161544750291692683263147)
            ·
              refine ⟨34742317125437539024894721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23161544750291692683263147 34742317125437539024894721)
              ·
                refine ⟨26056737844078154268671041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34742317125437539024894721 26056737844078154268671041)
                ·
                  refine ⟨19542553383058615701503281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26056737844078154268671041 19542553383058615701503281)
                  ·
                    refine ⟨14656915037293961776127461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19542553383058615701503281 14656915037293961776127461)
                    ·
                      refine ⟨2748171569492617833023899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14656915037293961776127461 2748171569492617833023899)
                      ·
                        rfl

theorem cell23_5352045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5352045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352045 prefixEnd_5352045 := by exact prefixLift 5352045
  have htrace : WordTrace (prefixWord ++ tailWord_5352045) baseStart_5352045 baseEnd_5352045 := by
    simpa [prefixWord, tailWord_5352045, baseEnd_5352045] using wordTrace_append hprefix tailTrace_5352045
  have hstable : (prefixWord ++ tailWord_5352045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352045).length < 2 ^ (prefixWord ++ tailWord_5352045).sum := by decide
  have hdescent : baseEnd_5352045 < baseStart_5352045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352055 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 5]
def baseStart_5352055 : Nat := 118140960795 + 5352055 * 2 ^ 59
def prefixEnd_5352055 : Nat := 4983230072969 + 3 ^ 40 * 5352055 * 2
def baseEnd_5352055 : Nat := 305352967144351421544317

theorem tailTrace_5352055 : CollatzResearch.WordTrace tailWord_5352055 prefixEnd_5352055 305352967144351421544317 := by
  unfold tailWord_5352055
  simp only [CollatzResearch.WordTrace]
  refine ⟨195205482625426268067217619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130136988416950845378145079 195205482625426268067217619)
  ·
    refine ⟨292808223938139402100826429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195205482625426268067217619 292808223938139402100826429)
    ·
      refine ⟨109803083976802275787809911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292808223938139402100826429 109803083976802275787809911)
      ·
        refine ⟨164704625965203413681714867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109803083976802275787809911 164704625965203413681714867)
        ·
          refine ⟨247056938947805120522572301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164704625965203413681714867 247056938947805120522572301)
          ·
            refine ⟨92646352105426920195964613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247056938947805120522572301 92646352105426920195964613)
            ·
              refine ⟨17371191019767547536743365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92646352105426920195964613 17371191019767547536743365)
              ·
                refine ⟨3257098316206415163139381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17371191019767547536743365 3257098316206415163139381)
                ·
                  refine ⟨305352967144351421544317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3257098316206415163139381 305352967144351421544317)
                  ·
                    rfl

theorem cell23_5352055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 5].length) (baseStart_5352055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352055 prefixEnd_5352055 := by exact prefixLift 5352055
  have htrace : WordTrace (prefixWord ++ tailWord_5352055) baseStart_5352055 baseEnd_5352055 := by
    simpa [prefixWord, tailWord_5352055, baseEnd_5352055] using wordTrace_append hprefix tailTrace_5352055
  have hstable : (prefixWord ++ tailWord_5352055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352055).length < 2 ^ (prefixWord ++ tailWord_5352055).sum := by decide
  have hdescent : baseEnd_5352055 < baseStart_5352055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352065 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_5352065 : Nat := 118140960795 + 5352065 * 2 ^ 59
def prefixEnd_5352065 : Nat := 4983230072969 + 3 ^ 40 * 5352065 * 2
def baseEnd_5352065 : Nat := 2748181839105707754773807

theorem tailTrace_5352065 : CollatzResearch.WordTrace tailWord_5352065 prefixEnd_5352065 2748181839105707754773807 := by
  unfold tailWord_5352065
  simp only [CollatzResearch.WordTrace]
  refine ⟨195205847355390039775081649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130137231570260026516721099 195205847355390039775081649)
  ·
    refine ⟨146404385516542529831311237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195205847355390039775081649 146404385516542529831311237)
    ·
      refine ⟨27450822284351724343370857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146404385516542529831311237 27450822284351724343370857)
      ·
        refine ⟨20588116713263793257528143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27450822284351724343370857 20588116713263793257528143)
        ·
          refine ⟨30882175069895689886292215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20588116713263793257528143 30882175069895689886292215)
          ·
            refine ⟨46323262604843534829438323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30882175069895689886292215 46323262604843534829438323)
            ·
              refine ⟨69484893907265302244157485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46323262604843534829438323 69484893907265302244157485)
              ·
                refine ⟨26056835215224488341559057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69484893907265302244157485 26056835215224488341559057)
                ·
                  refine ⟨19542626411418366256169293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26056835215224488341559057 19542626411418366256169293)
                  ·
                    refine ⟨7328484904281887346063485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19542626411418366256169293 7328484904281887346063485)
                    ·
                      refine ⟨2748181839105707754773807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328484904281887346063485 2748181839105707754773807)
                      ·
                        rfl

theorem cell23_5352065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_5352065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352065 prefixEnd_5352065 := by exact prefixLift 5352065
  have htrace : WordTrace (prefixWord ++ tailWord_5352065) baseStart_5352065 baseEnd_5352065 := by
    simpa [prefixWord, tailWord_5352065, baseEnd_5352065] using wordTrace_append hprefix tailTrace_5352065
  have hstable : (prefixWord ++ tailWord_5352065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352065).length < 2 ^ (prefixWord ++ tailWord_5352065).sum := by decide
  have hdescent : baseEnd_5352065 < baseStart_5352065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352106 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_5352106 : Nat := 118140960795 + 5352106 * 2 ^ 59
def prefixEnd_5352106 : Nat := 4983230072969 + 3 ^ 40 * 5352106 * 2
def baseEnd_5352106 : Nat := 305355876868060232706791

theorem tailTrace_5352106 : CollatzResearch.WordTrace tailWord_5352106 prefixEnd_5352106 305355876868060232706791 := by
  unfold tailWord_5352106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48801835687060375944331043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130138228498827669184882781 48801835687060375944331043)
  ·
    refine ⟨73202753530590563916496565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48801835687060375944331043 73202753530590563916496565)
    ·
      refine ⟨6862758143492865367171553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73202753530590563916496565 6862758143492865367171553)
      ·
        refine ⟨5147068607619649025378665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862758143492865367171553 5147068607619649025378665)
        ·
          refine ⟨3860301455714736769033999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147068607619649025378665 3860301455714736769033999)
          ·
            refine ⟨5790452183572105153550999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860301455714736769033999 5790452183572105153550999)
            ·
              refine ⟨8685678275358157730326499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790452183572105153550999 8685678275358157730326499)
              ·
                refine ⟨13028517413037236595489749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685678275358157730326499 13028517413037236595489749)
                ·
                  refine ⟨305355876868060232706791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13028517413037236595489749 305355876868060232706791)
                  ·
                    rfl

theorem cell23_5352106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_5352106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352106 prefixEnd_5352106 := by exact prefixLift 5352106
  have htrace : WordTrace (prefixWord ++ tailWord_5352106) baseStart_5352106 baseEnd_5352106 := by
    simpa [prefixWord, tailWord_5352106, baseEnd_5352106] using wordTrace_append hprefix tailTrace_5352106
  have hstable : (prefixWord ++ tailWord_5352106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352106).length < 2 ^ (prefixWord ++ tailWord_5352106).sum := by decide
  have hdescent : baseEnd_5352106 < baseStart_5352106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352142 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_5352142 : Nat := 118140960795 + 5352142 * 2 ^ 59
def prefixEnd_5352142 : Nat := 4983230072969 + 3 ^ 40 * 5352142 * 2
def baseEnd_5352142 : Nat := 2748221377116103953510953

theorem tailTrace_5352142 : CollatzResearch.WordTrace tailWord_5352142 prefixEnd_5352142 2748221377116103953510953 := by
  unfold tailWord_5352142
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401081972013885240704335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130139103850740721283756453 24401081972013885240704335)
  ·
    refine ⟨36601622958020827861056503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24401081972013885240704335 36601622958020827861056503)
    ·
      refine ⟨54902434437031241791584755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36601622958020827861056503 54902434437031241791584755)
      ·
        refine ⟨82353651655546862687377133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54902434437031241791584755 82353651655546862687377133)
        ·
          refine ⟨30882619370830073507766425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82353651655546862687377133 30882619370830073507766425)
          ·
            refine ⟨23161964528122555130824819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30882619370830073507766425 23161964528122555130824819)
            ·
              refine ⟨34742946792183832696237229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23161964528122555130824819 34742946792183832696237229)
              ·
                refine ⟨13028605047068937261088961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34742946792183832696237229 13028605047068937261088961)
                ·
                  refine ⟨9771453785301702945816721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13028605047068937261088961 9771453785301702945816721)
                  ·
                    refine ⟨7328590338976277209362541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9771453785301702945816721 7328590338976277209362541)
                    ·
                      refine ⟨2748221377116103953510953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328590338976277209362541 2748221377116103953510953)
                      ·
                        rfl

theorem cell23_5352142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_5352142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352142 prefixEnd_5352142 := by exact prefixLift 5352142
  have htrace : WordTrace (prefixWord ++ tailWord_5352142) baseStart_5352142 baseEnd_5352142 := by
    simpa [prefixWord, tailWord_5352142, baseEnd_5352142] using wordTrace_append hprefix tailTrace_5352142
  have hstable : (prefixWord ++ tailWord_5352142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352142).length < 2 ^ (prefixWord ++ tailWord_5352142).sum := by decide
  have hdescent : baseEnd_5352142 < baseStart_5352142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352172 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_5352172 : Nat := 118140960795 + 5352172 * 2 ^ 59
def prefixEnd_5352172 : Nat := 4983230072969 + 3 ^ 40 * 5352172 * 2
def baseEnd_5352172 : Nat := 2748236781535738836135815

theorem tailTrace_5352172 : CollatzResearch.WordTrace tailWord_5352172 prefixEnd_5352172 2748236781535738836135815 := by
  unfold tailWord_5352172
  simp only [CollatzResearch.WordTrace]
  refine ⟨97604874983001198524613385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130139833310668264699484513 97604874983001198524613385)
  ·
    refine ⟨73203656237250898893460039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97604874983001198524613385 73203656237250898893460039)
    ·
      refine ⟨109805484355876348340190059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73203656237250898893460039 109805484355876348340190059)
      ·
        refine ⟨164708226533814522510285089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109805484355876348340190059 164708226533814522510285089)
        ·
          refine ⟨123531169900360891882713817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164708226533814522510285089 123531169900360891882713817)
          ·
            refine ⟨92648377425270668912035363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123531169900360891882713817 92648377425270668912035363)
            ·
              refine ⟨138972566137906003368053045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92648377425270668912035363 138972566137906003368053045)
              ·
                refine ⟨13028678075428687815754973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138972566137906003368053045 13028678075428687815754973)
                ·
                  refine ⟨4885754278285757930908115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13028678075428687815754973 4885754278285757930908115)
                  ·
                    refine ⟨7328631417428636896362173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885754278285757930908115 7328631417428636896362173)
                    ·
                      refine ⟨2748236781535738836135815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328631417428636896362173 2748236781535738836135815)
                      ·
                        rfl

theorem cell23_5352172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_5352172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352172 prefixEnd_5352172 := by exact prefixLift 5352172
  have htrace : WordTrace (prefixWord ++ tailWord_5352172) baseStart_5352172 baseEnd_5352172 := by
    simpa [prefixWord, tailWord_5352172, baseEnd_5352172] using wordTrace_append hprefix tailTrace_5352172
  have hstable : (prefixWord ++ tailWord_5352172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352172).length < 2 ^ (prefixWord ++ tailWord_5352172).sum := by decide
  have hdescent : baseEnd_5352172 < baseStart_5352172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352175 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 3, 5]
def baseStart_5352175 : Nat := 118140960795 + 5352175 * 2 ^ 59
def prefixEnd_5352175 : Nat := 4983230072969 + 3 ^ 40 * 5352175 * 2
def baseEnd_5352175 : Nat := 916079440659234108132767

theorem tailTrace_5352175 : CollatzResearch.WordTrace tailWord_5352175 prefixEnd_5352175 916079440659234108132767 := by
  unfold tailWord_5352175
  simp only [CollatzResearch.WordTrace]
  refine ⟨195209859384991528561585979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130139906256661019041057319 195209859384991528561585979)
  ·
    refine ⟨292814789077487292842378969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195209859384991528561585979 292814789077487292842378969)
    ·
      refine ⟨219611091808115469631784227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292814789077487292842378969 219611091808115469631784227)
      ·
        refine ⟨329416637712173204447676341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219611091808115469631784227 329416637712173204447676341)
        ·
          refine ⟨30882809785516237916969657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329416637712173204447676341 30882809785516237916969657)
          ·
            refine ⟨23162107339137178437727243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30882809785516237916969657 23162107339137178437727243)
            ·
              refine ⟨34743161008705767656590865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23162107339137178437727243 34743161008705767656590865)
              ·
                refine ⟨26057370756529325742443149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34743161008705767656590865 26057370756529325742443149)
                ·
                  refine ⟨9771514033698497153416181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26057370756529325742443149 9771514033698497153416181)
                  ·
                    refine ⟨916079440659234108132767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9771514033698497153416181 916079440659234108132767)
                    ·
                      rfl

theorem cell23_5352175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_5352175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352175 prefixEnd_5352175 := by exact prefixLift 5352175
  have htrace : WordTrace (prefixWord ++ tailWord_5352175) baseStart_5352175 baseEnd_5352175 := by
    simpa [prefixWord, tailWord_5352175, baseEnd_5352175] using wordTrace_append hprefix tailTrace_5352175
  have hstable : (prefixWord ++ tailWord_5352175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352175).length < 2 ^ (prefixWord ++ tailWord_5352175).sum := by decide
  have hdescent : baseEnd_5352175 < baseStart_5352175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352199 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5352199 : Nat := 118140960795 + 5352199 * 2 ^ 59
def prefixEnd_5352199 : Nat := 4983230072969 + 3 ^ 40 * 5352199 * 2
def baseEnd_5352199 : Nat := 2748250645513410230498191

theorem tailTrace_5352199 : CollatzResearch.WordTrace tailWord_5352199 prefixEnd_5352199 2748250645513410230498191 := by
  unfold tailWord_5352199
  simp only [CollatzResearch.WordTrace]
  refine ⟨195210734736904580660459651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130140489824603053773639767 195210734736904580660459651)
  ·
    refine ⟨292816102105356870990689477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195210734736904580660459651 292816102105356870990689477)
    ·
      refine ⟨54903019144754413310754277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292816102105356870990689477 54903019144754413310754277)
      ·
        refine ⟨10294316089641452495766427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54903019144754413310754277 10294316089641452495766427)
        ·
          refine ⟨15441474134462178743649641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294316089641452495766427 15441474134462178743649641)
          ·
            refine ⟨11581105600846634057737231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15441474134462178743649641 11581105600846634057737231)
            ·
              refine ⟨17371658401269951086605847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11581105600846634057737231 17371658401269951086605847)
              ·
                refine ⟨26057487601904926629908771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17371658401269951086605847 26057487601904926629908771)
                ·
                  refine ⟨39086231402857389944863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26057487601904926629908771 39086231402857389944863157)
                  ·
                    refine ⟨3664334194017880307330921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39086231402857389944863157 3664334194017880307330921)
                    ·
                      refine ⟨2748250645513410230498191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664334194017880307330921 2748250645513410230498191)
                      ·
                        rfl

theorem cell23_5352199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5352199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352199 prefixEnd_5352199 := by exact prefixLift 5352199
  have htrace : WordTrace (prefixWord ++ tailWord_5352199) baseStart_5352199 baseEnd_5352199 := by
    simpa [prefixWord, tailWord_5352199, baseEnd_5352199] using wordTrace_append hprefix tailTrace_5352199
  have hstable : (prefixWord ++ tailWord_5352199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352199).length < 2 ^ (prefixWord ++ tailWord_5352199).sum := by decide
  have hdescent : baseEnd_5352199 < baseStart_5352199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352225 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5352225 : Nat := 118140960795 + 5352225 * 2 ^ 59
def prefixEnd_5352225 : Nat := 4983230072969 + 3 ^ 40 * 5352225 * 2
def baseEnd_5352225 : Nat := 2748263996010427128773071

theorem tailTrace_5352225 : CollatzResearch.WordTrace tailWord_5352225 prefixEnd_5352225 2748263996010427128773071 := by
  unfold tailWord_5352225
  simp only [CollatzResearch.WordTrace]
  refine ⟨195211683034810387100906129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130141122023206924733937419 195211683034810387100906129)
  ·
    refine ⟨146408762276107790325679597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195211683034810387100906129 146408762276107790325679597)
    ·
      refine ⟨54903285853540421372129849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146408762276107790325679597 54903285853540421372129849)
      ·
        refine ⟨41177464390155316029097387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54903285853540421372129849 41177464390155316029097387)
        ·
          refine ⟨61766196585232974043646081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41177464390155316029097387 61766196585232974043646081)
          ·
            refine ⟨46324647438924730532734561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61766196585232974043646081 46324647438924730532734561)
            ·
              refine ⟨34743485579193547899550921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46324647438924730532734561 34743485579193547899550921)
              ·
                refine ⟨26057614184395160924663191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34743485579193547899550921 26057614184395160924663191)
                ·
                  refine ⟨39086421276592741386994787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26057614184395160924663191 39086421276592741386994787)
                  ·
                    refine ⟨58629631914889112080492181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39086421276592741386994787 58629631914889112080492181)
                    ·
                      refine ⟨2748263996010427128773071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58629631914889112080492181 2748263996010427128773071)
                      ·
                        rfl

theorem cell23_5352225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5352225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352225 prefixEnd_5352225 := by exact prefixLift 5352225
  have htrace : WordTrace (prefixWord ++ tailWord_5352225) baseStart_5352225 baseEnd_5352225 := by
    simpa [prefixWord, tailWord_5352225, baseEnd_5352225] using wordTrace_append hprefix tailTrace_5352225
  have hstable : (prefixWord ++ tailWord_5352225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352225).length < 2 ^ (prefixWord ++ tailWord_5352225).sum := by decide
  have hdescent : baseEnd_5352225 < baseStart_5352225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352232 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5352232 : Nat := 118140960795 + 5352232 * 2 ^ 59
def prefixEnd_5352232 : Nat := 4983230072969 + 3 ^ 40 * 5352232 * 2
def baseEnd_5352232 : Nat := 2748267590375008601385539

theorem tailTrace_5352232 : CollatzResearch.WordTrace tailWord_5352232 prefixEnd_5352232 2748267590375008601385539 := by
  unfold tailWord_5352232
  simp only [CollatzResearch.WordTrace]
  refine ⟨97605969172892513648205475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130141292230523351530940633 97605969172892513648205475)
  ·
    refine ⟨146408953759338770472308213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97605969172892513648205475 146408953759338770472308213)
    ·
      refine ⟨13725839414938009731778895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146408953759338770472308213 13725839414938009731778895)
      ·
        refine ⟨20588759122407014597668343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725839414938009731778895 20588759122407014597668343)
        ·
          refine ⟨30883138683610521896502515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20588759122407014597668343 30883138683610521896502515)
          ·
            refine ⟨46324708025415782844753773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30883138683610521896502515 46324708025415782844753773)
            ·
              refine ⟨17371765509530918566782665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46324708025415782844753773 17371765509530918566782665)
              ·
                refine ⟨13028824132148188925086999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17371765509530918566782665 13028824132148188925086999)
                ·
                  refine ⟨19543236198222283387630499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13028824132148188925086999 19543236198222283387630499)
                  ·
                    refine ⟨29314854297333425081445749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19543236198222283387630499 29314854297333425081445749)
                    ·
                      refine ⟨2748267590375008601385539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29314854297333425081445749 2748267590375008601385539)
                      ·
                        rfl

theorem cell23_5352232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5352232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352232 prefixEnd_5352232 := by exact prefixLift 5352232
  have htrace : WordTrace (prefixWord ++ tailWord_5352232) baseStart_5352232 baseEnd_5352232 := by
    simpa [prefixWord, tailWord_5352232, baseEnd_5352232] using wordTrace_append hprefix tailTrace_5352232
  have hstable : (prefixWord ++ tailWord_5352232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352232).length < 2 ^ (prefixWord ++ tailWord_5352232).sum := by decide
  have hdescent : baseEnd_5352232 < baseStart_5352232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352257 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5352257 : Nat := 118140960795 + 5352257 * 2 ^ 59
def prefixEnd_5352257 : Nat := 4983230072969 + 3 ^ 40 * 5352257 * 2
def baseEnd_5352257 : Nat := 2748280427391371003572925

theorem tailTrace_5352257 : CollatzResearch.WordTrace tailWord_5352257 prefixEnd_5352257 2748280427391371003572925 := by
  unfold tailWord_5352257
  simp only [CollatzResearch.WordTrace]
  refine ⟨195212850170694456566071025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130141900113796304377380683 195212850170694456566071025)
  ·
    refine ⟨146409637628020842424553269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195212850170694456566071025 146409637628020842424553269)
    ·
      refine ⟨13725903527626953977301869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146409637628020842424553269 13725903527626953977301869)
      ·
        refine ⟨5147213822860107741488201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13725903527626953977301869 5147213822860107741488201)
        ·
          refine ⟨3860410367145080806116151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147213822860107741488201 3860410367145080806116151)
          ·
            refine ⟨5790615550717621209174227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860410367145080806116151 5790615550717621209174227)
            ·
              refine ⟨8685923326076431813761341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790615550717621209174227 8685923326076431813761341)
              ·
                refine ⟨3257221247278661930160503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8685923326076431813761341 3257221247278661930160503)
                ·
                  refine ⟨4885831870917992895240755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257221247278661930160503 4885831870917992895240755)
                  ·
                    refine ⟨7328747806376989342861133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885831870917992895240755 7328747806376989342861133)
                    ·
                      refine ⟨2748280427391371003572925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328747806376989342861133 2748280427391371003572925)
                      ·
                        rfl

theorem cell23_5352257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5352257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352257 prefixEnd_5352257 := by exact prefixLift 5352257
  have htrace : WordTrace (prefixWord ++ tailWord_5352257) baseStart_5352257 baseEnd_5352257 := by
    simpa [prefixWord, tailWord_5352257, baseEnd_5352257] using wordTrace_append hprefix tailTrace_5352257
  have hstable : (prefixWord ++ tailWord_5352257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352257).length < 2 ^ (prefixWord ++ tailWord_5352257).sum := by decide
  have hdescent : baseEnd_5352257 < baseStart_5352257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352269 : List Nat := [1, 6, 1, 2, 2, 2, 9]
def baseStart_5352269 : Nat := 118140960795 + 5352269 * 2 ^ 59
def prefixEnd_5352269 : Nat := 4983230072969 + 3 ^ 40 * 5352269 * 2
def baseEnd_5352269 : Nat := 33929464063694135266949

theorem tailTrace_5352269 : CollatzResearch.WordTrace tailWord_5352269 prefixEnd_5352269 33929464063694135266949 := by
  unfold tailWord_5352269
  simp only [CollatzResearch.WordTrace]
  refine ⟨195213287846650982615507861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130142191897767321743671907 195213287846650982615507861)
  ·
    refine ⟨9150622867811764810101931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195213287846650982615507861 9150622867811764810101931)
    ·
      refine ⟨13725934301717647215152897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150622867811764810101931 13725934301717647215152897)
      ·
        refine ⟨10294450726288235411364673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13725934301717647215152897 10294450726288235411364673)
        ·
          refine ⟨7720838044716176558523505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10294450726288235411364673 7720838044716176558523505)
          ·
            refine ⟨5790628533537132418892629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7720838044716176558523505 5790628533537132418892629)
            ·
              refine ⟨33929464063694135266949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5790628533537132418892629 33929464063694135266949)
              ·
                rfl

theorem cell23_5352269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 9].length) (baseStart_5352269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352269 prefixEnd_5352269 := by exact prefixLift 5352269
  have htrace : WordTrace (prefixWord ++ tailWord_5352269) baseStart_5352269 baseEnd_5352269 := by
    simpa [prefixWord, tailWord_5352269, baseEnd_5352269] using wordTrace_append hprefix tailTrace_5352269
  have hstable : (prefixWord ++ tailWord_5352269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352269).length < 2 ^ (prefixWord ++ tailWord_5352269).sum := by decide
  have hdescent : baseEnd_5352269 < baseStart_5352269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352279 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_5352279 : Nat := 118140960795 + 5352279 * 2 ^ 59
def prefixEnd_5352279 : Nat := 4983230072969 + 3 ^ 40 * 5352279 * 2
def baseEnd_5352279 : Nat := 2748291723965769917497823

theorem tailTrace_5352279 : CollatzResearch.WordTrace tailWord_5352279 prefixEnd_5352279 2748291723965769917497823 := by
  unfold tailWord_5352279
  simp only [CollatzResearch.WordTrace]
  refine ⟨195213652576614754323371891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130142435051076502882247927 195213652576614754323371891)
  ·
    refine ⟨292820478864922131485057837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195213652576614754323371891 292820478864922131485057837)
    ·
      refine ⟨109807679574345799306896689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292820478864922131485057837 109807679574345799306896689)
      ·
        refine ⟨82355759680759349480172517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109807679574345799306896689 82355759680759349480172517)
        ·
          refine ⟨15441704940142378027532347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82355759680759349480172517 15441704940142378027532347)
          ·
            refine ⟨23162557410213567041298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15441704940142378027532347 23162557410213567041298521)
            ·
              refine ⟨17371918057660175280973891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23162557410213567041298521 17371918057660175280973891)
              ·
                refine ⟨26057877086490262921460837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17371918057660175280973891 26057877086490262921460837)
                ·
                  refine ⟨4885851953716924297773907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26057877086490262921460837 4885851953716924297773907)
                  ·
                    refine ⟨7328777930575386446660861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885851953716924297773907 7328777930575386446660861)
                    ·
                      refine ⟨2748291723965769917497823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328777930575386446660861 2748291723965769917497823)
                      ·
                        rfl

theorem cell23_5352279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_5352279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352279 prefixEnd_5352279 := by exact prefixLift 5352279
  have htrace : WordTrace (prefixWord ++ tailWord_5352279) baseStart_5352279 baseEnd_5352279 := by
    simpa [prefixWord, tailWord_5352279, baseEnd_5352279] using wordTrace_append hprefix tailTrace_5352279
  have hstable : (prefixWord ++ tailWord_5352279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352279).length < 2 ^ (prefixWord ++ tailWord_5352279).sum := by decide
  have hdescent : baseEnd_5352279 < baseStart_5352279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352290 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5352290 : Nat := 118140960795 + 5352290 * 2 ^ 59
def prefixEnd_5352290 : Nat := 4983230072969 + 3 ^ 40 * 5352290 * 2
def baseEnd_5352290 : Nat := 916099124084323124820091

theorem tailTrace_5352290 : CollatzResearch.WordTrace tailWord_5352290 prefixEnd_5352290 916099124084323124820091 := by
  unfold tailWord_5352290
  simp only [CollatzResearch.WordTrace]
  refine ⟨48803513444893725800505581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130142702519716602134681549 48803513444893725800505581)
  ·
    refine ⟨18301317541835147175189593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48803513444893725800505581 18301317541835147175189593)
    ·
      refine ⟨13725988156376360381392195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18301317541835147175189593 13725988156376360381392195)
      ·
        refine ⟨20588982234564540572088293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725988156376360381392195 20588982234564540572088293)
        ·
          refine ⟨3860434168980851357266555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20588982234564540572088293 3860434168980851357266555)
          ·
            refine ⟨5790651253471277035899833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860434168980851357266555 5790651253471277035899833)
            ·
              refine ⟨4342988440103457776924875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5790651253471277035899833 4342988440103457776924875)
              ·
                refine ⟨6514482660155186665387313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342988440103457776924875 6514482660155186665387313)
                ·
                  refine ⟨4885861995116389999040485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514482660155186665387313 4885861995116389999040485)
                  ·
                    refine ⟨916099124084323124820091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4885861995116389999040485 916099124084323124820091)
                    ·
                      rfl

theorem cell23_5352290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5352290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352290 prefixEnd_5352290 := by exact prefixLift 5352290
  have htrace : WordTrace (prefixWord ++ tailWord_5352290) baseStart_5352290 baseEnd_5352290 := by
    simpa [prefixWord, tailWord_5352290, baseEnd_5352290] using wordTrace_append hprefix tailTrace_5352290
  have hstable : (prefixWord ++ tailWord_5352290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352290).length < 2 ^ (prefixWord ++ tailWord_5352290).sum := by decide
  have hdescent : baseEnd_5352290 < baseStart_5352290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352296 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5352296 : Nat := 118140960795 + 5352296 * 2 ^ 59
def prefixEnd_5352296 : Nat := 4983230072969 + 3 ^ 40 * 5352296 * 2
def baseEnd_5352296 : Nat := 2748300453136896350985245

theorem tailTrace_5352296 : CollatzResearch.WordTrace tailWord_5352296 prefixEnd_5352296 2748300453136896350985245 := by
  unfold tailWord_5352296
  simp only [CollatzResearch.WordTrace]
  refine ⟨97607136308776583113370371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130142848411702110817827161 97607136308776583113370371)
  ·
    refine ⟨146410704463164874670055557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97607136308776583113370371 146410704463164874670055557)
    ·
      refine ⟨27452007086843414000635417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146410704463164874670055557 27452007086843414000635417)
      ·
        refine ⟨20589005315132560500476563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27452007086843414000635417 20589005315132560500476563)
        ·
          refine ⟨30883507972698840750714845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20589005315132560500476563 30883507972698840750714845)
          ·
            refine ⟨11581315489762065281518067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30883507972698840750714845 11581315489762065281518067)
            ·
              refine ⟨17371973234643097922277101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11581315489762065281518067 17371973234643097922277101)
              ·
                refine ⟨6514489962991161720853913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17371973234643097922277101 6514489962991161720853913)
                ·
                  refine ⟨4885867472243371290640435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514489962991161720853913 4885867472243371290640435)
                  ·
                    refine ⟨7328801208365056935960653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885867472243371290640435 7328801208365056935960653)
                    ·
                      refine ⟨2748300453136896350985245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328801208365056935960653 2748300453136896350985245)
                      ·
                        rfl

theorem cell23_5352296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5352296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352296 prefixEnd_5352296 := by exact prefixLift 5352296
  have htrace : WordTrace (prefixWord ++ tailWord_5352296) baseStart_5352296 baseEnd_5352296 := by
    simpa [prefixWord, tailWord_5352296, baseEnd_5352296] using wordTrace_append hprefix tailTrace_5352296
  have hstable : (prefixWord ++ tailWord_5352296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352296).length < 2 ^ (prefixWord ++ tailWord_5352296).sum := by decide
  have hdescent : baseEnd_5352296 < baseStart_5352296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352306 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_5352306 : Nat := 118140960795 + 5352306 * 2 ^ 59
def prefixEnd_5352306 : Nat := 4983230072969 + 3 ^ 40 * 5352306 * 2
def baseEnd_5352306 : Nat := 2748305587943441311860199

theorem tailTrace_5352306 : CollatzResearch.WordTrace tailWord_5352306 prefixEnd_5352306 2748305587943441311860199 := by
  unfold tailWord_5352306
  simp only [CollatzResearch.WordTrace]
  refine ⟨48803659336879234483651193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130143091565011291956403181 48803659336879234483651193)
  ·
    refine ⟨36602744502659425862738395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48803659336879234483651193 36602744502659425862738395)
    ·
      refine ⟨54904116753989138794107593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36602744502659425862738395 54904116753989138794107593)
      ·
        refine ⟨41178087565491854095580695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54904116753989138794107593 41178087565491854095580695)
        ·
          refine ⟨61767131348237781143371043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41178087565491854095580695 61767131348237781143371043)
          ·
            refine ⟨92650697022356671715056565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61767131348237781143371043 92650697022356671715056565)
            ·
              refine ⟨8686002845845937973286553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92650697022356671715056565 8686002845845937973286553)
              ·
                refine ⟨6514502134384453479964915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8686002845845937973286553 6514502134384453479964915)
                ·
                  refine ⟨9771753201576680219947373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514502134384453479964915 9771753201576680219947373)
                  ·
                    refine ⟨3664407450591255082480265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9771753201576680219947373 3664407450591255082480265)
                    ·
                      refine ⟨2748305587943441311860199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664407450591255082480265 2748305587943441311860199)
                      ·
                        rfl

theorem cell23_5352306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_5352306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352306 prefixEnd_5352306 := by exact prefixLift 5352306
  have htrace : WordTrace (prefixWord ++ tailWord_5352306) baseStart_5352306 baseEnd_5352306 := by
    simpa [prefixWord, tailWord_5352306, baseEnd_5352306] using wordTrace_append hprefix tailTrace_5352306
  have hstable : (prefixWord ++ tailWord_5352306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352306).length < 2 ^ (prefixWord ++ tailWord_5352306).sum := by decide
  have hdescent : baseEnd_5352306 < baseStart_5352306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352319 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 6, 2, 2]
def baseStart_5352319 : Nat := 118140960795 + 5352319 * 2 ^ 59
def prefixEnd_5352319 : Nat := 4983230072969 + 3 ^ 40 * 5352319 * 2
def baseEnd_5352319 : Nat := 2748312263191949760997639

theorem tailTrace_5352319 : CollatzResearch.WordTrace tailWord_5352319 prefixEnd_5352319 2748312263191949760997639 := by
  unfold tailWord_5352319
  simp only [CollatzResearch.WordTrace]
  refine ⟨195215111496469841154828011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130143407664313227436552007 195215111496469841154828011)
  ·
    refine ⟨292822667244704761732242017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195215111496469841154828011 292822667244704761732242017)
    ·
      refine ⟨219617000433528571299181513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292822667244704761732242017 219617000433528571299181513)
      ·
        refine ⟨164712750325146428474386135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219617000433528571299181513 164712750325146428474386135)
        ·
          refine ⟨247069125487719642711579203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164712750325146428474386135 247069125487719642711579203)
          ·
            refine ⟨370603688231579464067368805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247069125487719642711579203 370603688231579464067368805)
            ·
              refine ⟨69488191543421149512631651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 370603688231579464067368805 69488191543421149512631651)
              ·
                refine ⟨104232287315131724268947477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69488191543421149512631651 104232287315131724268947477)
                ·
                  refine ⟨4885888467896799575106913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104232287315131724268947477 4885888467896799575106913)
                  ·
                    refine ⟨3664416350922599681330185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4885888467896799575106913 3664416350922599681330185)
                    ·
                      refine ⟨2748312263191949760997639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664416350922599681330185 2748312263191949760997639)
                      ·
                        rfl

theorem cell23_5352319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_5352319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352319 prefixEnd_5352319 := by exact prefixLift 5352319
  have htrace : WordTrace (prefixWord ++ tailWord_5352319) baseStart_5352319 baseEnd_5352319 := by
    simpa [prefixWord, tailWord_5352319, baseEnd_5352319] using wordTrace_append hprefix tailTrace_5352319
  have hstable : (prefixWord ++ tailWord_5352319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352319).length < 2 ^ (prefixWord ++ tailWord_5352319).sum := by decide
  have hdescent : baseEnd_5352319 < baseStart_5352319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352345 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_5352345 : Nat := 118140960795 + 5352345 * 2 ^ 59
def prefixEnd_5352345 : Nat := 4983230072969 + 3 ^ 40 * 5352345 * 2
def baseEnd_5352345 : Nat := 2748325613688966659272519

theorem tailTrace_5352345 : CollatzResearch.WordTrace tailWord_5352345 prefixEnd_5352345 2748325613688966659272519 := by
  unfold tailWord_5352345
  simp only [CollatzResearch.WordTrace]
  refine ⟨195216059794375647595274489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130144039862917098396849659 195216059794375647595274489)
  ·
    refine ⟨146412044845781735696455867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195216059794375647595274489 146412044845781735696455867)
    ·
      refine ⟨219618067268672603544683801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146412044845781735696455867 219618067268672603544683801)
      ·
        refine ⟨164713550451504452658512851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219618067268672603544683801 164713550451504452658512851)
        ·
          refine ⟨247070325677256678987769277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164713550451504452658512851 247070325677256678987769277)
          ·
            refine ⟨92651372128971254620413479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247070325677256678987769277 92651372128971254620413479)
            ·
              refine ⟨138977058193456881930620219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92651372128971254620413479 138977058193456881930620219)
              ·
                refine ⟨208465587290185322895930329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138977058193456881930620219 208465587290185322895930329)
                ·
                  refine ⟨156349190467638992171947747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208465587290185322895930329 156349190467638992171947747)
                  ·
                    refine ⟨234523785701458488257921621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 156349190467638992171947747 234523785701458488257921621)
                    ·
                      refine ⟨2748325613688966659272519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 234523785701458488257921621 2748325613688966659272519)
                      ·
                        rfl

theorem cell23_5352345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_5352345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352345 prefixEnd_5352345 := by exact prefixLift 5352345
  have htrace : WordTrace (prefixWord ++ tailWord_5352345) baseStart_5352345 baseEnd_5352345 := by
    simpa [prefixWord, tailWord_5352345, baseEnd_5352345] using wordTrace_append hprefix tailTrace_5352345
  have hstable : (prefixWord ++ tailWord_5352345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352345).length < 2 ^ (prefixWord ++ tailWord_5352345).sum := by decide
  have hdescent : baseEnd_5352345 < baseStart_5352345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352352 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_5352352 : Nat := 118140960795 + 5352352 * 2 ^ 59
def prefixEnd_5352352 : Nat := 4983230072969 + 3 ^ 40 * 5352352 * 2
def baseEnd_5352352 : Nat := 2748329208053548131884987

theorem tailTrace_5352352 : CollatzResearch.WordTrace tailWord_5352352 prefixEnd_5352352 2748329208053548131884987 := by
  unfold tailWord_5352352
  simp only [CollatzResearch.WordTrace]
  refine ⟨97608157552675143895389655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130144210070233525193852873 97608157552675143895389655)
  ·
    refine ⟨146412236329012715843084483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97608157552675143895389655 146412236329012715843084483)
    ·
      refine ⟨219618354493519073764626725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146412236329012715843084483 219618354493519073764626725)
      ·
        refine ⟨41178441467534826330867511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219618354493519073764626725 41178441467534826330867511)
        ·
          refine ⟨61767662201302239496301267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41178441467534826330867511 61767662201302239496301267)
          ·
            refine ⟨92651493301953359244451901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61767662201302239496301267 92651493301953359244451901)
            ·
              refine ⟨34744309988232509716669463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92651493301953359244451901 34744309988232509716669463)
              ·
                refine ⟨52116464982348764575004195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34744309988232509716669463 52116464982348764575004195)
                ·
                  refine ⟨78174697473523146862506293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52116464982348764575004195 78174697473523146862506293)
                  ·
                    refine ⟨7328877888142795018359965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78174697473523146862506293 7328877888142795018359965)
                    ·
                      refine ⟨2748329208053548131884987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7328877888142795018359965 2748329208053548131884987)
                      ·
                        rfl

theorem cell23_5352352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_5352352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352352 prefixEnd_5352352 := by exact prefixLift 5352352
  have htrace : WordTrace (prefixWord ++ tailWord_5352352) baseStart_5352352 baseEnd_5352352 := by
    simpa [prefixWord, tailWord_5352352, baseEnd_5352352] using wordTrace_append hprefix tailTrace_5352352
  have hstable : (prefixWord ++ tailWord_5352352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352352).length < 2 ^ (prefixWord ++ tailWord_5352352).sum := by decide
  have hdescent : baseEnd_5352352 < baseStart_5352352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352353 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5352353 : Nat := 118140960795 + 5352353 * 2 ^ 59
def prefixEnd_5352353 : Nat := 4983230072969 + 3 ^ 40 * 5352353 * 2
def baseEnd_5352353 : Nat := 2748329721534202627972483

theorem tailTrace_5352353 : CollatzResearch.WordTrace tailWord_5352353 prefixEnd_5352353 2748329721534202627972483 := by
  unfold tailWord_5352353
  simp only [CollatzResearch.WordTrace]
  refine ⟨195216351578346664961565713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130144234385564443307710475 195216351578346664961565713)
  ·
    refine ⟨146412263683759998721174285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195216351578346664961565713 146412263683759998721174285)
    ·
      refine ⟨54904598881409999520440357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146412263683759998721174285 54904598881409999520440357)
      ·
        refine ⟨10294612290264374910082567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54904598881409999520440357 10294612290264374910082567)
        ·
          refine ⟨15441918435396562365123851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294612290264374910082567 15441918435396562365123851)
          ·
            refine ⟨23162877653094843547685777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15441918435396562365123851 23162877653094843547685777)
            ·
              refine ⟨17372158239821132660764333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23162877653094843547685777 17372158239821132660764333)
              ·
                refine ⟨6514559339932924747786625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17372158239821132660764333 6514559339932924747786625)
                ·
                  refine ⟨4885919504949693560839969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514559339932924747786625 4885919504949693560839969)
                  ·
                    refine ⟨3664439628712270170629977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4885919504949693560839969 3664439628712270170629977)
                    ·
                      refine ⟨2748329721534202627972483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664439628712270170629977 2748329721534202627972483)
                      ·
                        rfl

theorem cell23_5352353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5352353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352353 prefixEnd_5352353 := by exact prefixLift 5352353
  have htrace : WordTrace (prefixWord ++ tailWord_5352353) baseStart_5352353 baseEnd_5352353 := by
    simpa [prefixWord, tailWord_5352353, baseEnd_5352353] using wordTrace_append hprefix tailTrace_5352353
  have hstable : (prefixWord ++ tailWord_5352353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352353).length < 2 ^ (prefixWord ++ tailWord_5352353).sum := by decide
  have hdescent : baseEnd_5352353 < baseStart_5352353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352359 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 7]
def baseStart_5352359 : Nat := 118140960795 + 5352359 * 2 ^ 59
def prefixEnd_5352359 : Nat := 4983230072969 + 3 ^ 40 * 5352359 * 2
def baseEnd_5352359 : Nat := 305370311379792178277495

theorem tailTrace_5352359 : CollatzResearch.WordTrace tailWord_5352359 prefixEnd_5352359 305370311379792178277495 := by
  unfold tailWord_5352359
  simp only [CollatzResearch.WordTrace]
  refine ⟨195216570416324927986284131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130144380277549951990856087 195216570416324927986284131)
  ·
    refine ⟨292824855624487391979426197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195216570416324927986284131 292824855624487391979426197)
    ·
      refine ⟨13726165107397846499035603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 292824855624487391979426197 13726165107397846499035603)
      ·
        refine ⟨20589247661096769748553405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13726165107397846499035603 20589247661096769748553405)
        ·
          refine ⟨7720967872911288655707527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20589247661096769748553405 7720967872911288655707527)
          ·
            refine ⟨11581451809366932983561291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720967872911288655707527 11581451809366932983561291)
            ·
              refine ⟨17372177714050399475341937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11581451809366932983561291 17372177714050399475341937)
              ·
                refine ⟨13029133285537799606506453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17372177714050399475341937 13029133285537799606506453)
                ·
                  refine ⟨305370311379792178277495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13029133285537799606506453 305370311379792178277495)
                  ·
                    rfl

theorem cell23_5352359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 7].length) (baseStart_5352359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352359 prefixEnd_5352359 := by exact prefixLift 5352359
  have htrace : WordTrace (prefixWord ++ tailWord_5352359) baseStart_5352359 baseEnd_5352359 := by
    simpa [prefixWord, tailWord_5352359, baseEnd_5352359] using wordTrace_append hprefix tailTrace_5352359
  have hstable : (prefixWord ++ tailWord_5352359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352359).length < 2 ^ (prefixWord ++ tailWord_5352359).sum := by decide
  have hdescent : baseEnd_5352359 < baseStart_5352359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352419 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 3, 4]
def baseStart_5352419 : Nat := 118140960795 + 5352419 * 2 ^ 59
def prefixEnd_5352419 : Nat := 4983230072969 + 3 ^ 40 * 5352419 * 2
def baseEnd_5352419 : Nat := 916121203752466456582393

theorem tailTrace_5352419 : CollatzResearch.WordTrace tailWord_5352419 prefixEnd_5352419 916121203752466456582393 := by
  unfold tailWord_5352419
  simp only [CollatzResearch.WordTrace]
  refine ⟨195218758796107558233468311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130145839197405038822312207 195218758796107558233468311)
  ·
    refine ⟨292828138194161337350202467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195218758796107558233468311 292828138194161337350202467)
    ·
      refine ⟨439242207291242006025303701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292828138194161337350202467 439242207291242006025303701)
      ·
        refine ⟨20589478466776969032436111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 439242207291242006025303701 20589478466776969032436111)
        ·
          refine ⟨30884217700165453548654167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20589478466776969032436111 30884217700165453548654167)
          ·
            refine ⟨46326326550248180322981251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30884217700165453548654167 46326326550248180322981251)
            ·
              refine ⟨69489489825372270484471877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46326326550248180322981251 69489489825372270484471877)
              ·
                refine ⟨13029279342257300715838477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69489489825372270484471877 13029279342257300715838477)
                ·
                  refine ⟨4885979753346487768439429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13029279342257300715838477 4885979753346487768439429)
                  ·
                    refine ⟨916121203752466456582393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4885979753346487768439429 916121203752466456582393)
                    ·
                      rfl

theorem cell23_5352419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 4].length) (baseStart_5352419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352419 prefixEnd_5352419 := by exact prefixLift 5352419
  have htrace : WordTrace (prefixWord ++ tailWord_5352419) baseStart_5352419 baseEnd_5352419 := by
    simpa [prefixWord, tailWord_5352419, baseEnd_5352419] using wordTrace_append hprefix tailTrace_5352419
  have hstable : (prefixWord ++ tailWord_5352419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352419).length < 2 ^ (prefixWord ++ tailWord_5352419).sum := by decide
  have hdescent : baseEnd_5352419 < baseStart_5352419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352453 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_5352453 : Nat := 118140960795 + 5352453 * 2 ^ 59
def prefixEnd_5352453 : Nat := 4983230072969 + 3 ^ 40 * 5352453 * 2
def baseEnd_5352453 : Nat := 916127023199884078907341

theorem tailTrace_5352453 : CollatzResearch.WordTrace tailWord_5352453 prefixEnd_5352453 916127023199884078907341 := by
  unfold tailWord_5352453
  simp only [CollatzResearch.WordTrace]
  refine ⟨195219998877984382040206013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130146665918656254693470675 195219998877984382040206013)
  ·
    refine ⟨73207499579244143265077255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195219998877984382040206013 73207499579244143265077255)
    ·
      refine ⟨109811249368866214897615883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73207499579244143265077255 109811249368866214897615883)
      ·
        refine ⟨164716874053299322346423825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109811249368866214897615883 164716874053299322346423825)
        ·
          refine ⟨123537655539974491759817869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164716874053299322346423825 123537655539974491759817869)
          ·
            refine ⟨46326620827490434409931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123537655539974491759817869 46326620827490434409931701)
            ·
              refine ⟨4343120702577228225931097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46326620827490434409931701 4343120702577228225931097)
              ·
                refine ⟨3257340526932921169448323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4343120702577228225931097 3257340526932921169448323)
                ·
                  refine ⟨4886010790399381754172485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257340526932921169448323 4886010790399381754172485)
                  ·
                    refine ⟨916127023199884078907341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886010790399381754172485 916127023199884078907341)
                    ·
                      rfl

theorem cell23_5352453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_5352453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352453 prefixEnd_5352453 := by exact prefixLift 5352453
  have htrace : WordTrace (prefixWord ++ tailWord_5352453) baseStart_5352453 baseEnd_5352453 := by
    simpa [prefixWord, tailWord_5352453, baseEnd_5352453] using wordTrace_append hprefix tailTrace_5352453
  have hstable : (prefixWord ++ tailWord_5352453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352453).length < 2 ^ (prefixWord ++ tailWord_5352453).sum := by decide
  have hdescent : baseEnd_5352453 < baseStart_5352453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352479 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 3, 5]
def baseStart_5352479 : Nat := 118140960795 + 5352479 * 2 ^ 59
def prefixEnd_5352479 : Nat := 4983230072969 + 3 ^ 40 * 5352479 * 2
def baseEnd_5352479 : Nat := 916131473365556378332301

theorem tailTrace_5352479 : CollatzResearch.WordTrace tailWord_5352479 prefixEnd_5352479 916131473365556378332301 := by
  unfold tailWord_5352479
  simp only [CollatzResearch.WordTrace]
  refine ⟨195220947175890188480652491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130147298117260125653768327 195220947175890188480652491)
  ·
    refine ⟨292831420763835282720978737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195220947175890188480652491 292831420763835282720978737)
    ·
      refine ⟨219623565572876462040734053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292831420763835282720978737 219623565572876462040734053)
      ·
        refine ⟨41179418544914336632637635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219623565572876462040734053 41179418544914336632637635)
        ·
          refine ⟨61769127817371504948956453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41179418544914336632637635 61769127817371504948956453)
          ·
            refine ⟨11581711465757157177929335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61769127817371504948956453 11581711465757157177929335)
            ·
              refine ⟨17372567198635735766894003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11581711465757157177929335 17372567198635735766894003)
              ·
                refine ⟨26058850797953603650341005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17372567198635735766894003 26058850797953603650341005)
                ·
                  refine ⟨9772069049232601368877877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26058850797953603650341005 9772069049232601368877877)
                  ·
                    refine ⟨916131473365556378332301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9772069049232601368877877 916131473365556378332301)
                    ·
                      rfl

theorem cell23_5352479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_5352479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352479 prefixEnd_5352479 := by exact prefixLift 5352479
  have htrace : WordTrace (prefixWord ++ tailWord_5352479) baseStart_5352479 baseEnd_5352479 := by
    simpa [prefixWord, tailWord_5352479, baseEnd_5352479] using wordTrace_append hprefix tailTrace_5352479
  have hstable : (prefixWord ++ tailWord_5352479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352479).length < 2 ^ (prefixWord ++ tailWord_5352479).sum := by decide
  have hdescent : baseEnd_5352479 < baseStart_5352479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352496 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 1, 5]
def baseStart_5352496 : Nat := 118140960795 + 5352496 * 2 ^ 59
def prefixEnd_5352496 : Nat := 4983230072969 + 3 ^ 40 * 5352496 * 2
def baseEnd_5352496 : Nat := 916134383089265189494775

theorem tailTrace_5352496 : CollatzResearch.WordTrace tailWord_5352496 prefixEnd_5352496 916134383089265189494775 := by
  unfold tailWord_5352496
  simp only [CollatzResearch.WordTrace]
  refine ⟨97610783608414300192010671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130147711477885733589347561 97610783608414300192010671)
  ·
    refine ⟨146416175412621450288016007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97610783608414300192010671 146416175412621450288016007)
    ·
      refine ⟨219624263118932175432024011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146416175412621450288016007 219624263118932175432024011)
      ·
        refine ⟨329436394678398263148036017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219624263118932175432024011 329436394678398263148036017)
        ·
          refine ⟨247077296008798697361027013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329436394678398263148036017 247077296008798697361027013)
          ·
            refine ⟨46326993001649755755192565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247077296008798697361027013 46326993001649755755192565)
            ·
              refine ⟨4343155593904664602049303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46326993001649755755192565 4343155593904664602049303)
              ·
                refine ⟨6514733390856996903073955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343155593904664602049303 6514733390856996903073955)
                ·
                  refine ⟨9772100086285495354610933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514733390856996903073955 9772100086285495354610933)
                  ·
                    refine ⟨916134383089265189494775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9772100086285495354610933 916134383089265189494775)
                    ·
                      rfl

theorem cell23_5352496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_5352496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352496 prefixEnd_5352496 := by exact prefixLift 5352496
  have htrace : WordTrace (prefixWord ++ tailWord_5352496) baseStart_5352496 baseEnd_5352496 := by
    simpa [prefixWord, tailWord_5352496, baseEnd_5352496] using wordTrace_append hprefix tailTrace_5352496
  have hstable : (prefixWord ++ tailWord_5352496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352496).length < 2 ^ (prefixWord ++ tailWord_5352496).sum := by decide
  have hdescent : baseEnd_5352496 < baseStart_5352496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352526 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_5352526 : Nat := 118140960795 + 5352526 * 2 ^ 59
def prefixEnd_5352526 : Nat := 4983230072969 + 3 ^ 40 * 5352526 * 2
def baseEnd_5352526 : Nat := 916139517895810150369729

theorem tailTrace_5352526 : CollatzResearch.WordTrace tailWord_5352526 prefixEnd_5352526 916139517895810150369729 := by
  unfold tailWord_5352526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402832675839989438451679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130148440937813277005075621 24402832675839989438451679)
  ·
    refine ⟨36604249013759984157677519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24402832675839989438451679 36604249013759984157677519)
    ·
      refine ⟨54906373520639976236516279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36604249013759984157677519 54906373520639976236516279)
      ·
        refine ⟨82359560280959964354774419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54906373520639976236516279 82359560280959964354774419)
        ·
          refine ⟨123539340421439946532161629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82359560280959964354774419 123539340421439946532161629)
          ·
            refine ⟨46327252658039979949560611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123539340421439946532161629 46327252658039979949560611)
            ·
              refine ⟨69490878987059969924340917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46327252658039979949560611 69490878987059969924340917)
              ·
                refine ⟨6514769905036872180406961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69490878987059969924340917 6514769905036872180406961)
                ·
                  refine ⟨4886077428777654135305221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514769905036872180406961 4886077428777654135305221)
                  ·
                    refine ⟨916139517895810150369729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886077428777654135305221 916139517895810150369729)
                    ·
                      rfl

theorem cell23_5352526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_5352526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352526 prefixEnd_5352526 := by exact prefixLift 5352526
  have htrace : WordTrace (prefixWord ++ tailWord_5352526) baseStart_5352526 baseEnd_5352526 := by
    simpa [prefixWord, tailWord_5352526, baseEnd_5352526] using wordTrace_append hprefix tailTrace_5352526
  have hstable : (prefixWord ++ tailWord_5352526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352526).length < 2 ^ (prefixWord ++ tailWord_5352526).sum := by decide
  have hdescent : baseEnd_5352526 < baseStart_5352526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352529 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_5352529 : Nat := 118140960795 + 5352529 * 2 ^ 59
def prefixEnd_5352529 : Nat := 4983230072969 + 3 ^ 40 * 5352529 * 2
def baseEnd_5352529 : Nat := 2748420094129393939371673

theorem tailTrace_5352529 : CollatzResearch.WordTrace tailWord_5352529 prefixEnd_5352529 2748420094129393939371673 := by
  unfold tailWord_5352529
  simp only [CollatzResearch.WordTrace]
  refine ⟨195222770825709047019972641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130148513883806031346648427 195222770825709047019972641)
  ·
    refine ⟨146417078119281785264979481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195222770825709047019972641 146417078119281785264979481)
    ·
      refine ⟨109812808589461338948734611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146417078119281785264979481 109812808589461338948734611)
      ·
        refine ⟨164719212884192008423101917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109812808589461338948734611 164719212884192008423101917)
        ·
          refine ⟨61769704831572003158663219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164719212884192008423101917 61769704831572003158663219)
          ·
            refine ⟨92654557247358004737994829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61769704831572003158663219 92654557247358004737994829)
            ·
              refine ⟨34745458967759251776748061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92654557247358004737994829 34745458967759251776748061)
              ·
                refine ⟨13029547112909719416280523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34745458967759251776748061 13029547112909719416280523)
                ·
                  refine ⟨19544320669364579124420785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13029547112909719416280523 19544320669364579124420785)
                  ·
                    refine ⟨14658240502023434343315589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19544320669364579124420785 14658240502023434343315589)
                    ·
                      refine ⟨2748420094129393939371673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14658240502023434343315589 2748420094129393939371673)
                      ·
                        rfl

theorem cell23_5352529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_5352529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352529 prefixEnd_5352529 := by exact prefixLift 5352529
  have htrace : WordTrace (prefixWord ++ tailWord_5352529) baseStart_5352529 baseEnd_5352529 := by
    simpa [prefixWord, tailWord_5352529, baseEnd_5352529] using wordTrace_append hprefix tailTrace_5352529
  have hstable : (prefixWord ++ tailWord_5352529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352529).length < 2 ^ (prefixWord ++ tailWord_5352529).sum := by decide
  have hdescent : baseEnd_5352529 < baseStart_5352529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352533 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5352533 : Nat := 118140960795 + 5352533 * 2 ^ 59
def prefixEnd_5352533 : Nat := 4983230072969 + 3 ^ 40 * 5352533 * 2
def baseEnd_5352533 : Nat := 2748422148052011923721655

theorem tailTrace_5352533 : CollatzResearch.WordTrace tailWord_5352533 prefixEnd_5352533 2748422148052011923721655 := by
  unfold tailWord_5352533
  simp only [CollatzResearch.WordTrace]
  refine ⟨195222916717694555703118253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130148611145129703802078835 195222916717694555703118253)
  ·
    refine ⟨73208593769135458388669345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195222916717694555703118253 73208593769135458388669345)
    ·
      refine ⟨54906445326851593791502009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73208593769135458388669345 54906445326851593791502009)
      ·
        refine ⟨41179833995138695343626507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54906445326851593791502009 41179833995138695343626507)
        ·
          refine ⟨61769750992708043015439761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41179833995138695343626507 61769750992708043015439761)
          ·
            refine ⟨46327313244531032261579821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61769750992708043015439761 46327313244531032261579821)
            ·
              refine ⟨17372742466699137098092433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46327313244531032261579821 17372742466699137098092433)
              ·
                refine ⟨13029556850024352823569325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17372742466699137098092433 13029556850024352823569325)
                ·
                  refine ⟨4886083818759132308838497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13029556850024352823569325 4886083818759132308838497)
                  ·
                    refine ⟨3664562864069349231628873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4886083818759132308838497 3664562864069349231628873)
                    ·
                      refine ⟨2748422148052011923721655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664562864069349231628873 2748422148052011923721655)
                      ·
                        rfl

theorem cell23_5352533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5352533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352533 prefixEnd_5352533 := by exact prefixLift 5352533
  have htrace : WordTrace (prefixWord ++ tailWord_5352533) baseStart_5352533 baseEnd_5352533 := by
    simpa [prefixWord, tailWord_5352533, baseEnd_5352533] using wordTrace_append hprefix tailTrace_5352533
  have hstable : (prefixWord ++ tailWord_5352533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352533).length < 2 ^ (prefixWord ++ tailWord_5352533).sum := by decide
  have hdescent : baseEnd_5352533 < baseStart_5352533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352536 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_5352536 : Nat := 118140960795 + 5352536 * 2 ^ 59
def prefixEnd_5352536 : Nat := 4983230072969 + 3 ^ 40 * 5352536 * 2
def baseEnd_5352536 : Nat := 2748423688493975411984141

theorem tailTrace_5352536 : CollatzResearch.WordTrace tailWord_5352536 prefixEnd_5352536 2748423688493975411984141 := by
  unfold tailWord_5352536
  simp only [CollatzResearch.WordTrace]
  refine ⟨97611513068341843607738731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130148684091122458143651641 97611513068341843607738731)
  ·
    refine ⟨146417269602512765411608097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97611513068341843607738731 146417269602512765411608097)
    ·
      refine ⟨109812952201884574058706073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146417269602512765411608097 109812952201884574058706073)
      ·
        refine ⟨82359714151413430544029555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109812952201884574058706073 82359714151413430544029555)
        ·
          refine ⟨123539571227120145816044333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82359714151413430544029555 123539571227120145816044333)
          ·
            refine ⟨46327339210170054681016625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123539571227120145816044333 46327339210170054681016625)
            ·
              refine ⟨34745504407627541010762469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46327339210170054681016625 34745504407627541010762469)
              ·
                refine ⟨6514782076430163939517963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34745504407627541010762469 6514782076430163939517963)
                ·
                  refine ⟨9772173114645245909276945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514782076430163939517963 9772173114645245909276945)
                  ·
                    refine ⟨7329129835983934431957709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9772173114645245909276945 7329129835983934431957709)
                    ·
                      refine ⟨2748423688493975411984141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7329129835983934431957709 2748423688493975411984141)
                      ·
                        rfl

theorem cell23_5352536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_5352536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352536 prefixEnd_5352536 := by exact prefixLift 5352536
  have htrace : WordTrace (prefixWord ++ tailWord_5352536) baseStart_5352536 baseEnd_5352536 := by
    simpa [prefixWord, tailWord_5352536, baseEnd_5352536] using wordTrace_append hprefix tailTrace_5352536
  have hstable : (prefixWord ++ tailWord_5352536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352536).length < 2 ^ (prefixWord ++ tailWord_5352536).sum := by decide
  have hdescent : baseEnd_5352536 < baseStart_5352536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352553 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 1, 2, 3]
def baseStart_5352553 : Nat := 118140960795 + 5352553 * 2 ^ 59
def prefixEnd_5352553 : Nat := 4983230072969 + 3 ^ 40 * 5352553 * 2
def baseEnd_5352553 : Nat := 2748432417665101845471563

theorem tailTrace_5352553 : CollatzResearch.WordTrace tailWord_5352553 prefixEnd_5352553 2748432417665101845471563 := by
  unfold tailWord_5352553
  simp only [CollatzResearch.WordTrace]
  refine ⟨195223646177622099118846313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130149097451748066079230875 195223646177622099118846313)
  ·
    refine ⟨146417734633216574339134735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195223646177622099118846313 146417734633216574339134735)
    ·
      refine ⟨219626601949824861508702103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146417734633216574339134735 219626601949824861508702103)
      ·
        refine ⟨329439902924737292263053155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219626601949824861508702103 329439902924737292263053155)
        ·
          refine ⟨494159854387105938394579733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329439902924737292263053155 494159854387105938394579733)
          ·
            refine ⟨23163743174395590862245925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 494159854387105938394579733 23163743174395590862245925)
            ·
              refine ⟨4343201845199173286671111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23163743174395590862245925 4343201845199173286671111)
              ·
                refine ⟨6514802767798759930006667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343201845199173286671111 6514802767798759930006667)
                ·
                  refine ⟨9772204151698139895010001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514802767798759930006667 9772204151698139895010001)
                  ·
                    refine ⟨7329153113773604921257501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9772204151698139895010001 7329153113773604921257501)
                    ·
                      refine ⟨2748432417665101845471563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7329153113773604921257501 2748432417665101845471563)
                      ·
                        rfl

theorem cell23_5352553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 2, 3].length) (baseStart_5352553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352553 prefixEnd_5352553 := by exact prefixLift 5352553
  have htrace : WordTrace (prefixWord ++ tailWord_5352553) baseStart_5352553 baseEnd_5352553 := by
    simpa [prefixWord, tailWord_5352553, baseEnd_5352553] using wordTrace_append hprefix tailTrace_5352553
  have hstable : (prefixWord ++ tailWord_5352553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352553).length < 2 ^ (prefixWord ++ tailWord_5352553).sum := by decide
  have hdescent : baseEnd_5352553 < baseStart_5352553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352576 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2]
def baseStart_5352576 : Nat := 118140960795 + 5352576 * 2 ^ 59
def prefixEnd_5352576 : Nat := 4983230072969 + 3 ^ 40 * 5352576 * 2
def baseEnd_5352576 : Nat := 2748444227720155255483957

theorem tailTrace_5352576 : CollatzResearch.WordTrace tailWord_5352576 prefixEnd_5352576 2748444227720155255483957 := by
  unfold tailWord_5352576
  simp only [CollatzResearch.WordTrace]
  refine ⟨97612242528269387023466791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130149656704359182697955721 97612242528269387023466791)
  ·
    refine ⟨146418363792404080535200187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97612242528269387023466791 146418363792404080535200187)
    ·
      refine ⟨219627545688606120802800281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146418363792404080535200187 219627545688606120802800281)
      ·
        refine ⟨164720659266454590602100211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219627545688606120802800281 164720659266454590602100211)
        ·
          refine ⟨247080988899681885903150317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164720659266454590602100211 247080988899681885903150317)
          ·
            refine ⟨92655370837380707213681369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247080988899681885903150317 92655370837380707213681369)
            ·
              refine ⟨69491528128035530410261027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92655370837380707213681369 69491528128035530410261027)
              ·
                refine ⟨104237292192053295615391541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69491528128035530410261027 104237292192053295615391541)
                ·
                  refine ⟨9772246143004996463942957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104237292192053295615391541 9772246143004996463942957)
                  ·
                    refine ⟨3664592303626873673978609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9772246143004996463942957 3664592303626873673978609)
                    ·
                      refine ⟨2748444227720155255483957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664592303626873673978609 2748444227720155255483957)
                      ·
                        rfl

theorem cell23_5352576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_5352576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352576 prefixEnd_5352576 := by exact prefixLift 5352576
  have htrace : WordTrace (prefixWord ++ tailWord_5352576) baseStart_5352576 baseEnd_5352576 := by
    simpa [prefixWord, tailWord_5352576, baseEnd_5352576] using wordTrace_append hprefix tailTrace_5352576
  have hstable : (prefixWord ++ tailWord_5352576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352576).length < 2 ^ (prefixWord ++ tailWord_5352576).sum := by decide
  have hdescent : baseEnd_5352576 < baseStart_5352576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352623 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 4, 2, 2]
def baseStart_5352623 : Nat := 118140960795 + 5352623 * 2 ^ 59
def prefixEnd_5352623 : Nat := 4983230072969 + 3 ^ 40 * 5352623 * 2
def baseEnd_5352623 : Nat := 2748468361310916571596241

theorem tailTrace_5352623 : CollatzResearch.WordTrace tailWord_5352623 prefixEnd_5352623 2748468361310916571596241 := by
  unfold tailWord_5352623
  simp only [CollatzResearch.WordTrace]
  refine ⟨195226199287368501073894523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130150799524912334049263015 195226199287368501073894523)
  ·
    refine ⟨292839298931052751610841785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195226199287368501073894523 292839298931052751610841785)
    ·
      refine ⟨219629474198289563708131339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292839298931052751610841785 219629474198289563708131339)
      ·
        refine ⟨329444211297434345562197009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219629474198289563708131339 329444211297434345562197009)
        ·
          refine ⟨247083158473075759171647757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329444211297434345562197009 247083158473075759171647757)
          ·
            refine ⟨92656184427403409689367909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247083158473075759171647757 92656184427403409689367909)
            ·
              refine ⟨17373034580138139316756483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92656184427403409689367909 17373034580138139316756483)
              ·
                refine ⟨26059551870207208975134725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17373034580138139316756483 26059551870207208975134725)
                ·
                  refine ⟨4886165975663851682837761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26059551870207208975134725 4886165975663851682837761)
                  ·
                    refine ⟨3664624481747888762128321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4886165975663851682837761 3664624481747888762128321)
                    ·
                      refine ⟨2748468361310916571596241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664624481747888762128321 2748468361310916571596241)
                      ·
                        rfl

theorem cell23_5352623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2, 2].length) (baseStart_5352623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352623 prefixEnd_5352623 := by exact prefixLift 5352623
  have htrace : WordTrace (prefixWord ++ tailWord_5352623) baseStart_5352623 baseEnd_5352623 := by
    simpa [prefixWord, tailWord_5352623, baseEnd_5352623] using wordTrace_append hprefix tailTrace_5352623
  have hstable : (prefixWord ++ tailWord_5352623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352623).length < 2 ^ (prefixWord ++ tailWord_5352623).sum := by decide
  have hdescent : baseEnd_5352623 < baseStart_5352623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352644 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_5352644 : Nat := 118140960795 + 5352644 * 2 ^ 59
def prefixEnd_5352644 : Nat := 4983230072969 + 3 ^ 40 * 5352644 * 2
def baseEnd_5352644 : Nat := 2748479144404660989433645

theorem tailTrace_5352644 : CollatzResearch.WordTrace tailWord_5352644 prefixEnd_5352644 2748479144404660989433645 := by
  unfold tailWord_5352644
  simp only [CollatzResearch.WordTrace]
  refine ⟨97613482610146210830204493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130151310146861614440272657 97613482610146210830204493)
  ·
    refine ⟨36605055978804829061326685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97613482610146210830204493 36605055978804829061326685)
    ·
      refine ⟨13726895992051810897997507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36605055978804829061326685 13726895992051810897997507)
      ·
        refine ⟨20590343988077716346996261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13726895992051810897997507 20590343988077716346996261)
        ·
          refine ⟨3860689497764571815061799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20590343988077716346996261 3860689497764571815061799)
          ·
            refine ⟨5791034246646857722592699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860689497764571815061799 5791034246646857722592699)
            ·
              refine ⟨8686551369970286583889049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791034246646857722592699 8686551369970286583889049)
              ·
                refine ⟨6514913527477714937916787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8686551369970286583889049 6514913527477714937916787)
                ·
                  refine ⟨9772370291216572406875181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514913527477714937916787 9772370291216572406875181)
                  ·
                    refine ⟨3664638859206214652578193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9772370291216572406875181 3664638859206214652578193)
                    ·
                      refine ⟨2748479144404660989433645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664638859206214652578193 2748479144404660989433645)
                      ·
                        rfl

theorem cell23_5352644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_5352644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352644 prefixEnd_5352644 := by exact prefixLift 5352644
  have htrace : WordTrace (prefixWord ++ tailWord_5352644) baseStart_5352644 baseEnd_5352644 := by
    simpa [prefixWord, tailWord_5352644, baseEnd_5352644] using wordTrace_append hprefix tailTrace_5352644
  have hstable : (prefixWord ++ tailWord_5352644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352644).length < 2 ^ (prefixWord ++ tailWord_5352644).sum := by decide
  have hdescent : baseEnd_5352644 < baseStart_5352644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352659 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 6, 5]
def baseStart_5352659 : Nat := 118140960795 + 5352659 * 2 ^ 59
def prefixEnd_5352659 : Nat := 4983230072969 + 3 ^ 40 * 5352659 * 2
def baseEnd_5352659 : Nat := 916162282204826143582025

theorem tailTrace_5352659 : CollatzResearch.WordTrace tailWord_5352659 prefixEnd_5352659 916162282204826143582025 := by
  unfold tailWord_5352659
  simp only [CollatzResearch.WordTrace]
  refine ⟨195227512315238079222205031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130151674876825386148136687 195227512315238079222205031)
  ·
    refine ⟨292841268472857118833307547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195227512315238079222205031 292841268472857118833307547)
    ·
      refine ⟨439261902709285678249961321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292841268472857118833307547 439261902709285678249961321)
      ·
        refine ⟨329446427031964258687470991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439261902709285678249961321 329446427031964258687470991)
        ·
          refine ⟨494169640547946388031206487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329446427031964258687470991 494169640547946388031206487)
          ·
            refine ⟨741254460821919582046809731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494169640547946388031206487 741254460821919582046809731)
            ·
              refine ⟨1111881691232879373070214597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741254460821919582046809731 1111881691232879373070214597)
              ·
                refine ⟨208477817106164882450665237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1111881691232879373070214597 208477817106164882450665237)
                ·
                  refine ⟨9772397676851478864874933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208477817106164882450665237 9772397676851478864874933)
                  ·
                    refine ⟨916162282204826143582025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9772397676851478864874933 916162282204826143582025)
                    ·
                      rfl

theorem cell23_5352659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 5].length) (baseStart_5352659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352659 prefixEnd_5352659 := by exact prefixLift 5352659
  have htrace : WordTrace (prefixWord ++ tailWord_5352659) baseStart_5352659 baseEnd_5352659 := by
    simpa [prefixWord, tailWord_5352659, baseEnd_5352659] using wordTrace_append hprefix tailTrace_5352659
  have hstable : (prefixWord ++ tailWord_5352659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352659).length < 2 ^ (prefixWord ++ tailWord_5352659).sum := by decide
  have hdescent : baseEnd_5352659 < baseStart_5352659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352676 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_5352676 : Nat := 118140960795 + 5352676 * 2 ^ 59
def prefixEnd_5352676 : Nat := 4983230072969 + 3 ^ 40 * 5352676 * 2
def baseEnd_5352676 : Nat := 916165191928534954744499

theorem tailTrace_5352676 : CollatzResearch.WordTrace tailWord_5352676 prefixEnd_5352676 916165191928534954744499 := by
  unfold tailWord_5352676
  simp only [CollatzResearch.WordTrace]
  refine ⟨97614066178088245562786941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130152088237450994083715921 97614066178088245562786941)
  ·
    refine ⟨36605274816783092086045103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97614066178088245562786941 36605274816783092086045103)
    ·
      refine ⟨54907912225174638129067655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36605274816783092086045103 54907912225174638129067655)
      ·
        refine ⟨82361868337761957193601483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54907912225174638129067655 82361868337761957193601483)
        ·
          refine ⟨123542802506642935790402225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82361868337761957193601483 123542802506642935790402225)
          ·
            refine ⟨92657101879982201842801669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123542802506642935790402225 92657101879982201842801669)
            ·
              refine ⟨17373206602496662845525313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92657101879982201842801669 17373206602496662845525313)
              ·
                refine ⟨13029904951872497134143985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17373206602496662845525313 13029904951872497134143985)
                ·
                  refine ⟨9772428713904372850607989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13029904951872497134143985 9772428713904372850607989)
                  ·
                    refine ⟨916165191928534954744499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9772428713904372850607989 916165191928534954744499)
                    ·
                      rfl

theorem cell23_5352676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_5352676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352676 prefixEnd_5352676 := by exact prefixLift 5352676
  have htrace : WordTrace (prefixWord ++ tailWord_5352676) baseStart_5352676 baseEnd_5352676 := by
    simpa [prefixWord, tailWord_5352676, baseEnd_5352676] using wordTrace_append hprefix tailTrace_5352676
  have hstable : (prefixWord ++ tailWord_5352676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352676).length < 2 ^ (prefixWord ++ tailWord_5352676).sum := by decide
  have hdescent : baseEnd_5352676 < baseStart_5352676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352686 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_5352686 : Nat := 118140960795 + 5352686 * 2 ^ 59
def prefixEnd_5352686 : Nat := 4983230072969 + 3 ^ 40 * 5352686 * 2
def baseEnd_5352686 : Nat := 2748500710592149825108451

theorem tailTrace_5352686 : CollatzResearch.WordTrace tailWord_5352686 prefixEnd_5352686 2748500710592149825108451 := by
  unfold tailWord_5352686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24403562135767532854179739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130152331390760175222291941 24403562135767532854179739)
  ·
    refine ⟨36605343203651299281269609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24403562135767532854179739 36605343203651299281269609)
    ·
      refine ⟨27454007402738474460952207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36605343203651299281269609 27454007402738474460952207)
      ·
        refine ⟨41181011104107711691428311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27454007402738474460952207 41181011104107711691428311)
        ·
          refine ⟨61771516656161567537142467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41181011104107711691428311 61771516656161567537142467)
          ·
            refine ⟨92657274984242351305713701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61771516656161567537142467 92657274984242351305713701)
            ·
              refine ⟨17373239059545440869821319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92657274984242351305713701 17373239059545440869821319)
              ·
                refine ⟨26059858589318161304731979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17373239059545440869821319 26059858589318161304731979)
                ·
                  refine ⟨39089787883977241957097969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26059858589318161304731979 39089787883977241957097969)
                  ·
                    refine ⟨29317340912982931467823477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39089787883977241957097969 29317340912982931467823477)
                    ·
                      refine ⟨2748500710592149825108451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29317340912982931467823477 2748500710592149825108451)
                      ·
                        rfl

theorem cell23_5352686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_5352686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352686 prefixEnd_5352686 := by exact prefixLift 5352686
  have htrace : WordTrace (prefixWord ++ tailWord_5352686) baseStart_5352686 baseEnd_5352686 := by
    simpa [prefixWord, tailWord_5352686, baseEnd_5352686] using wordTrace_append hprefix tailTrace_5352686
  have hstable : (prefixWord ++ tailWord_5352686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352686).length < 2 ^ (prefixWord ++ tailWord_5352686).sum := by decide
  have hdescent : baseEnd_5352686 < baseStart_5352686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352689 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_5352689 : Nat := 118140960795 + 5352689 * 2 ^ 59
def prefixEnd_5352689 : Nat := 4983230072969 + 3 ^ 40 * 5352689 * 2
def baseEnd_5352689 : Nat := 916167417011371104456979

theorem tailTrace_5352689 : CollatzResearch.WordTrace tailWord_5352689 prefixEnd_5352689 916167417011371104456979 := by
  unfold tailWord_5352689
  simp only [CollatzResearch.WordTrace]
  refine ⟨195228606505129394345797121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130152404336752929563864747 195228606505129394345797121)
  ·
    refine ⟨146421454878847045759347841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195228606505129394345797121 146421454878847045759347841)
    ·
      refine ⟨109816091159135284319510881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146421454878847045759347841 109816091159135284319510881)
      ·
        refine ⟨82362068369351463239633161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109816091159135284319510881 82362068369351463239633161)
        ·
          refine ⟨61771551277013597429724871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82362068369351463239633161 61771551277013597429724871)
          ·
            refine ⟨92657326915520396144587307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61771551277013597429724871 92657326915520396144587307)
            ·
              refine ⟨138985990373280594216880961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92657326915520396144587307 138985990373280594216880961)
              ·
                refine ⟨104239492779960445662660721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138985990373280594216880961 104239492779960445662660721)
                ·
                  refine ⟨78179619584970334246995541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104239492779960445662660721 78179619584970334246995541)
                  ·
                    refine ⟨916167417011371104456979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78179619584970334246995541 916167417011371104456979)
                    ·
                      rfl

theorem cell23_5352689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_5352689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352689 prefixEnd_5352689 := by exact prefixLift 5352689
  have htrace : WordTrace (prefixWord ++ tailWord_5352689) baseStart_5352689 baseEnd_5352689 := by
    simpa [prefixWord, tailWord_5352689, baseEnd_5352689] using wordTrace_append hprefix tailTrace_5352689
  have hstable : (prefixWord ++ tailWord_5352689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352689).length < 2 ^ (prefixWord ++ tailWord_5352689).sum := by decide
  have hdescent : baseEnd_5352689 < baseStart_5352689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352729 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_5352729 : Nat := 118140960795 + 5352729 * 2 ^ 59
def prefixEnd_5352729 : Nat := 4983230072969 + 3 ^ 40 * 5352729 * 2
def baseEnd_5352729 : Nat := 2748522790260293156870753

theorem tailTrace_5352729 : CollatzResearch.WordTrace tailWord_5352729 prefixEnd_5352729 2748522790260293156870753 := by
  unfold tailWord_5352729
  simp only [CollatzResearch.WordTrace]
  refine ⟨195230065424984481177253241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130153376949989654118168827 195230065424984481177253241)
  ·
    refine ⟨146422549068738360882939931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195230065424984481177253241 146422549068738360882939931)
    ·
      refine ⟨219633823603107541324409897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146422549068738360882939931 219633823603107541324409897)
      ·
        refine ⟨164725367702330655993307423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219633823603107541324409897 164725367702330655993307423)
        ·
          refine ⟨247088051553495983989961135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164725367702330655993307423 247088051553495983989961135)
          ·
            refine ⟨370632077330243975984941703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247088051553495983989961135 370632077330243975984941703)
            ·
              refine ⟨555948115995365963977412555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370632077330243975984941703 555948115995365963977412555)
              ·
                refine ⟨833922173993048945966118833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555948115995365963977412555 833922173993048945966118833)
                ·
                  refine ⟨625441630494786709474589125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833922173993048945966118833 625441630494786709474589125)
                  ·
                    refine ⟨117270305717772508026485461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625441630494786709474589125 117270305717772508026485461)
                    ·
                      refine ⟨2748522790260293156870753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117270305717772508026485461 2748522790260293156870753)
                      ·
                        rfl

theorem cell23_5352729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_5352729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352729 prefixEnd_5352729 := by exact prefixLift 5352729
  have htrace : WordTrace (prefixWord ++ tailWord_5352729) baseStart_5352729 baseEnd_5352729 := by
    simpa [prefixWord, tailWord_5352729, baseEnd_5352729] using wordTrace_append hprefix tailTrace_5352729
  have hstable : (prefixWord ++ tailWord_5352729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352729).length < 2 ^ (prefixWord ++ tailWord_5352729).sum := by decide
  have hdescent : baseEnd_5352729 < baseStart_5352729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352740 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_5352740 : Nat := 118140960795 + 5352740 * 2 ^ 59
def prefixEnd_5352740 : Nat := 4983230072969 + 3 ^ 40 * 5352740 * 2
def baseEnd_5352740 : Nat := 916176146182497537944401

theorem tailTrace_5352740 : CollatzResearch.WordTrace tailWord_5352740 prefixEnd_5352740 916176146182497537944401 := by
  unfold tailWord_5352740
  simp only [CollatzResearch.WordTrace]
  refine ⟨97615233313972315027951837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130153644418629753370602449 97615233313972315027951837)
  ·
    refine ⟨36605712492739618135481939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97615233313972315027951837 36605712492739618135481939)
    ·
      refine ⟨54908568739109427203222909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36605712492739618135481939 54908568739109427203222909)
      ·
        refine ⟨20590713277166035201208591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54908568739109427203222909 20590713277166035201208591)
        ·
          refine ⟨30886069915749052801812887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20590713277166035201208591 30886069915749052801812887)
          ·
            refine ⟨46329104873623579202719331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30886069915749052801812887 46329104873623579202719331)
            ·
              refine ⟨69493657310435368804078997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46329104873623579202719331 69493657310435368804078997)
              ·
                refine ⟨3257515186426657912691203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69493657310435368804078997 3257515186426657912691203)
                ·
                  refine ⟨4886272779639986869036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257515186426657912691203 4886272779639986869036805)
                  ·
                    refine ⟨916176146182497537944401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886272779639986869036805 916176146182497537944401)
                    ·
                      rfl

theorem cell23_5352740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_5352740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352740 prefixEnd_5352740 := by exact prefixLift 5352740
  have htrace : WordTrace (prefixWord ++ tailWord_5352740) baseStart_5352740 baseEnd_5352740 := by
    simpa [prefixWord, tailWord_5352740, baseEnd_5352740] using wordTrace_append hprefix tailTrace_5352740
  have hstable : (prefixWord ++ tailWord_5352740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352740).length < 2 ^ (prefixWord ++ tailWord_5352740).sum := by decide
  have hdescent : baseEnd_5352740 < baseStart_5352740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352773 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_5352773 : Nat := 118140960795 + 5352773 * 2 ^ 59
def prefixEnd_5352773 : Nat := 4983230072969 + 3 ^ 40 * 5352773 * 2
def baseEnd_5352773 : Nat := 2748545383409090984720551

theorem tailTrace_5352773 : CollatzResearch.WordTrace tailWord_5352773 prefixEnd_5352773 2748545383409090984720551 := by
  unfold tailWord_5352773
  simp only [CollatzResearch.WordTrace]
  refine ⟨195231670236825076691854973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130154446824550051127903315 195231670236825076691854973)
  ·
    refine ⟨73211876338809403759445615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195231670236825076691854973 73211876338809403759445615)
    ·
      refine ⟨109817814508214105639168423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73211876338809403759445615 109817814508214105639168423)
      ·
        refine ⟨164726721762321158458752635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109817814508214105639168423 164726721762321158458752635)
        ·
          refine ⟨247090082643481737688128953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164726721762321158458752635 247090082643481737688128953)
          ·
            refine ⟨185317561982611303266096715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247090082643481737688128953 185317561982611303266096715)
            ·
              refine ⟨277976342973916954899145073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185317561982611303266096715 277976342973916954899145073)
              ·
                refine ⟨208482257230437716174358805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277976342973916954899145073 208482257230437716174358805)
                ·
                  refine ⟨9772605807676767945673069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208482257230437716174358805 9772605807676767945673069)
                  ·
                    refine ⟨3664727177878787979627401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9772605807676767945673069 3664727177878787979627401)
                    ·
                      refine ⟨2748545383409090984720551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664727177878787979627401 2748545383409090984720551)
                      ·
                        rfl

theorem cell23_5352773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_5352773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352773 prefixEnd_5352773 := by exact prefixLift 5352773
  have htrace : WordTrace (prefixWord ++ tailWord_5352773) baseStart_5352773 baseEnd_5352773 := by
    simpa [prefixWord, tailWord_5352773, baseEnd_5352773] using wordTrace_append hprefix tailTrace_5352773
  have hstable : (prefixWord ++ tailWord_5352773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352773).length < 2 ^ (prefixWord ++ tailWord_5352773).sum := by decide
  have hdescent : baseEnd_5352773 < baseStart_5352773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352816 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_5352816 : Nat := 118140960795 + 5352816 * 2 ^ 59
def prefixEnd_5352816 : Nat := 4983230072969 + 3 ^ 40 * 5352816 * 2
def baseEnd_5352816 : Nat := 2748567463077234316482853

theorem tailTrace_5352816 : CollatzResearch.WordTrace tailWord_5352816 prefixEnd_5352816 2748567463077234316482853 := by
  unfold tailWord_5352816
  simp only [CollatzResearch.WordTrace]
  refine ⟨97616619287834647517835151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130155492383779530023780201 97616619287834647517835151)
  ·
    refine ⟨146424928931751971276752727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97616619287834647517835151 146424928931751971276752727)
    ·
      refine ⟨219637393397627956915129091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146424928931751971276752727 219637393397627956915129091)
      ·
        refine ⟨329456090096441935372693637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219637393397627956915129091 329456090096441935372693637)
        ·
          refine ⟨61773016893082862882380057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329456090096441935372693637 61773016893082862882380057)
          ·
            refine ⟨46329762669812147161785043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61773016893082862882380057 46329762669812147161785043)
            ·
              refine ⟨69494644004718220742677565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46329762669812147161785043 69494644004718220742677565)
              ·
                refine ⟨26060491501769332778504087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69494644004718220742677565 26060491501769332778504087)
                ·
                  refine ⟨39090737252653999167756131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26060491501769332778504087 39090737252653999167756131)
                  ·
                    refine ⟨58636105878980998751634197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39090737252653999167756131 58636105878980998751634197)
                    ·
                      refine ⟨2748567463077234316482853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58636105878980998751634197 2748567463077234316482853)
                      ·
                        rfl

theorem cell23_5352816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_5352816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352816 prefixEnd_5352816 := by exact prefixLift 5352816
  have htrace : WordTrace (prefixWord ++ tailWord_5352816) baseStart_5352816 baseEnd_5352816 := by
    simpa [prefixWord, tailWord_5352816, baseEnd_5352816] using wordTrace_append hprefix tailTrace_5352816
  have hstable : (prefixWord ++ tailWord_5352816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352816).length < 2 ^ (prefixWord ++ tailWord_5352816).sum := by decide
  have hdescent : baseEnd_5352816 < baseStart_5352816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352823 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_5352823 : Nat := 118140960795 + 5352823 * 2 ^ 59
def prefixEnd_5352823 : Nat := 4983230072969 + 3 ^ 40 * 5352823 * 2
def baseEnd_5352823 : Nat := 2748571057441815789095321

theorem tailTrace_5352823 : CollatzResearch.WordTrace tailWord_5352823 prefixEnd_5352823 2748571057441815789095321 := by
  unfold tailWord_5352823
  simp only [CollatzResearch.WordTrace]
  refine ⟨195233493886643935231175123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130155662591095956820783415 195233493886643935231175123)
  ·
    refine ⟨292850240829965902846762685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195233493886643935231175123 292850240829965902846762685)
    ·
      refine ⟨109818840311237213567536007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292850240829965902846762685 109818840311237213567536007)
      ·
        refine ⟨164728260466855820351304011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109818840311237213567536007 164728260466855820351304011)
        ·
          refine ⟨247092390700283730526956017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164728260466855820351304011 247092390700283730526956017)
          ·
            refine ⟨185319293025212797895217013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247092390700283730526956017 185319293025212797895217013)
            ·
              refine ⟨17373683721113699802676595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185319293025212797895217013 17373683721113699802676595)
              ·
                refine ⟨26060525581670549704014893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17373683721113699802676595 26060525581670549704014893)
                ·
                  refine ⟨9772697093126456139005585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26060525581670549704014893 9772697093126456139005585)
                  ·
                    refine ⟨7329522819844842104254189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9772697093126456139005585 7329522819844842104254189)
                    ·
                      refine ⟨2748571057441815789095321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7329522819844842104254189 2748571057441815789095321)
                      ·
                        rfl

theorem cell23_5352823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_5352823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352823 prefixEnd_5352823 := by exact prefixLift 5352823
  have htrace : WordTrace (prefixWord ++ tailWord_5352823) baseStart_5352823 baseEnd_5352823 := by
    simpa [prefixWord, tailWord_5352823, baseEnd_5352823] using wordTrace_append hprefix tailTrace_5352823
  have hstable : (prefixWord ++ tailWord_5352823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352823).length < 2 ^ (prefixWord ++ tailWord_5352823).sum := by decide
  have hdescent : baseEnd_5352823 < baseStart_5352823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352834 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5352834 : Nat := 118140960795 + 5352834 * 2 ^ 59
def prefixEnd_5352834 : Nat := 4983230072969 + 3 ^ 40 * 5352834 * 2
def baseEnd_5352834 : Nat := 916192235243005082019257

theorem tailTrace_5352834 : CollatzResearch.WordTrace tailWord_5352834 prefixEnd_5352834 916192235243005082019257 := by
  unfold tailWord_5352834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48808473772401021027456389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130155930059736056073217037 48808473772401021027456389)
  ·
    refine ⟨9151588832325191442648073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48808473772401021027456389 9151588832325191442648073)
    ·
      refine ⟨6863691624243893581986055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9151588832325191442648073 6863691624243893581986055)
      ·
        refine ⟨10295537436365840372979083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6863691624243893581986055 10295537436365840372979083)
        ·
          refine ⟨15443306154548760559468625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10295537436365840372979083 15443306154548760559468625)
          ·
            refine ⟨11582479615911570419601469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15443306154548760559468625 11582479615911570419601469)
            ·
              refine ⟨4343429855966838907350551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11582479615911570419601469 4343429855966838907350551)
              ·
                refine ⟨6515144783950258361025827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343429855966838907350551 6515144783950258361025827)
                ·
                  refine ⟨9772717175925387541538741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6515144783950258361025827 9772717175925387541538741)
                  ·
                    refine ⟨916192235243005082019257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9772717175925387541538741 916192235243005082019257)
                    ·
                      rfl

theorem cell23_5352834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5352834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352834 prefixEnd_5352834 := by exact prefixLift 5352834
  have htrace : WordTrace (prefixWord ++ tailWord_5352834) baseStart_5352834 baseEnd_5352834 := by
    simpa [prefixWord, tailWord_5352834, baseEnd_5352834] using wordTrace_append hprefix tailTrace_5352834
  have hstable : (prefixWord ++ tailWord_5352834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352834).length < 2 ^ (prefixWord ++ tailWord_5352834).sum := by decide
  have hdescent : baseEnd_5352834 < baseStart_5352834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352840 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_5352840 : Nat := 118140960795 + 5352840 * 2 ^ 59
def prefixEnd_5352840 : Nat := 4983230072969 + 3 ^ 40 * 5352840 * 2
def baseEnd_5352840 : Nat := 2748579786612942222582743

theorem tailTrace_5352840 : CollatzResearch.WordTrace tailWord_5352840 prefixEnd_5352840 2748579786612942222582743 := by
  unfold tailWord_5352840
  simp only [CollatzResearch.WordTrace]
  refine ⟨97617056963791173567271987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130156075951721564756362649 97617056963791173567271987)
  ·
    refine ⟨146425585445686760350907981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97617056963791173567271987 146425585445686760350907981)
    ·
      refine ⟨54909594542132535131590493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146425585445686760350907981 54909594542132535131590493)
      ·
        refine ⟨20591097953299700674346435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54909594542132535131590493 20591097953299700674346435)
        ·
          refine ⟨30886646929949551011519653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20591097953299700674346435 30886646929949551011519653)
          ·
            refine ⟨5791246299365540814659935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30886646929949551011519653 5791246299365540814659935)
            ·
              refine ⟨8686869449048311221989903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791246299365540814659935 8686869449048311221989903)
              ·
                refine ⟨13030304173572466832984855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8686869449048311221989903 13030304173572466832984855)
                ·
                  refine ⟨19545456260358700249477283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13030304173572466832984855 19545456260358700249477283)
                  ·
                    refine ⟨29318184390538050374215925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19545456260358700249477283 29318184390538050374215925)
                    ·
                      refine ⟨2748579786612942222582743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29318184390538050374215925 2748579786612942222582743)
                      ·
                        rfl

theorem cell23_5352840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_5352840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352840 prefixEnd_5352840 := by exact prefixLift 5352840
  have htrace : WordTrace (prefixWord ++ tailWord_5352840) baseStart_5352840 baseEnd_5352840 := by
    simpa [prefixWord, tailWord_5352840, baseEnd_5352840] using wordTrace_append hprefix tailTrace_5352840
  have hstable : (prefixWord ++ tailWord_5352840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352840).length < 2 ^ (prefixWord ++ tailWord_5352840).sum := by decide
  have hdescent : baseEnd_5352840 < baseStart_5352840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352910 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_5352910 : Nat := 118140960795 + 5352910 * 2 ^ 59
def prefixEnd_5352910 : Nat := 4983230072969 + 3 ^ 40 * 5352910 * 2
def baseEnd_5352910 : Nat := 2748615730258756948707421

theorem tailTrace_5352910 : CollatzResearch.WordTrace tailWord_5352910 prefixEnd_5352910 2748615730258756948707421 := by
  unfold tailWord_5352910
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404583379666093636199023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130157778024885832726394789 24404583379666093636199023)
  ·
    refine ⟨36606875069499140454298535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24404583379666093636199023 36606875069499140454298535)
    ·
      refine ⟨54910312604248710681447803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36606875069499140454298535 54910312604248710681447803)
      ·
        refine ⟨82365468906373066022171705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54910312604248710681447803 82365468906373066022171705)
        ·
          refine ⟨61774101679779799516628779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82365468906373066022171705 61774101679779799516628779)
          ·
            refine ⟨92661152519669699274943169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61774101679779799516628779 92661152519669699274943169)
            ·
              refine ⟨69495864389752274456207377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92661152519669699274943169 69495864389752274456207377)
              ·
                refine ⟨52121898292314205842155533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69495864389752274456207377 52121898292314205842155533)
                ·
                  refine ⟨19545711859617827190808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52121898292314205842155533 19545711859617827190808325)
                  ·
                    refine ⟨3664820973678342598276561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19545711859617827190808325 3664820973678342598276561)
                    ·
                      refine ⟨2748615730258756948707421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3664820973678342598276561 2748615730258756948707421)
                      ·
                        rfl

theorem cell23_5352910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_5352910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352910 prefixEnd_5352910 := by exact prefixLift 5352910
  have htrace : WordTrace (prefixWord ++ tailWord_5352910) baseStart_5352910 baseEnd_5352910 := by
    simpa [prefixWord, tailWord_5352910, baseEnd_5352910] using wordTrace_append hprefix tailTrace_5352910
  have hstable : (prefixWord ++ tailWord_5352910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352910).length < 2 ^ (prefixWord ++ tailWord_5352910).sum := by decide
  have hdescent : baseEnd_5352910 < baseStart_5352910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5352943 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_5352943 : Nat := 118140960795 + 5352943 * 2 ^ 59
def prefixEnd_5352943 : Nat := 4983230072969 + 3 ^ 40 * 5352943 * 2
def baseEnd_5352943 : Nat := 2748632675120355319594769

theorem tailTrace_5352943 : CollatzResearch.WordTrace tailWord_5352943 prefixEnd_5352943 2748632675120355319594769 := by
  unfold tailWord_5352943
  simp only [CollatzResearch.WordTrace]
  refine ⟨195237870646209195725543483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130158580430806130483695655 195237870646209195725543483)
  ·
    refine ⟨292856805969313793588315225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195237870646209195725543483 292856805969313793588315225)
    ·
      refine ⟨219642604476985345191236419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292856805969313793588315225 219642604476985345191236419)
      ·
        refine ⟨329463906715478017786854629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219642604476985345191236419 329463906715478017786854629)
        ·
          refine ⟨61774482509152128335035243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329463906715478017786854629 61774482509152128335035243)
          ·
            refine ⟨92661723763728192502552865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61774482509152128335035243 92661723763728192502552865)
            ·
              refine ⟨69496292822796144376914649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92661723763728192502552865 69496292822796144376914649)
              ·
                refine ⟨52122219617097108282685987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69496292822796144376914649 52122219617097108282685987)
                ·
                  refine ⟨78183329425645662424028981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52122219617097108282685987 78183329425645662424028981)
                  ·
                    refine ⟨7329687133654280852252717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78183329425645662424028981 7329687133654280852252717)
                    ·
                      refine ⟨2748632675120355319594769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7329687133654280852252717 2748632675120355319594769)
                      ·
                        rfl

theorem cell23_5352943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_5352943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5352943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5352943 prefixEnd_5352943 := by exact prefixLift 5352943
  have htrace : WordTrace (prefixWord ++ tailWord_5352943) baseStart_5352943 baseEnd_5352943 := by
    simpa [prefixWord, tailWord_5352943, baseEnd_5352943] using wordTrace_append hprefix tailTrace_5352943
  have hstable : (prefixWord ++ tailWord_5352943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5352943).length < 2 ^ (prefixWord ++ tailWord_5352943).sum := by decide
  have hdescent : baseEnd_5352943 < baseStart_5352943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5352943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353118 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_5353118 : Nat := 118140960795 + 5353118 * 2 ^ 59
def prefixEnd_5353118 : Nat := 4983230072969 + 3 ^ 40 * 5353118 * 2
def baseEnd_5353118 : Nat := 2748722534234892134906465

theorem tailTrace_5353118 : CollatzResearch.WordTrace tailWord_5353118 prefixEnd_5353118 2748722534234892134906465 := by
  unfold tailWord_5353118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24405531677571900076645501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130162835613716800408776005 24405531677571900076645501)
  ·
    refine ⟨9152074379089462528742063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24405531677571900076645501 9152074379089462528742063)
    ·
      refine ⟨13728111568634193793113095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9152074379089462528742063 13728111568634193793113095)
      ·
        refine ⟨20592167352951290689669643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13728111568634193793113095 20592167352951290689669643)
        ·
          refine ⟨30888251029426936034504465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20592167352951290689669643 30888251029426936034504465)
          ·
            refine ⟨23166188272070202025878349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30888251029426936034504465 23166188272070202025878349)
            ·
              refine ⟨8687320602026325759704381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23166188272070202025878349 8687320602026325759704381)
              ·
                refine ⟨3257745225759872159889143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8687320602026325759704381 3257745225759872159889143)
                ·
                  refine ⟨4886617838639808239833715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257745225759872159889143 4886617838639808239833715)
                  ·
                    refine ⟨7329926757959712359750573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4886617838639808239833715 7329926757959712359750573)
                    ·
                      refine ⟨2748722534234892134906465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7329926757959712359750573 2748722534234892134906465)
                      ·
                        rfl

theorem cell23_5353118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_5353118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353118 prefixEnd_5353118 := by exact prefixLift 5353118
  have htrace : WordTrace (prefixWord ++ tailWord_5353118) baseStart_5353118 baseEnd_5353118 := by
    simpa [prefixWord, tailWord_5353118, baseEnd_5353118] using wordTrace_append hprefix tailTrace_5353118
  have hstable : (prefixWord ++ tailWord_5353118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353118).length < 2 ^ (prefixWord ++ tailWord_5353118).sum := by decide
  have hdescent : baseEnd_5353118 < baseStart_5353118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353158 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5353158 : Nat := 118140960795 + 5353158 * 2 ^ 59
def prefixEnd_5353158 : Nat := 4983230072969 + 3 ^ 40 * 5353158 * 2
def baseEnd_5353158 : Nat := 2748743073461071978406281

theorem tailTrace_5353158 : CollatzResearch.WordTrace tailWord_5353158 prefixEnd_5353158 2748743073461071978406281 := by
  unfold tailWord_5353158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101428510638446482644379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130163808226953524963080085 6101428510638446482644379)
  ·
    refine ⟨9152142765957669723966569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6101428510638446482644379 9152142765957669723966569)
    ·
      refine ⟨6864107074468252292974927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9152142765957669723966569 6864107074468252292974927)
      ·
        refine ⟨10296160611702378439462391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864107074468252292974927 10296160611702378439462391)
        ·
          refine ⟨15444240917553567659193587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10296160611702378439462391 15444240917553567659193587)
          ·
            refine ⟨23166361376330351488790381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15444240917553567659193587 23166361376330351488790381)
            ·
              refine ⟨8687385516123881808296393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23166361376330351488790381 8687385516123881808296393)
              ·
                refine ⟨6515539137092911356222295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8687385516123881808296393 6515539137092911356222295)
                ·
                  refine ⟨9773308705639367034333443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6515539137092911356222295 9773308705639367034333443)
                  ·
                    refine ⟨14659963058459050551500165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9773308705639367034333443 14659963058459050551500165)
                    ·
                      refine ⟨2748743073461071978406281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14659963058459050551500165 2748743073461071978406281)
                      ·
                        rfl

theorem cell23_5353158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5353158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353158 prefixEnd_5353158 := by exact prefixLift 5353158
  have htrace : WordTrace (prefixWord ++ tailWord_5353158) baseStart_5353158 baseEnd_5353158 := by
    simpa [prefixWord, tailWord_5353158, baseEnd_5353158] using wordTrace_append hprefix tailTrace_5353158
  have hstable : (prefixWord ++ tailWord_5353158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353158).length < 2 ^ (prefixWord ++ tailWord_5353158).sum := by decide
  have hdescent : baseEnd_5353158 < baseStart_5353158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353184 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2]
def baseStart_5353184 : Nat := 118140960795 + 5353184 * 2 ^ 59
def prefixEnd_5353184 : Nat := 4983230072969 + 3 ^ 40 * 5353184 * 2
def baseEnd_5353184 : Nat := 2748756423958088876681161

theorem tailTrace_5353184 : CollatzResearch.WordTrace tailWord_5353184 prefixEnd_5353184 2748756423958088876681161 := by
  unfold tailWord_5353184
  simp only [CollatzResearch.WordTrace]
  refine ⟨97623330319168046942533303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130164440425557395923377737 97623330319168046942533303)
  ·
    refine ⟨146434995478752070413799955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97623330319168046942533303 146434995478752070413799955)
    ·
      refine ⟨219652493218128105620699933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146434995478752070413799955 219652493218128105620699933)
      ·
        refine ⟨82369684956798039607762475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219652493218128105620699933 82369684956798039607762475)
        ·
          refine ⟨123554527435197059411643713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82369684956798039607762475 123554527435197059411643713)
          ·
            refine ⟨92665895576397794558732785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123554527435197059411643713 92665895576397794558732785)
            ·
              refine ⟨69499421682298345919049589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92665895576397794558732785 69499421682298345919049589)
              ·
                refine ⟨6515570782715469929910899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69499421682298345919049589 6515570782715469929910899)
                ·
                  refine ⟨9773356174073204894866349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6515570782715469929910899 9773356174073204894866349)
                  ·
                    refine ⟨3665008565277451835574881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9773356174073204894866349 3665008565277451835574881)
                    ·
                      refine ⟨2748756423958088876681161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665008565277451835574881 2748756423958088876681161)
                      ·
                        rfl

theorem cell23_5353184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_5353184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353184 prefixEnd_5353184 := by exact prefixLift 5353184
  have htrace : WordTrace (prefixWord ++ tailWord_5353184) baseStart_5353184 baseEnd_5353184 := by
    simpa [prefixWord, tailWord_5353184, baseEnd_5353184] using wordTrace_append hprefix tailTrace_5353184
  have hstable : (prefixWord ++ tailWord_5353184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353184).length < 2 ^ (prefixWord ++ tailWord_5353184).sum := by decide
  have hdescent : baseEnd_5353184 < baseStart_5353184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353197 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5353197 : Nat := 118140960795 + 5353197 * 2 ^ 59
def prefixEnd_5353197 : Nat := 4983230072969 + 3 ^ 40 * 5353197 * 2
def baseEnd_5353197 : Nat := 2748763099206597325818601

theorem tailTrace_5353197 : CollatzResearch.WordTrace tailWord_5353197 prefixEnd_5353197 2748763099206597325818601 := by
  unfold tailWord_5353197
  simp only [CollatzResearch.WordTrace]
  refine ⟨195247134787288997105289845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130164756524859331403526563 195247134787288997105289845)
  ·
    refine ⟨18304418886308343478620923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195247134787288997105289845 18304418886308343478620923)
    ·
      refine ⟨27456628329462515217931385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18304418886308343478620923 27456628329462515217931385)
      ·
        refine ⟨20592471247096886413448539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27456628329462515217931385 20592471247096886413448539)
        ·
          refine ⟨30888706870645329620172809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20592471247096886413448539 30888706870645329620172809)
          ·
            refine ⟨23166530152983997215129607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30888706870645329620172809 23166530152983997215129607)
            ·
              refine ⟨34749795229475995822694411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23166530152983997215129607 34749795229475995822694411)
              ·
                refine ⟨52124692844213993734041617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34749795229475995822694411 52124692844213993734041617)
                ·
                  refine ⟨39093519633160495300531213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52124692844213993734041617 39093519633160495300531213)
                  ·
                    refine ⟨14660069862435185737699205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39093519633160495300531213 14660069862435185737699205)
                    ·
                      refine ⟨2748763099206597325818601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14660069862435185737699205 2748763099206597325818601)
                      ·
                        rfl

theorem cell23_5353197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5353197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353197 prefixEnd_5353197 := by exact prefixLift 5353197
  have htrace : WordTrace (prefixWord ++ tailWord_5353197) baseStart_5353197 baseEnd_5353197 := by
    simpa [prefixWord, tailWord_5353197, baseEnd_5353197] using wordTrace_append hprefix tailTrace_5353197
  have hstable : (prefixWord ++ tailWord_5353197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353197).length < 2 ^ (prefixWord ++ tailWord_5353197).sum := by decide
  have hdescent : baseEnd_5353197 < baseStart_5353197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353200 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_5353200 : Nat := 118140960795 + 5353200 * 2 ^ 59
def prefixEnd_5353200 : Nat := 4983230072969 + 3 ^ 40 * 5353200 * 2
def baseEnd_5353200 : Nat := 2748764639648560814081087

theorem tailTrace_5353200 : CollatzResearch.WordTrace tailWord_5353200 prefixEnd_5353200 2748764639648560814081087 := by
  unfold tailWord_5353200
  simp only [CollatzResearch.WordTrace]
  refine ⟨97623622103139064308824527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130164829470852085745099369 97623622103139064308824527)
  ·
    refine ⟨146435433154708596463236791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97623622103139064308824527 146435433154708596463236791)
    ·
      refine ⟨219653149732062894694855187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146435433154708596463236791 219653149732062894694855187)
      ·
        refine ⟨329479724598094342042282781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219653149732062894694855187 329479724598094342042282781)
        ·
          refine ⟨123554896724285378265856043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329479724598094342042282781 123554896724285378265856043)
          ·
            refine ⟨185332345086428067398784065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123554896724285378265856043 185332345086428067398784065)
            ·
              refine ⟨138999258814821050549088049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185332345086428067398784065 138999258814821050549088049)
              ·
                refine ⟨104249444111115787911816037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138999258814821050549088049 104249444111115787911816037)
                ·
                  refine ⟨19546770770834210233465507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104249444111115787911816037 19546770770834210233465507)
                  ·
                    refine ⟨29320156156251315350198261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19546770770834210233465507 29320156156251315350198261)
                    ·
                      refine ⟨2748764639648560814081087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29320156156251315350198261 2748764639648560814081087)
                      ·
                        rfl

theorem cell23_5353200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_5353200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353200 prefixEnd_5353200 := by exact prefixLift 5353200
  have htrace : WordTrace (prefixWord ++ tailWord_5353200) baseStart_5353200 baseEnd_5353200 := by
    simpa [prefixWord, tailWord_5353200, baseEnd_5353200] using wordTrace_append hprefix tailTrace_5353200
  have hstable : (prefixWord ++ tailWord_5353200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353200).length < 2 ^ (prefixWord ++ tailWord_5353200).sum := by decide
  have hdescent : baseEnd_5353200 < baseStart_5353200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353229 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5353229 : Nat := 118140960795 + 5353229 * 2 ^ 59
def prefixEnd_5353229 : Nat := 4983230072969 + 3 ^ 40 * 5353229 * 2
def baseEnd_5353229 : Nat := 2748779530587541200618455

theorem tailTrace_5353229 : CollatzResearch.WordTrace tailWord_5353229 prefixEnd_5353229 2748779530587541200618455 := by
  unfold tailWord_5353229
  simp only [CollatzResearch.WordTrace]
  refine ⟨195248301923173066570454741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130165534615448711046969827 195248301923173066570454741)
  ·
    refine ⟨4576132076324368747745033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 195248301923173066570454741 4576132076324368747745033)
    ·
      refine ⟨3432099057243276560808775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4576132076324368747745033 3432099057243276560808775)
      ·
        refine ⟨5148148585864914841213163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432099057243276560808775 5148148585864914841213163)
        ·
          refine ⟨7722222878797372261819745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148148585864914841213163 7722222878797372261819745)
          ·
            refine ⟨5791667159098029196364809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722222878797372261819745 5791667159098029196364809)
            ·
              refine ⟨4343750369323521897273607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5791667159098029196364809 4343750369323521897273607)
              ·
                refine ⟨6515625553985282845910411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343750369323521897273607 6515625553985282845910411)
                ·
                  refine ⟨9773438330977924268865617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6515625553985282845910411 9773438330977924268865617)
                  ·
                    refine ⟨7330078748233443201649213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9773438330977924268865617 7330078748233443201649213)
                    ·
                      refine ⟨2748779530587541200618455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330078748233443201649213 2748779530587541200618455)
                      ·
                        rfl

theorem cell23_5353229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5353229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353229 prefixEnd_5353229 := by exact prefixLift 5353229
  have htrace : WordTrace (prefixWord ++ tailWord_5353229) baseStart_5353229 baseEnd_5353229 := by
    simpa [prefixWord, tailWord_5353229, baseEnd_5353229] using wordTrace_append hprefix tailTrace_5353229
  have hstable : (prefixWord ++ tailWord_5353229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353229).length < 2 ^ (prefixWord ++ tailWord_5353229).sum := by decide
  have hdescent : baseEnd_5353229 < baseStart_5353229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353247 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_5353247 : Nat := 118140960795 + 5353247 * 2 ^ 59
def prefixEnd_5353247 : Nat := 4983230072969 + 3 ^ 40 * 5353247 * 2
def baseEnd_5353247 : Nat := 2748788773239322130193371

theorem tailTrace_5353247 : CollatzResearch.WordTrace tailWord_5353247 prefixEnd_5353247 2748788773239322130193371 := by
  unfold tailWord_5353247
  simp only [CollatzResearch.WordTrace]
  refine ⟨195248958437107855644609995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130165972291405237096406663 195248958437107855644609995)
  ·
    refine ⟨292873437655661783466914993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195248958437107855644609995 292873437655661783466914993)
    ·
      refine ⟨219655078241746337600186245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292873437655661783466914993 219655078241746337600186245)
      ·
        refine ⟨41185327170327438300034921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219655078241746337600186245 41185327170327438300034921)
        ·
          refine ⟨30888995377745578725026191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41185327170327438300034921 30888995377745578725026191)
          ·
            refine ⟨46333493066618368087539287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30888995377745578725026191 46333493066618368087539287)
            ·
              refine ⟨69500239599927552131308931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46333493066618368087539287 69500239599927552131308931)
              ·
                refine ⟨104250359399891328196963397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69500239599927552131308931 104250359399891328196963397)
                ·
                  refine ⟨19546942387479624036930637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104250359399891328196963397 19546942387479624036930637)
                  ·
                    refine ⟨7330103395304859013848989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19546942387479624036930637 7330103395304859013848989)
                    ·
                      refine ⟨2748788773239322130193371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330103395304859013848989 2748788773239322130193371)
                      ·
                        rfl

theorem cell23_5353247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_5353247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353247 prefixEnd_5353247 := by exact prefixLift 5353247
  have htrace : WordTrace (prefixWord ++ tailWord_5353247) baseStart_5353247 baseEnd_5353247 := by
    simpa [prefixWord, tailWord_5353247, baseEnd_5353247] using wordTrace_append hprefix tailTrace_5353247
  have hstable : (prefixWord ++ tailWord_5353247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353247).length < 2 ^ (prefixWord ++ tailWord_5353247).sum := by decide
  have hdescent : baseEnd_5353247 < baseStart_5353247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353287 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_5353287 : Nat := 118140960795 + 5353287 * 2 ^ 59
def prefixEnd_5353287 : Nat := 4983230072969 + 3 ^ 40 * 5353287 * 2
def baseEnd_5353287 : Nat := 2748809312465501973693187

theorem tailTrace_5353287 : CollatzResearch.WordTrace tailWord_5353287 prefixEnd_5353287 2748809312465501973693187 := by
  unfold tailWord_5353287
  simp only [CollatzResearch.WordTrace]
  refine ⟨195250417356962942476066115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130166944904641961650710743 195250417356962942476066115)
  ·
    refine ⟨292875626035444413714099173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195250417356962942476066115 292875626035444413714099173)
    ·
      refine ⟨54914179881645827571393595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292875626035444413714099173 54914179881645827571393595)
      ·
        refine ⟨82371269822468741357090393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54914179881645827571393595 82371269822468741357090393)
        ·
          refine ⟨61778452366851556017817795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82371269822468741357090393 61778452366851556017817795)
          ·
            refine ⟨92667678550277334026726693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61778452366851556017817795 92667678550277334026726693)
            ·
              refine ⟨17375189728177000130011255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92667678550277334026726693 17375189728177000130011255)
              ·
                refine ⟨26062784592265500195016883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17375189728177000130011255 26062784592265500195016883)
                ·
                  refine ⟨39094176888398250292525325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26062784592265500195016883 39094176888398250292525325)
                  ·
                    refine ⟨14660316333149343859696997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39094176888398250292525325 14660316333149343859696997)
                    ·
                      refine ⟨2748809312465501973693187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14660316333149343859696997 2748809312465501973693187)
                      ·
                        rfl

theorem cell23_5353287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_5353287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353287 prefixEnd_5353287 := by exact prefixLift 5353287
  have htrace : WordTrace (prefixWord ++ tailWord_5353287) baseStart_5353287 baseEnd_5353287 := by
    simpa [prefixWord, tailWord_5353287, baseEnd_5353287] using wordTrace_append hprefix tailTrace_5353287
  have hstable : (prefixWord ++ tailWord_5353287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353287).length < 2 ^ (prefixWord ++ tailWord_5353287).sum := by decide
  have hdescent : baseEnd_5353287 < baseStart_5353287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353405 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_5353405 : Nat := 118140960795 + 5353405 * 2 ^ 59
def prefixEnd_5353405 : Nat := 4983230072969 + 3 ^ 40 * 5353405 * 2
def baseEnd_5353405 : Nat := 2748869903182732512017645

theorem tailTrace_5353405 : CollatzResearch.WordTrace tailWord_5353405 prefixEnd_5353405 2748869903182732512017645 := by
  unfold tailWord_5353405
  simp only [CollatzResearch.WordTrace]
  refine ⟨195254721170535448628861669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130169814113690299085907779 195254721170535448628861669)
  ·
    refine ⟨36610260219475396617911563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195254721170535448628861669 36610260219475396617911563)
    ·
      refine ⟨54915390329213094926867345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36610260219475396617911563 54915390329213094926867345)
      ·
        refine ⟨41186542746909821195150509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54915390329213094926867345 41186542746909821195150509)
        ·
          refine ⟨15444953530091182948181441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41186542746909821195150509 15444953530091182948181441)
          ·
            refine ⟨11583715147568387211136081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15444953530091182948181441 11583715147568387211136081)
            ·
              refine ⟨8687786360676290408352061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11583715147568387211136081 8687786360676290408352061)
              ·
                refine ⟨3257919885253608903132023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8687786360676290408352061 3257919885253608903132023)
                ·
                  refine ⟨4886879827880413354698035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257919885253608903132023 4886879827880413354698035)
                  ·
                    refine ⟨7330319741820620032047053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4886879827880413354698035 7330319741820620032047053)
                    ·
                      refine ⟨2748869903182732512017645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330319741820620032047053 2748869903182732512017645)
                      ·
                        rfl

theorem cell23_5353405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_5353405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353405 prefixEnd_5353405 := by exact prefixLift 5353405
  have htrace : WordTrace (prefixWord ++ tailWord_5353405) baseStart_5353405 baseEnd_5353405 := by
    simpa [prefixWord, tailWord_5353405, baseEnd_5353405] using wordTrace_append hprefix tailTrace_5353405
  have hstable : (prefixWord ++ tailWord_5353405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353405).length < 2 ^ (prefixWord ++ tailWord_5353405).sum := by decide
  have hdescent : baseEnd_5353405 < baseStart_5353405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353484 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5353484 : Nat := 118140960795 + 5353484 * 2 ^ 59
def prefixEnd_5353484 : Nat := 4983230072969 + 3 ^ 40 * 5353484 * 2
def baseEnd_5353484 : Nat := 2748910468154437702929781

theorem tailTrace_5353484 : CollatzResearch.WordTrace tailWord_5353484 prefixEnd_5353484 2748910468154437702929781 := by
  unfold tailWord_5353484
  simp only [CollatzResearch.WordTrace]
  refine ⟨97628801268624622560493753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130171735024832830080658337 97628801268624622560493753)
  ·
    refine ⟨73221600951468466920370315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97628801268624622560493753 73221600951468466920370315)
    ·
      refine ⟨109832401427202700380555473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73221600951468466920370315 109832401427202700380555473)
      ·
        refine ⟨82374301070402025285416605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109832401427202700380555473 82374301070402025285416605)
        ·
          refine ⟨30890362901400759482031227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82374301070402025285416605 30890362901400759482031227)
          ·
            refine ⟨46335544352101139223046841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30890362901400759482031227 46335544352101139223046841)
            ·
              refine ⟨34751658264075854417285131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46335544352101139223046841 34751658264075854417285131)
              ·
                refine ⟨52127487396113781625927697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34751658264075854417285131 52127487396113781625927697)
                ·
                  refine ⟨39095615547085336219445773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52127487396113781625927697 39095615547085336219445773)
                  ·
                    refine ⟨14660855830157001082292165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39095615547085336219445773 14660855830157001082292165)
                    ·
                      refine ⟨2748910468154437702929781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14660855830157001082292165 2748910468154437702929781)
                      ·
                        rfl

theorem cell23_5353484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5353484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353484 prefixEnd_5353484 := by exact prefixLift 5353484
  have htrace : WordTrace (prefixWord ++ tailWord_5353484) baseStart_5353484 baseEnd_5353484 := by
    simpa [prefixWord, tailWord_5353484, baseEnd_5353484] using wordTrace_append hprefix tailTrace_5353484
  have hstable : (prefixWord ++ tailWord_5353484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353484).length < 2 ^ (prefixWord ++ tailWord_5353484).sum := by decide
  have hdescent : baseEnd_5353484 < baseStart_5353484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353485 : List Nat := [1, 7, 1, 2, 1, 1, 2, 8]
def baseStart_5353485 : Nat := 118140960795 + 5353485 * 2 ^ 59
def prefixEnd_5353485 : Nat := 4983230072969 + 3 ^ 40 * 5353485 * 2
def baseEnd_5353485 : Nat := 101811517838336748111751

theorem tailTrace_5353485 : CollatzResearch.WordTrace tailWord_5353485 prefixEnd_5353485 101811517838336748111751 := by
  unfold tailWord_5353485
  simp only [CollatzResearch.WordTrace]
  refine ⟨195257639010245622291773909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130171759340163748194515939 195257639010245622291773909)
  ·
    refine ⟨4576350914302631772463451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 195257639010245622291773909 4576350914302631772463451)
    ·
      refine ⟨6864526371453947658695177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576350914302631772463451 6864526371453947658695177)
      ·
        refine ⟨5148394778590460744021383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6864526371453947658695177 5148394778590460744021383)
        ·
          refine ⟨7722592167885691116032075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148394778590460744021383 7722592167885691116032075)
          ·
            refine ⟨11583888251828536674048113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722592167885691116032075 11583888251828536674048113)
            ·
              refine ⟨8687916188871402505536085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11583888251828536674048113 8687916188871402505536085)
              ·
                refine ⟨101811517838336748111751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8687916188871402505536085 101811517838336748111751)
                ·
                  rfl

theorem cell23_5353485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 8].length) (baseStart_5353485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353485 prefixEnd_5353485 := by exact prefixLift 5353485
  have htrace : WordTrace (prefixWord ++ tailWord_5353485) baseStart_5353485 baseEnd_5353485 := by
    simpa [prefixWord, tailWord_5353485, baseEnd_5353485] using wordTrace_append hprefix tailTrace_5353485
  have hstable : (prefixWord ++ tailWord_5353485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353485).length < 2 ^ (prefixWord ++ tailWord_5353485).sum := by decide
  have hdescent : baseEnd_5353485 < baseStart_5353485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353495 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5353495 : Nat := 118140960795 + 5353495 * 2 ^ 59
def prefixEnd_5353495 : Nat := 4983230072969 + 3 ^ 40 * 5353495 * 2
def baseEnd_5353495 : Nat := 2748916116441637159892231

theorem tailTrace_5353495 : CollatzResearch.WordTrace tailWord_5353495 prefixEnd_5353495 2748916116441637159892231 := by
  unfold tailWord_5353495
  simp only [CollatzResearch.WordTrace]
  refine ⟨195258003740209393999637939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130172002493472929333091959 195258003740209393999637939)
  ·
    refine ⟨292887005610314090999456909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195258003740209393999637939 292887005610314090999456909)
    ·
      refine ⟨109832627103867784124796341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292887005610314090999456909 109832627103867784124796341)
      ·
        refine ⟨10296808790987604761699657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109832627103867784124796341 10296808790987604761699657)
        ·
          refine ⟨7722606593240703571274743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10296808790987604761699657 7722606593240703571274743)
          ·
            refine ⟨11583909889861055356912115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722606593240703571274743 11583909889861055356912115)
            ·
              refine ⟨17375864834791583035368173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11583909889861055356912115 17375864834791583035368173)
              ·
                refine ⟨6515949313046843638263065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17375864834791583035368173 6515949313046843638263065)
                ·
                  refine ⟨4886961984785132728697299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6515949313046843638263065 4886961984785132728697299)
                  ·
                    refine ⟨7330442977177699093045949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4886961984785132728697299 7330442977177699093045949)
                    ·
                      refine ⟨2748916116441637159892231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330442977177699093045949 2748916116441637159892231)
                      ·
                        rfl

theorem cell23_5353495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5353495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353495 prefixEnd_5353495 := by exact prefixLift 5353495
  have htrace : WordTrace (prefixWord ++ tailWord_5353495) baseStart_5353495 baseEnd_5353495 := by
    simpa [prefixWord, tailWord_5353495, baseEnd_5353495] using wordTrace_append hprefix tailTrace_5353495
  have hstable : (prefixWord ++ tailWord_5353495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353495).length < 2 ^ (prefixWord ++ tailWord_5353495).sum := by decide
  have hdescent : baseEnd_5353495 < baseStart_5353495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353518 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5353518 : Nat := 118140960795 + 5353518 * 2 ^ 59
def prefixEnd_5353518 : Nat := 4983230072969 + 3 ^ 40 * 5353518 * 2
def baseEnd_5353518 : Nat := 2748927926496690569904625

theorem tailTrace_5353518 : CollatzResearch.WordTrace tailWord_5353518 prefixEnd_5353518 2748927926496690569904625 := by
  unfold tailWord_5353518
  simp only [CollatzResearch.WordTrace]
  refine ⟨24407355327390758615965651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130172561746084045951816805 24407355327390758615965651)
  ·
    refine ⟨36611032991086137923948477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24407355327390758615965651 36611032991086137923948477)
    ·
      refine ⟨13729137371657301721480679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36611032991086137923948477 13729137371657301721480679)
      ·
        refine ⟨20593706057485952582221019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13729137371657301721480679 20593706057485952582221019)
        ·
          refine ⟨30890559086228928873331529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20593706057485952582221019 30890559086228928873331529)
          ·
            refine ⟨23167919314671696654998647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30890559086228928873331529 23167919314671696654998647)
            ·
              refine ⟨34751878972007544982497971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23167919314671696654998647 34751878972007544982497971)
              ·
                refine ⟨52127818458011317473746957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34751878972007544982497971 52127818458011317473746957)
                ·
                  refine ⟨19547931921754244052655109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52127818458011317473746957 19547931921754244052655109)
                  ·
                    refine ⟨3665237235328920759872833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19547931921754244052655109 3665237235328920759872833)
                    ·
                      refine ⟨2748927926496690569904625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665237235328920759872833 2748927926496690569904625)
                      ·
                        rfl

theorem cell23_5353518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5353518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353518 prefixEnd_5353518 := by exact prefixLift 5353518
  have htrace : WordTrace (prefixWord ++ tailWord_5353518) baseStart_5353518 baseEnd_5353518 := by
    simpa [prefixWord, tailWord_5353518, baseEnd_5353518] using wordTrace_append hprefix tailTrace_5353518
  have hstable : (prefixWord ++ tailWord_5353518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353518).length < 2 ^ (prefixWord ++ tailWord_5353518).sum := by decide
  have hdescent : baseEnd_5353518 < baseStart_5353518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353558 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5353558 : Nat := 118140960795 + 5353558 * 2 ^ 59
def prefixEnd_5353558 : Nat := 4983230072969 + 3 ^ 40 * 5353558 * 2
def baseEnd_5353558 : Nat := 305438718413652268156049

theorem tailTrace_5353558 : CollatzResearch.WordTrace tailWord_5353558 prefixEnd_5353558 305438718413652268156049 := by
  unfold tailWord_5353558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12203768846186322234948833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130173534359320770506120885 12203768846186322234948833)
  ·
    refine ⟨9152826634639741676211625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12203768846186322234948833 9152826634639741676211625)
    ·
      refine ⟨6864619975979806257158719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9152826634639741676211625 6864619975979806257158719)
      ·
        refine ⟨10296929963969709385738079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864619975979806257158719 10296929963969709385738079)
        ·
          refine ⟨15445394945954564078607119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10296929963969709385738079 15445394945954564078607119)
          ·
            refine ⟨23168092418931846117910679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15445394945954564078607119 23168092418931846117910679)
            ·
              refine ⟨34752138628397769176866019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23168092418931846117910679 34752138628397769176866019)
              ·
                refine ⟨52128207942596653765299029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34752138628397769176866019 52128207942596653765299029)
                ·
                  refine ⟨305438718413652268156049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52128207942596653765299029 305438718413652268156049)
                  ·
                    rfl

theorem cell23_5353558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5353558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353558 prefixEnd_5353558 := by exact prefixLift 5353558
  have htrace : WordTrace (prefixWord ++ tailWord_5353558) baseStart_5353558 baseEnd_5353558 := by
    simpa [prefixWord, tailWord_5353558, baseEnd_5353558] using wordTrace_append hprefix tailTrace_5353558
  have hstable : (prefixWord ++ tailWord_5353558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353558).length < 2 ^ (prefixWord ++ tailWord_5353558).sum := by decide
  have hdescent : baseEnd_5353558 < baseStart_5353558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353561 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 5, 2]
def baseStart_5353561 : Nat := 118140960795 + 5353561 * 2 ^ 59
def prefixEnd_5353561 : Nat := 4983230072969 + 3 ^ 40 * 5353561 * 2
def baseEnd_5353561 : Nat := 2748950006164833901666927

theorem tailTrace_5353561 : CollatzResearch.WordTrace tailWord_5353561 prefixEnd_5353561 2748950006164833901666927 := by
  unfold tailWord_5353561
  simp only [CollatzResearch.WordTrace]
  refine ⟨195260410957970287271540537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130173607305313524847693691 195260410957970287271540537)
  ·
    refine ⟨146445308218477715453655403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195260410957970287271540537 146445308218477715453655403)
    ·
      refine ⟨219667962327716573180483105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146445308218477715453655403 219667962327716573180483105)
      ·
        refine ⟨164750971745787429885362329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219667962327716573180483105 164750971745787429885362329)
        ·
          refine ⟨123563228809340572414021747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164750971745787429885362329 123563228809340572414021747)
          ·
            refine ⟨185344843214010858621032621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123563228809340572414021747 185344843214010858621032621)
            ·
              refine ⟨69504316205254071982887233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185344843214010858621032621 69504316205254071982887233)
              ·
                refine ⟨52128237153940553987165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69504316205254071982887233 52128237153940553987165425)
                ·
                  refine ⟨39096177865455415490374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52128237153940553987165425 39096177865455415490374069)
                  ·
                    refine ⟨3665266674886445202222569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39096177865455415490374069 3665266674886445202222569)
                    ·
                      refine ⟨2748950006164833901666927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665266674886445202222569 2748950006164833901666927)
                      ·
                        rfl

theorem cell23_5353561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_5353561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353561 prefixEnd_5353561 := by exact prefixLift 5353561
  have htrace : WordTrace (prefixWord ++ tailWord_5353561) baseStart_5353561 baseEnd_5353561 := by
    simpa [prefixWord, tailWord_5353561, baseEnd_5353561] using wordTrace_append hprefix tailTrace_5353561
  have hstable : (prefixWord ++ tailWord_5353561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353561).length < 2 ^ (prefixWord ++ tailWord_5353561).sum := by decide
  have hdescent : baseEnd_5353561 < baseStart_5353561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353571 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 2, 5]
def baseStart_5353571 : Nat := 118140960795 + 5353571 * 2 ^ 59
def prefixEnd_5353571 : Nat := 4983230072969 + 3 ^ 40 * 5353571 * 2
def baseEnd_5353571 : Nat := 916318380323792954180627

theorem tailTrace_5353571 : CollatzResearch.WordTrace tailWord_5353571 prefixEnd_5353571 916318380323792954180627 := by
  unfold tailWord_5353571
  simp only [CollatzResearch.WordTrace]
  refine ⟨195260775687934058979404567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130173850458622705986269711 195260775687934058979404567)
  ·
    refine ⟨292891163531901088469106851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195260775687934058979404567 292891163531901088469106851)
    ·
      refine ⟨439336745297851632703660277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292891163531901088469106851 439336745297851632703660277)
      ·
        refine ⟨41187819871673590565968151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 439336745297851632703660277 41187819871673590565968151)
        ·
          refine ⟨61781729807510385848952227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41187819871673590565968151 61781729807510385848952227)
          ·
            refine ⟨92672594711265578773428341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61781729807510385848952227 92672594711265578773428341)
            ·
              refine ⟨8688055754181148010008907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92672594711265578773428341 8688055754181148010008907)
              ·
                refine ⟨13032083631271722015013361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8688055754181148010008907 13032083631271722015013361)
                ·
                  refine ⟨9774062723453791511260021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13032083631271722015013361 9774062723453791511260021)
                  ·
                    refine ⟨916318380323792954180627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9774062723453791511260021 916318380323792954180627)
                    ·
                      rfl

theorem cell23_5353571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 5].length) (baseStart_5353571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353571 prefixEnd_5353571 := by exact prefixLift 5353571
  have htrace : WordTrace (prefixWord ++ tailWord_5353571) baseStart_5353571 baseEnd_5353571 := by
    simpa [prefixWord, tailWord_5353571, baseEnd_5353571] using wordTrace_append hprefix tailTrace_5353571
  have hstable : (prefixWord ++ tailWord_5353571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353571).length < 2 ^ (prefixWord ++ tailWord_5353571).sum := by decide
  have hdescent : baseEnd_5353571 < baseStart_5353571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353618 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5353618 : Nat := 118140960795 + 5353618 * 2 ^ 59
def prefixEnd_5353618 : Nat := 4983230072969 + 3 ^ 40 * 5353618 * 2
def baseEnd_5353618 : Nat := 916326424854046726218055

theorem tailTrace_5353618 : CollatzResearch.WordTrace tailWord_5353618 prefixEnd_5353618 916326424854046726218055 := by
  unfold tailWord_5353618
  simp only [CollatzResearch.WordTrace]
  refine ⟨48815622479690946501591377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130174993279175857337577005 48815622479690946501591377)
  ·
    refine ⟨36611716859768209876193533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48815622479690946501591377 36611716859768209876193533)
    ·
      refine ⟨13729393822413078703572575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36611716859768209876193533 13729393822413078703572575)
      ·
        refine ⟨20594090733619618055358863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13729393822413078703572575 20594090733619618055358863)
        ·
          refine ⟨30891136100429427083038295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20594090733619618055358863 30891136100429427083038295)
          ·
            refine ⟨46336704150644140624557443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30891136100429427083038295 46336704150644140624557443)
            ·
              refine ⟨69505056225966210936836165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46336704150644140624557443 69505056225966210936836165)
              ·
                refine ⟨13032198042368664550656781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69505056225966210936836165 13032198042368664550656781)
                ·
                  refine ⟨4887074265888249206496293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13032198042368664550656781 4887074265888249206496293)
                  ·
                    refine ⟨916326424854046726218055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4887074265888249206496293 916326424854046726218055)
                    ·
                      rfl

theorem cell23_5353618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5353618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353618 prefixEnd_5353618 := by exact prefixLift 5353618
  have htrace : WordTrace (prefixWord ++ tailWord_5353618) baseStart_5353618 baseEnd_5353618 := by
    simpa [prefixWord, tailWord_5353618, baseEnd_5353618] using wordTrace_append hprefix tailTrace_5353618
  have hstable : (prefixWord ++ tailWord_5353618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353618).length < 2 ^ (prefixWord ++ tailWord_5353618).sum := by decide
  have hdescent : baseEnd_5353618 < baseStart_5353618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353628 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5353628 : Nat := 118140960795 + 5353628 * 2 ^ 59
def prefixEnd_5353628 : Nat := 4983230072969 + 3 ^ 40 * 5353628 * 2
def baseEnd_5353628 : Nat := 2748984409368685139529119

theorem tailTrace_5353628 : CollatzResearch.WordTrace tailWord_5353628 prefixEnd_5353628 2748984409368685139529119 := by
  unfold tailWord_5353628
  simp only [CollatzResearch.WordTrace]
  refine ⟨97631427324363778857114769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130175236432485038476153025 97631427324363778857114769)
  ·
    refine ⟨73223570493272834142836077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97631427324363778857114769 73223570493272834142836077)
    ·
      refine ⟨27458838934977312803563529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73223570493272834142836077 27458838934977312803563529)
      ·
        refine ⟨20594129201232984602672647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27458838934977312803563529 20594129201232984602672647)
        ·
          refine ⟨30891193801849476904008971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20594129201232984602672647 30891193801849476904008971)
          ·
            refine ⟨46336790702774215356013457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30891193801849476904008971 46336790702774215356013457)
            ·
              refine ⟨34752593027080661517010093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46336790702774215356013457 34752593027080661517010093)
              ·
                refine ⟨13032222385155248068878785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34752593027080661517010093 13032222385155248068878785)
                ·
                  refine ⟨9774166788866436051659089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13032222385155248068878785 9774166788866436051659089)
                  ·
                    refine ⟨7330625091649827038744317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9774166788866436051659089 7330625091649827038744317)
                    ·
                      refine ⟨2748984409368685139529119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330625091649827038744317 2748984409368685139529119)
                      ·
                        rfl

theorem cell23_5353628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5353628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353628 prefixEnd_5353628 := by exact prefixLift 5353628
  have htrace : WordTrace (prefixWord ++ tailWord_5353628) baseStart_5353628 baseEnd_5353628 := by
    simpa [prefixWord, tailWord_5353628, baseEnd_5353628] using wordTrace_append hprefix tailTrace_5353628
  have hstable : (prefixWord ++ tailWord_5353628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353628).length < 2 ^ (prefixWord ++ tailWord_5353628).sum := by decide
  have hdescent : baseEnd_5353628 < baseStart_5353628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353631 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 8]
def baseStart_5353631 : Nat := 118140960795 + 5353631 * 2 ^ 59
def prefixEnd_5353631 : Nat := 4983230072969 + 3 ^ 40 * 5353631 * 2
def baseEnd_5353631 : Nat := 305442883312294291976845

theorem tailTrace_5353631 : CollatzResearch.WordTrace tailWord_5353631 prefixEnd_5353631 305442883312294291976845 := by
  unfold tailWord_5353631
  simp only [CollatzResearch.WordTrace]
  refine ⟨195262964067716689226588747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130175309378477792817725831 195262964067716689226588747)
  ·
    refine ⟨292894446101575033839883121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195262964067716689226588747 292894446101575033839883121)
    ·
      refine ⟨219670834576181275379912341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292894446101575033839883121 219670834576181275379912341)
      ·
        refine ⟨10297070370758497283433391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 219670834576181275379912341 10297070370758497283433391)
        ·
          refine ⟨15445605556137745925150087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10297070370758497283433391 15445605556137745925150087)
          ·
            refine ⟨23168408334206618887725131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15445605556137745925150087 23168408334206618887725131)
            ·
              refine ⟨34752612501309928331587697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23168408334206618887725131 34752612501309928331587697)
              ·
                refine ⟨26064459375982446248690773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34752612501309928331587697 26064459375982446248690773)
                ·
                  refine ⟨305442883312294291976845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26064459375982446248690773 305442883312294291976845)
                  ·
                    rfl

theorem cell23_5353631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 8].length) (baseStart_5353631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353631 prefixEnd_5353631 := by exact prefixLift 5353631
  have htrace : WordTrace (prefixWord ++ tailWord_5353631) baseStart_5353631 baseEnd_5353631 := by
    simpa [prefixWord, tailWord_5353631, baseEnd_5353631] using wordTrace_append hprefix tailTrace_5353631
  have hstable : (prefixWord ++ tailWord_5353631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353631).length < 2 ^ (prefixWord ++ tailWord_5353631).sum := by decide
  have hdescent : baseEnd_5353631 < baseStart_5353631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353644 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_5353644 : Nat := 118140960795 + 5353644 * 2 ^ 59
def prefixEnd_5353644 : Nat := 4983230072969 + 3 ^ 40 * 5353644 * 2
def baseEnd_5353644 : Nat := 916330875019719025643015

theorem tailTrace_5353644 : CollatzResearch.WordTrace tailWord_5353644 prefixEnd_5353644 916330875019719025643015 := by
  unfold tailWord_5353644
  simp only [CollatzResearch.WordTrace]
  refine ⟨97631719108334796223405993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130175625477779728297874657 97631719108334796223405993)
  ·
    refine ⟨73223789331251097167554495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97631719108334796223405993 73223789331251097167554495)
    ·
      refine ⟨109835683996876645751331743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73223789331251097167554495 109835683996876645751331743)
      ·
        refine ⟨164753525995314968626997615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109835683996876645751331743 164753525995314968626997615)
        ·
          refine ⟨247130288992972452940496423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164753525995314968626997615 247130288992972452940496423)
          ·
            refine ⟨370695433489458679410744635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247130288992972452940496423 370695433489458679410744635)
            ·
              refine ⟨556043150234188019116116953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370695433489458679410744635 556043150234188019116116953)
              ·
                refine ⟨417032362675641014337087715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556043150234188019116116953 417032362675641014337087715)
                ·
                  refine ⟨625548544013461521505631573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417032362675641014337087715 625548544013461521505631573)
                  ·
                    refine ⟨916330875019719025643015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 625548544013461521505631573 916330875019719025643015)
                    ·
                      rfl

theorem cell23_5353644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_5353644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353644 prefixEnd_5353644 := by exact prefixLift 5353644
  have htrace : WordTrace (prefixWord ++ tailWord_5353644) baseStart_5353644 baseEnd_5353644 := by
    simpa [prefixWord, tailWord_5353644, baseEnd_5353644] using wordTrace_append hprefix tailTrace_5353644
  have hstable : (prefixWord ++ tailWord_5353644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353644).length < 2 ^ (prefixWord ++ tailWord_5353644).sum := by decide
  have hdescent : baseEnd_5353644 < baseStart_5353644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353645 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_5353645 : Nat := 118140960795 + 5353645 * 2 ^ 59
def prefixEnd_5353645 : Nat := 4983230072969 + 3 ^ 40 * 5353645 * 2
def baseEnd_5353645 : Nat := 2748993138539811573016541

theorem tailTrace_5353645 : CollatzResearch.WordTrace tailWord_5353645 prefixEnd_5353645 2748993138539811573016541 := by
  unfold tailWord_5353645
  simp only [CollatzResearch.WordTrace]
  refine ⟨195263474689665969617598389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130175649793110646411732259 195263474689665969617598389)
  ·
    refine ⟨18305950752156184651649849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195263474689665969617598389 18305950752156184651649849)
    ·
      refine ⟨13729463064117138488737387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18305950752156184651649849 13729463064117138488737387)
      ·
        refine ⟨20594194596175707733106081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13729463064117138488737387 20594194596175707733106081)
        ·
          refine ⟨15445645947131780799829561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20594194596175707733106081 15445645947131780799829561)
          ·
            refine ⟨11584234460348835599872171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15445645947131780799829561 11584234460348835599872171)
            ·
              refine ⟨17376351690523253399808257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584234460348835599872171 17376351690523253399808257)
              ·
                refine ⟨13032263767892440049856193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17376351690523253399808257 13032263767892440049856193)
                ·
                  refine ⟨9774197825919330037392145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13032263767892440049856193 9774197825919330037392145)
                  ·
                    refine ⟨7330648369439497528044109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9774197825919330037392145 7330648369439497528044109)
                    ·
                      refine ⟨2748993138539811573016541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330648369439497528044109 2748993138539811573016541)
                      ·
                        rfl

theorem cell23_5353645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_5353645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353645 prefixEnd_5353645 := by exact prefixLift 5353645
  have htrace : WordTrace (prefixWord ++ tailWord_5353645) baseStart_5353645 baseEnd_5353645 := by
    simpa [prefixWord, tailWord_5353645, baseEnd_5353645] using wordTrace_append hprefix tailTrace_5353645
  have hstable : (prefixWord ++ tailWord_5353645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353645).length < 2 ^ (prefixWord ++ tailWord_5353645).sum := by decide
  have hdescent : baseEnd_5353645 < baseStart_5353645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353661 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_5353661 : Nat := 118140960795 + 5353661 * 2 ^ 59
def prefixEnd_5353661 : Nat := 4983230072969 + 3 ^ 40 * 5353661 * 2
def baseEnd_5353661 : Nat := 916333784743427836805489

theorem tailTrace_5353661 : CollatzResearch.WordTrace tailWord_5353661 prefixEnd_5353661 916333784743427836805489 := by
  unfold tailWord_5353661
  simp only [CollatzResearch.WordTrace]
  refine ⟨195264058257608004350180837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130176038838405336233453891 195264058257608004350180837)
  ·
    refine ⟨36612010923301500815658907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195264058257608004350180837 36612010923301500815658907)
    ·
      refine ⟨54918016384952251223488361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36612010923301500815658907 54918016384952251223488361)
      ·
        refine ⟨41188512288714188417616271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54918016384952251223488361 41188512288714188417616271)
        ·
          refine ⟨61782768433071282626424407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41188512288714188417616271 61782768433071282626424407)
          ·
            refine ⟨92674152649606923939636611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61782768433071282626424407 92674152649606923939636611)
            ·
              refine ⟨139011228974410385909454917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92674152649606923939636611 139011228974410385909454917)
              ·
                refine ⟨26064605432701947358022797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139011228974410385909454917 26064605432701947358022797)
                ·
                  refine ⟨9774227037263230259258549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26064605432701947358022797 9774227037263230259258549)
                  ·
                    refine ⟨916333784743427836805489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9774227037263230259258549 916333784743427836805489)
                    ·
                      rfl

theorem cell23_5353661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_5353661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353661 prefixEnd_5353661 := by exact prefixLift 5353661
  have htrace : WordTrace (prefixWord ++ tailWord_5353661) baseStart_5353661 baseEnd_5353661 := by
    simpa [prefixWord, tailWord_5353661, baseEnd_5353661] using wordTrace_append hprefix tailTrace_5353661
  have hstable : (prefixWord ++ tailWord_5353661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353661).length < 2 ^ (prefixWord ++ tailWord_5353661).sum := by decide
  have hdescent : baseEnd_5353661 < baseStart_5353661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353665 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 6]
def baseStart_5353665 : Nat := 118140960795 + 5353665 * 2 ^ 59
def prefixEnd_5353665 : Nat := 4983230072969 + 3 ^ 40 * 5353665 * 2
def baseEnd_5353665 : Nat := 305444823128100166085161

theorem tailTrace_5353665 : CollatzResearch.WordTrace tailWord_5353665 prefixEnd_5353665 305444823128100166085161 := by
  unfold tailWord_5353665
  simp only [CollatzResearch.WordTrace]
  refine ⟨195264204149593513033326449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130176136099729008688884299 195264204149593513033326449)
  ·
    refine ⟨146448153112195134774994837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195264204149593513033326449 146448153112195134774994837)
    ·
      refine ⟨6864757177134146942577883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146448153112195134774994837 6864757177134146942577883)
      ·
        refine ⟨10297135765701220413866825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864757177134146942577883 10297135765701220413866825)
        ·
          refine ⟨7722851824275915310400119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10297135765701220413866825 7722851824275915310400119)
          ·
            refine ⟨11584277736413872965600179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722851824275915310400119 11584277736413872965600179)
            ·
              refine ⟨17376416604620809448400269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584277736413872965600179 17376416604620809448400269)
              ·
                refine ⟨6516156226732803543150101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17376416604620809448400269 6516156226732803543150101)
                ·
                  refine ⟨305444823128100166085161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6516156226732803543150101 305444823128100166085161)
                  ·
                    rfl

theorem cell23_5353665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_5353665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353665 prefixEnd_5353665 := by exact prefixLift 5353665
  have htrace : WordTrace (prefixWord ++ tailWord_5353665) baseStart_5353665 baseEnd_5353665 := by
    simpa [prefixWord, tailWord_5353665, baseEnd_5353665] using wordTrace_append hprefix tailTrace_5353665
  have hstable : (prefixWord ++ tailWord_5353665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353665).length < 2 ^ (prefixWord ++ tailWord_5353665).sum := by decide
  have hdescent : baseEnd_5353665 < baseStart_5353665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353678 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_5353678 : Nat := 118140960795 + 5353678 * 2 ^ 59
def prefixEnd_5353678 : Nat := 4983230072969 + 3 ^ 40 * 5353678 * 2
def baseEnd_5353678 : Nat := 916336694467136647967963

theorem tailTrace_5353678 : CollatzResearch.WordTrace tailWord_5353678 prefixEnd_5353678 916336694467136647967963 := by
  unfold tailWord_5353678
  simp only [CollatzResearch.WordTrace]
  refine ⟨24408084787318302031693711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130176452199030944169033125 24408084787318302031693711)
  ·
    refine ⟨36612127180977453047540567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24408084787318302031693711 36612127180977453047540567)
    ·
      refine ⟨54918190771466179571310851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36612127180977453047540567 54918190771466179571310851)
      ·
        refine ⟨82377286157199269356966277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54918190771466179571310851 82377286157199269356966277)
        ·
          refine ⟨15445741154474863004431177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82377286157199269356966277 15445741154474863004431177)
          ·
            refine ⟨11584305865856147253323383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15445741154474863004431177 11584305865856147253323383)
            ·
              refine ⟨17376458798784220879985075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584305865856147253323383 17376458798784220879985075)
              ·
                refine ⟨26064688198176331319977613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17376458798784220879985075 26064688198176331319977613)
                ·
                  refine ⟨9774258074316124244991605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26064688198176331319977613 9774258074316124244991605)
                  ·
                    refine ⟨916336694467136647967963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9774258074316124244991605 916336694467136647967963)
                    ·
                      rfl

theorem cell23_5353678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_5353678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353678 prefixEnd_5353678 := by exact prefixLift 5353678
  have htrace : WordTrace (prefixWord ++ tailWord_5353678) baseStart_5353678 baseEnd_5353678 := by
    simpa [prefixWord, tailWord_5353678, baseEnd_5353678] using wordTrace_append hprefix tailTrace_5353678
  have hstable : (prefixWord ++ tailWord_5353678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353678).length < 2 ^ (prefixWord ++ tailWord_5353678).sum := by decide
  have hdescent : baseEnd_5353678 < baseStart_5353678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353709 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5353709 : Nat := 118140960795 + 5353709 * 2 ^ 59
def prefixEnd_5353709 : Nat := 4983230072969 + 3 ^ 40 * 5353709 * 2
def baseEnd_5353709 : Nat := 2749026001301699322616247

theorem tailTrace_5353709 : CollatzResearch.WordTrace tailWord_5353709 prefixEnd_5353709 2749026001301699322616247 := by
  unfold tailWord_5353709
  simp only [CollatzResearch.WordTrace]
  refine ⟨195265808961434108547928181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130177205974289405698618787 195265808961434108547928181)
  ·
    refine ⟨18306169590134447676368267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195265808961434108547928181 18306169590134447676368267)
    ·
      refine ⟨27459254385201671514552401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18306169590134447676368267 27459254385201671514552401)
      ·
        refine ⟨20594440788901253635914301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27459254385201671514552401 20594440788901253635914301)
        ·
          refine ⟨7722915295837970113467863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20594440788901253635914301 7722915295837970113467863)
          ·
            refine ⟨11584372943756955170201795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722915295837970113467863 11584372943756955170201795)
            ·
              refine ⟨17376559415635432755302693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584372943756955170201795 17376559415635432755302693)
              ·
                refine ⟨3258104890431643641619255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17376559415635432755302693 3258104890431643641619255)
                ·
                  refine ⟨4887157335647465462428883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258104890431643641619255 4887157335647465462428883)
                  ·
                    refine ⟨7330736003471198193643325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4887157335647465462428883 7330736003471198193643325)
                    ·
                      refine ⟨2749026001301699322616247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7330736003471198193643325 2749026001301699322616247)
                      ·
                        rfl

theorem cell23_5353709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5353709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353709 prefixEnd_5353709 := by exact prefixLift 5353709
  have htrace : WordTrace (prefixWord ++ tailWord_5353709) baseStart_5353709 baseEnd_5353709 := by
    simpa [prefixWord, tailWord_5353709, baseEnd_5353709] using wordTrace_append hprefix tailTrace_5353709
  have hstable : (prefixWord ++ tailWord_5353709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353709).length < 2 ^ (prefixWord ++ tailWord_5353709).sum := by decide
  have hdescent : baseEnd_5353709 < baseStart_5353709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353715 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 3, 2, 2]
def baseStart_5353715 : Nat := 118140960795 + 5353715 * 2 ^ 59
def prefixEnd_5353715 : Nat := 4983230072969 + 3 ^ 40 * 5353715 * 2
def baseEnd_5353715 : Nat := 2749029082185626299141219

theorem tailTrace_5353715 : CollatzResearch.WordTrace tailWord_5353715 prefixEnd_5353715 2749029082185626299141219 := by
  unfold tailWord_5353715
  simp only [CollatzResearch.WordTrace]
  refine ⟨195266027799412371572646599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130177351866274914381764399 195266027799412371572646599)
  ·
    refine ⟨292899041699118557358969899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195266027799412371572646599 292899041699118557358969899)
    ·
      refine ⟨439348562548677836038454849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292899041699118557358969899 439348562548677836038454849)
      ·
        refine ⟨329511421911508377028841137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439348562548677836038454849 329511421911508377028841137)
        ·
          refine ⟨247133566433631282771630853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329511421911508377028841137 247133566433631282771630853)
          ·
            refine ⟨46337543706305865519680785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247133566433631282771630853 46337543706305865519680785)
            ·
              refine ⟨34753157779729399139760589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46337543706305865519680785 34753157779729399139760589)
              ·
                refine ⟨13032434167398524677410221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34753157779729399139760589 13032434167398524677410221)
                ·
                  refine ⟨4887162812774446754028833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13032434167398524677410221 4887162812774446754028833)
                  ·
                    refine ⟨3665372109580835065521625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4887162812774446754028833 3665372109580835065521625)
                    ·
                      refine ⟨2749029082185626299141219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665372109580835065521625 2749029082185626299141219)
                      ·
                        rfl

theorem cell23_5353715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 2, 2].length) (baseStart_5353715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353715 prefixEnd_5353715 := by exact prefixLift 5353715
  have htrace : WordTrace (prefixWord ++ tailWord_5353715) baseStart_5353715 baseEnd_5353715 := by
    simpa [prefixWord, tailWord_5353715, baseEnd_5353715] using wordTrace_append hprefix tailTrace_5353715
  have hstable : (prefixWord ++ tailWord_5353715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353715).length < 2 ^ (prefixWord ++ tailWord_5353715).sum := by decide
  have hdescent : baseEnd_5353715 < baseStart_5353715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353718 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5353718 : Nat := 118140960795 + 5353718 * 2 ^ 59
def prefixEnd_5353718 : Nat := 4983230072969 + 3 ^ 40 * 5353718 * 2
def baseEnd_5353718 : Nat := 2749030622627589787403705

theorem tailTrace_5353718 : CollatzResearch.WordTrace tailWord_5353718 prefixEnd_5353718 2749030622627589787403705 := by
  unfold tailWord_5353718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204133576150093942812863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130177424812267668723337205 12204133576150093942812863)
  ·
    refine ⟨18306200364225140914219295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12204133576150093942812863 18306200364225140914219295)
    ·
      refine ⟨27459300546337711371328943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18306200364225140914219295 27459300546337711371328943)
      ·
        refine ⟨41188950819506567056993415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27459300546337711371328943 41188950819506567056993415)
        ·
          refine ⟨61783426229259850585490123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41188950819506567056993415 61783426229259850585490123)
          ·
            refine ⟨92675139343889775878235185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61783426229259850585490123 92675139343889775878235185)
            ·
              refine ⟨69506354507917331908676389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92675139343889775878235185 69506354507917331908676389)
              ·
                refine ⟨13032441470234499732876823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69506354507917331908676389 13032441470234499732876823)
                ·
                  refine ⟨19548662205351749599315235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13032441470234499732876823 19548662205351749599315235)
                  ·
                    refine ⟨29322993308027624398972853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19548662205351749599315235 29322993308027624398972853)
                    ·
                      refine ⟨2749030622627589787403705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29322993308027624398972853 2749030622627589787403705)
                      ·
                        rfl

theorem cell23_5353718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5353718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353718 prefixEnd_5353718 := by exact prefixLift 5353718
  have htrace : WordTrace (prefixWord ++ tailWord_5353718) baseStart_5353718 baseEnd_5353718 := by
    simpa [prefixWord, tailWord_5353718, baseEnd_5353718] using wordTrace_append hprefix tailTrace_5353718
  have hstable : (prefixWord ++ tailWord_5353718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353718).length < 2 ^ (prefixWord ++ tailWord_5353718).sum := by decide
  have hdescent : baseEnd_5353718 < baseStart_5353718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353808 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_5353808 : Nat := 118140960795 + 5353808 * 2 ^ 59
def prefixEnd_5353808 : Nat := 4983230072969 + 3 ^ 40 * 5353808 * 2
def baseEnd_5353808 : Nat := 2749076835886494435278291

theorem tailTrace_5353808 : CollatzResearch.WordTrace tailWord_5353808 prefixEnd_5353808 2749076835886494435278291 := by
  unfold tailWord_5353808
  simp only [CollatzResearch.WordTrace]
  refine ⟨97634709894037724227891039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130179613192050298970521385 97634709894037724227891039)
  ·
    refine ⟨146452064841056586341836559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97634709894037724227891039 146452064841056586341836559)
    ·
      refine ⟨219678097261584879512754839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146452064841056586341836559 219678097261584879512754839)
      ·
        refine ⟨329517145892377319269132259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219678097261584879512754839 329517145892377319269132259)
        ·
          refine ⟨494275718838565978903698389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329517145892377319269132259 494275718838565978903698389)
          ·
            refine ⟨11584587160278890130555431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 494275718838565978903698389 11584587160278890130555431)
            ·
              refine ⟨17376880740418335195833147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584587160278890130555431 17376880740418335195833147)
              ·
                refine ⟨26065321110627502793749721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17376880740418335195833147 26065321110627502793749721)
                ·
                  refine ⟨19548990832970627095312291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26065321110627502793749721 19548990832970627095312291)
                  ·
                    refine ⟨29323486249455940642968437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19548990832970627095312291 29323486249455940642968437)
                    ·
                      refine ⟨2749076835886494435278291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29323486249455940642968437 2749076835886494435278291)
                      ·
                        rfl

theorem cell23_5353808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_5353808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353808 prefixEnd_5353808 := by exact prefixLift 5353808
  have htrace : WordTrace (prefixWord ++ tailWord_5353808) baseStart_5353808 baseEnd_5353808 := by
    simpa [prefixWord, tailWord_5353808, baseEnd_5353808] using wordTrace_append hprefix tailTrace_5353808
  have hstable : (prefixWord ++ tailWord_5353808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353808).length < 2 ^ (prefixWord ++ tailWord_5353808).sum := by decide
  have hdescent : baseEnd_5353808 < baseStart_5353808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353868 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5353868 : Nat := 118140960795 + 5353868 * 2 ^ 59
def prefixEnd_5353868 : Nat := 4983230072969 + 3 ^ 40 * 5353868 * 2
def baseEnd_5353868 : Nat := 2749107644725764200528015

theorem tailTrace_5353868 : CollatzResearch.WordTrace tailWord_5353868 prefixEnd_5353868 2749107644725764200528015 := by
  unfold tailWord_5353868
  simp only [CollatzResearch.WordTrace]
  refine ⟨97635804083929039351483129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130181072111905385801977505 97635804083929039351483129)
  ·
    refine ⟨73226853062946779513612347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97635804083929039351483129 73226853062946779513612347)
    ·
      refine ⟨109840279594420169270418521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73226853062946779513612347 109840279594420169270418521)
      ·
        refine ⟨82380209695815126952813891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109840279594420169270418521 82380209695815126952813891)
        ·
          refine ⟨123570314543722690429220837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82380209695815126952813891 123570314543722690429220837)
          ·
            refine ⟨23169433976948004455478907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123570314543722690429220837 23169433976948004455478907)
            ·
              refine ⟨34754150965422006683218361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23169433976948004455478907 34754150965422006683218361)
              ·
                refine ⟨26065613224066505012413771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34754150965422006683218361 26065613224066505012413771)
                ·
                  refine ⟨39098419836099757518620657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26065613224066505012413771 39098419836099757518620657)
                  ·
                    refine ⟨29323814877074818138965493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39098419836099757518620657 29323814877074818138965493)
                    ·
                      refine ⟨2749107644725764200528015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29323814877074818138965493 2749107644725764200528015)
                      ·
                        rfl

theorem cell23_5353868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5353868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353868 prefixEnd_5353868 := by exact prefixLift 5353868
  have htrace : WordTrace (prefixWord ++ tailWord_5353868) baseStart_5353868 baseEnd_5353868 := by
    simpa [prefixWord, tailWord_5353868, baseEnd_5353868] using wordTrace_append hprefix tailTrace_5353868
  have hstable : (prefixWord ++ tailWord_5353868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353868).length < 2 ^ (prefixWord ++ tailWord_5353868).sum := by decide
  have hdescent : baseEnd_5353868 < baseStart_5353868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353905 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_5353905 : Nat := 118140960795 + 5353905 * 2 ^ 59
def prefixEnd_5353905 : Nat := 4983230072969 + 3 ^ 40 * 5353905 * 2
def baseEnd_5353905 : Nat := 916375547836660185255115

theorem tailTrace_5353905 : CollatzResearch.WordTrace tailWord_5353905 prefixEnd_5353905 916375547836660185255115 := by
  unfold tailWord_5353905
  simp only [CollatzResearch.WordTrace]
  refine ⟨195272957668724034022063169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130181971779149356014708779 195272957668724034022063169)
  ·
    refine ⟨146454718251543025516547377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195272957668724034022063169 146454718251543025516547377)
    ·
      refine ⟨109841038688657269137410533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146454718251543025516547377 109841038688657269137410533)
      ·
        refine ⟨20595194754123237963264475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109841038688657269137410533 20595194754123237963264475)
        ·
          refine ⟨30892792131184856944896713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20595194754123237963264475 30892792131184856944896713)
          ·
            refine ⟨23169594098388642708672535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30892792131184856944896713 23169594098388642708672535)
            ·
              refine ⟨34754391147582964063008803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23169594098388642708672535 34754391147582964063008803)
              ·
                refine ⟨52131586721374446094513205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34754391147582964063008803 52131586721374446094513205)
                ·
                  refine ⟨4887336255128854321360613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52131586721374446094513205 4887336255128854321360613)
                  ·
                    refine ⟨916375547836660185255115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4887336255128854321360613 916375547836660185255115)
                    ·
                      rfl

theorem cell23_5353905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_5353905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353905 prefixEnd_5353905 := by exact prefixLift 5353905
  have htrace : WordTrace (prefixWord ++ tailWord_5353905) baseStart_5353905 baseEnd_5353905 := by
    simpa [prefixWord, tailWord_5353905, baseEnd_5353905] using wordTrace_append hprefix tailTrace_5353905
  have hstable : (prefixWord ++ tailWord_5353905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353905).length < 2 ^ (prefixWord ++ tailWord_5353905).sum := by decide
  have hdescent : baseEnd_5353905 < baseStart_5353905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353909 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_5353909 : Nat := 118140960795 + 5353909 * 2 ^ 59
def prefixEnd_5353909 : Nat := 4983230072969 + 3 ^ 40 * 5353909 * 2
def baseEnd_5353909 : Nat := 916376232477532846705109

theorem tailTrace_5353909 : CollatzResearch.WordTrace tailWord_5353909 prefixEnd_5353909 916376232477532846705109 := by
  unfold tailWord_5353909
  simp only [CollatzResearch.WordTrace]
  refine ⟨195273103560709542705208781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130182069040473028470139187 195273103560709542705208781)
  ·
    refine ⟨73227413835266078514453293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195273103560709542705208781 73227413835266078514453293)
    ·
      refine ⟨27460280188224779442919985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73227413835266078514453293 27460280188224779442919985)
      ·
        refine ⟨20595210141168584582189989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27460280188224779442919985 20595210141168584582189989)
        ·
          refine ⟨3861601901469109609160623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20595210141168584582189989 3861601901469109609160623)
          ·
            refine ⟨5792402852203664413740935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861601901469109609160623 5792402852203664413740935)
            ·
              refine ⟨8688604278305496620611403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792402852203664413740935 8688604278305496620611403)
              ·
                refine ⟨13032906417458244930917105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8688604278305496620611403 13032906417458244930917105)
                ·
                  refine ⟨9774679813093683698187829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13032906417458244930917105 9774679813093683698187829)
                  ·
                    refine ⟨916376232477532846705109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9774679813093683698187829 916376232477532846705109)
                    ·
                      rfl

theorem cell23_5353909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_5353909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353909 prefixEnd_5353909 := by exact prefixLift 5353909
  have htrace : WordTrace (prefixWord ++ tailWord_5353909) baseStart_5353909 baseEnd_5353909 := by
    simpa [prefixWord, tailWord_5353909, baseEnd_5353909] using wordTrace_append hprefix tailTrace_5353909
  have hstable : (prefixWord ++ tailWord_5353909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353909).length < 2 ^ (prefixWord ++ tailWord_5353909).sum := by decide
  have hdescent : baseEnd_5353909 < baseStart_5353909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5353973 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5353973 : Nat := 118140960795 + 5353973 * 2 ^ 59
def prefixEnd_5353973 : Nat := 4983230072969 + 3 ^ 40 * 5353973 * 2
def baseEnd_5353973 : Nat := 916387186731495429905011

theorem tailTrace_5353973 : CollatzResearch.WordTrace tailWord_5353973 prefixEnd_5353973 916387186731495429905011 := by
  unfold tailWord_5353973
  simp only [CollatzResearch.WordTrace]
  refine ⟨195275437832477681635538573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130183625221651787757025715 195275437832477681635538573)
  ·
    refine ⟨73228289187179130613326965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195275437832477681635538573 73228289187179130613326965)
    ·
      refine ⟨6865152111298043494999403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73228289187179130613326965 6865152111298043494999403)
      ·
        refine ⟨10297728166947065242499105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6865152111298043494999403 10297728166947065242499105)
        ·
          refine ⟨7723296125210298931874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10297728166947065242499105 7723296125210298931874329)
          ·
            refine ⟨5792472093907724198905747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7723296125210298931874329 5792472093907724198905747)
            ·
              refine ⟨8688708140861586298358621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792472093907724198905747 8688708140861586298358621)
              ·
                refine ⟨3258265552823094861884483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8688708140861586298358621 3258265552823094861884483)
                ·
                  refine ⟨4887398329234642292826725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258265552823094861884483 4887398329234642292826725)
                  ·
                    refine ⟨916387186731495429905011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4887398329234642292826725 916387186731495429905011)
                    ·
                      rfl

theorem cell23_5353973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5353973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5353973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5353973 prefixEnd_5353973 := by exact prefixLift 5353973
  have htrace : WordTrace (prefixWord ++ tailWord_5353973) baseStart_5353973 baseEnd_5353973 := by
    simpa [prefixWord, tailWord_5353973, baseEnd_5353973] using wordTrace_append hprefix tailTrace_5353973
  have hstable : (prefixWord ++ tailWord_5353973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5353973).length < 2 ^ (prefixWord ++ tailWord_5353973).sum := by decide
  have hdescent : baseEnd_5353973 < baseStart_5353973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5353973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354005 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_5354005 : Nat := 118140960795 + 5354005 * 2 ^ 59
def prefixEnd_5354005 : Nat := 4983230072969 + 3 ^ 40 * 5354005 * 2
def baseEnd_5354005 : Nat := 2749177991575430164514885

theorem tailTrace_5354005 : CollatzResearch.WordTrace tailWord_5354005 prefixEnd_5354005 2749177991575430164514885 := by
  unfold tailWord_5354005
  simp only [CollatzResearch.WordTrace]
  refine ⟨195276604968361751100703469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130184403312241167400468979 195276604968361751100703469)
  ·
    refine ⟨73228726863135656662763801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195276604968361751100703469 73228726863135656662763801)
    ·
      refine ⟨54921545147351742497072851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73228726863135656662763801 54921545147351742497072851)
      ·
        refine ⟨82382317721027613745609277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54921545147351742497072851 82382317721027613745609277)
        ·
          refine ⟨30893369145385355154603479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82382317721027613745609277 30893369145385355154603479)
          ·
            refine ⟨46340053718078032731905219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30893369145385355154603479 46340053718078032731905219)
            ·
              refine ⟨69510080577117049097857829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46340053718078032731905219 69510080577117049097857829)
              ·
                refine ⟨13033140108209446705848343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69510080577117049097857829 13033140108209446705848343)
                ·
                  refine ⟨19549710162314170058772515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033140108209446705848343 19549710162314170058772515)
                  ·
                    refine ⟨29324565243471255088158773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19549710162314170058772515 29324565243471255088158773)
                    ·
                      refine ⟨2749177991575430164514885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29324565243471255088158773 2749177991575430164514885)
                      ·
                        rfl

theorem cell23_5354005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_5354005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354005 prefixEnd_5354005 := by exact prefixLift 5354005
  have htrace : WordTrace (prefixWord ++ tailWord_5354005) baseStart_5354005 baseEnd_5354005 := by
    simpa [prefixWord, tailWord_5354005, baseEnd_5354005] using wordTrace_append hprefix tailTrace_5354005
  have hstable : (prefixWord ++ tailWord_5354005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354005).length < 2 ^ (prefixWord ++ tailWord_5354005).sum := by decide
  have hdescent : baseEnd_5354005 < baseStart_5354005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354015 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_5354015 : Nat := 118140960795 + 5354015 * 2 ^ 59
def prefixEnd_5354015 : Nat := 4983230072969 + 3 ^ 40 * 5354015 * 2
def baseEnd_5354015 : Nat := 2749183126381975125389839

theorem tailTrace_5354015 : CollatzResearch.WordTrace tailWord_5354015 prefixEnd_5354015 2749183126381975125389839 := by
  unfold tailWord_5354015
  simp only [CollatzResearch.WordTrace]
  refine ⟨195276969698325522808567499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130184646465550348539044999 195276969698325522808567499)
  ·
    refine ⟨292915454547488284212851249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195276969698325522808567499 292915454547488284212851249)
    ·
      refine ⟨219686590910616213159638437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292915454547488284212851249 219686590910616213159638437)
      ·
        refine ⟨41191235795740539967432207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219686590910616213159638437 41191235795740539967432207)
        ·
          refine ⟨61786853693610809951148311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41191235795740539967432207 61786853693610809951148311)
          ·
            refine ⟨92680280540416214926722467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61786853693610809951148311 92680280540416214926722467)
            ·
              refine ⟨139020420810624322390083701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92680280540416214926722467 139020420810624322390083701)
              ·
                refine ⟨13033164450996030224070347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139020420810624322390083701 13033164450996030224070347)
                ·
                  refine ⟨19549746676494045336105521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033164450996030224070347 19549746676494045336105521)
                  ·
                    refine ⟨14662310007370534002079141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19549746676494045336105521 14662310007370534002079141)
                    ·
                      refine ⟨2749183126381975125389839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14662310007370534002079141 2749183126381975125389839)
                      ·
                        rfl

theorem cell23_5354015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_5354015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354015 prefixEnd_5354015 := by exact prefixLift 5354015
  have htrace : WordTrace (prefixWord ++ tailWord_5354015) baseStart_5354015 baseEnd_5354015 := by
    simpa [prefixWord, tailWord_5354015, baseEnd_5354015] using wordTrace_append hprefix tailTrace_5354015
  have hstable : (prefixWord ++ tailWord_5354015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354015).length < 2 ^ (prefixWord ++ tailWord_5354015).sum := by decide
  have hdescent : baseEnd_5354015 < baseStart_5354015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354016 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 1, 5]
def baseStart_5354016 : Nat := 118140960795 + 5354016 * 2 ^ 59
def prefixEnd_5354016 : Nat := 4983230072969 + 3 ^ 40 * 5354016 * 2
def baseEnd_5354016 : Nat := 916394546620876540492445

theorem tailTrace_5354016 : CollatzResearch.WordTrace tailWord_5354016 prefixEnd_5354016 916394546620876540492445 := by
  unfold tailWord_5354016
  simp only [CollatzResearch.WordTrace]
  refine ⟨97638503085660949989676951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130184670780881266652902601 97638503085660949989676951)
  ·
    refine ⟨146457754628491424984515427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97638503085660949989676951 146457754628491424984515427)
    ·
      refine ⟨219686631942737137476773141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146457754628491424984515427 219686631942737137476773141)
      ·
        refine ⟨10297810872315803319223741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 219686631942737137476773141 10297810872315803319223741)
        ·
          refine ⟨3861679077118426244708903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10297810872315803319223741 3861679077118426244708903)
          ·
            refine ⟨5792518615677639367063355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861679077118426244708903 5792518615677639367063355)
            ·
              refine ⟨8688777923516459050595033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792518615677639367063355 8688777923516459050595033)
              ·
                refine ⟨6516583442637344287946275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8688777923516459050595033 6516583442637344287946275)
                ·
                  refine ⟨9774875163956016431919413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516583442637344287946275 9774875163956016431919413)
                  ·
                    refine ⟨916394546620876540492445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9774875163956016431919413 916394546620876540492445)
                    ·
                      rfl

theorem cell23_5354016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_5354016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354016 prefixEnd_5354016 := by exact prefixLift 5354016
  have htrace : WordTrace (prefixWord ++ tailWord_5354016) baseStart_5354016 baseEnd_5354016 := by
    simpa [prefixWord, tailWord_5354016, baseEnd_5354016] using wordTrace_append hprefix tailTrace_5354016
  have hstable : (prefixWord ++ tailWord_5354016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354016).length < 2 ^ (prefixWord ++ tailWord_5354016).sum := by decide
  have hdescent : baseEnd_5354016 < baseStart_5354016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354019 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 4]
def baseStart_5354019 : Nat := 118140960795 + 5354019 * 2 ^ 59
def prefixEnd_5354019 : Nat := 4983230072969 + 3 ^ 40 * 5354019 * 2
def baseEnd_5354019 : Nat := 2749185180304593109739821

theorem tailTrace_5354019 : CollatzResearch.WordTrace tailWord_5354019 prefixEnd_5354019 2749185180304593109739821 := by
  unfold tailWord_5354019
  simp only [CollatzResearch.WordTrace]
  refine ⟨195277115590311031491713111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130184743726874020994475407 195277115590311031491713111)
  ·
    refine ⟨292915673385466547237569667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195277115590311031491713111 292915673385466547237569667)
    ·
      refine ⟨439373510078199820856354501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292915673385466547237569667 439373510078199820856354501)
      ·
        refine ⟨82382533139662466410566469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 439373510078199820856354501 82382533139662466410566469)
        ·
          refine ⟨15446724963686712451981213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82382533139662466410566469 15446724963686712451981213)
          ·
            refine ⟨5792521861382517169492955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15446724963686712451981213 5792521861382517169492955)
            ·
              refine ⟨8688782792073775754239433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792521861382517169492955 8688782792073775754239433)
              ·
                refine ⟨6516587094055331815679575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8688782792073775754239433 6516587094055331815679575)
                ·
                  refine ⟨9774880641082997723519363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516587094055331815679575 9774880641082997723519363)
                  ·
                    refine ⟨14662320961624496585279045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9774880641082997723519363 14662320961624496585279045)
                    ·
                      refine ⟨2749185180304593109739821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14662320961624496585279045 2749185180304593109739821)
                      ·
                        rfl

theorem cell23_5354019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_5354019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354019 prefixEnd_5354019 := by exact prefixLift 5354019
  have htrace : WordTrace (prefixWord ++ tailWord_5354019) baseStart_5354019 baseEnd_5354019 := by
    simpa [prefixWord, tailWord_5354019, baseEnd_5354019] using wordTrace_append hprefix tailTrace_5354019
  have hstable : (prefixWord ++ tailWord_5354019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354019).length < 2 ^ (prefixWord ++ tailWord_5354019).sum := by decide
  have hdescent : baseEnd_5354019 < baseStart_5354019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354023 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5354023 : Nat := 118140960795 + 5354023 * 2 ^ 59
def prefixEnd_5354023 : Nat := 4983230072969 + 3 ^ 40 * 5354023 * 2
def baseEnd_5354023 : Nat := 2749187234227211094089803

theorem tailTrace_5354023 : CollatzResearch.WordTrace tailWord_5354023 prefixEnd_5354023 2749187234227211094089803 := by
  unfold tailWord_5354023
  simp only [CollatzResearch.WordTrace]
  refine ⟨195277261482296540174858723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130184840988197693449905815 195277261482296540174858723)
  ·
    refine ⟨292915892223444810262288085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195277261482296540174858723 292915892223444810262288085)
    ·
      refine ⟨6865216223986987740522377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 292915892223444810262288085 6865216223986987740522377)
      ·
        refine ⟨5148912167990240805391783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865216223986987740522377 5148912167990240805391783)
        ·
          refine ⟨7723368251985361208087675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148912167990240805391783 7723368251985361208087675)
          ·
            refine ⟨11585052377978041812131513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723368251985361208087675 11585052377978041812131513)
            ·
              refine ⟨8688789283483531359098635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11585052377978041812131513 8688789283483531359098635)
              ·
                refine ⟨13033183925225297038647953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8688789283483531359098635 13033183925225297038647953)
                ·
                  refine ⟨9774887943918972778985965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13033183925225297038647953 9774887943918972778985965)
                  ·
                    refine ⟨3665582978969614792119737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9774887943918972778985965 3665582978969614792119737)
                    ·
                      refine ⟨2749187234227211094089803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665582978969614792119737 2749187234227211094089803)
                      ·
                        rfl

theorem cell23_5354023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5354023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354023 prefixEnd_5354023 := by exact prefixLift 5354023
  have htrace : WordTrace (prefixWord ++ tailWord_5354023) baseStart_5354023 baseEnd_5354023 := by
    simpa [prefixWord, tailWord_5354023, baseEnd_5354023] using wordTrace_append hprefix tailTrace_5354023
  have hstable : (prefixWord ++ tailWord_5354023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354023).length < 2 ^ (prefixWord ++ tailWord_5354023).sum := by decide
  have hdescent : baseEnd_5354023 < baseStart_5354023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354039 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_5354039 : Nat := 118140960795 + 5354039 * 2 ^ 59
def prefixEnd_5354039 : Nat := 4983230072969 + 3 ^ 40 * 5354039 * 2
def baseEnd_5354039 : Nat := 2749195449917683031489729

theorem tailTrace_5354039 : CollatzResearch.WordTrace tailWord_5354039 prefixEnd_5354039 2749195449917683031489729 := by
  unfold tailWord_5354039
  simp only [CollatzResearch.WordTrace]
  refine ⟨195277845050238574907441171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130185230033492383271627447 195277845050238574907441171)
  ·
    refine ⟨292916767575357862361161757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195277845050238574907441171 292916767575357862361161757)
    ·
      refine ⟨109843787840759198385435659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292916767575357862361161757 109843787840759198385435659)
      ·
        refine ⟨164765681761138797578153489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109843787840759198385435659 164765681761138797578153489)
        ·
          refine ⟨123574261320854098183615117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164765681761138797578153489 123574261320854098183615117)
          ·
            refine ⟨46340347995320286818855669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123574261320854098183615117 46340347995320286818855669)
            ·
              refine ⟨4344407624561276889267719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46340347995320286818855669 4344407624561276889267719)
              ·
                refine ⟨6516611436841915333901579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344407624561276889267719 6516611436841915333901579)
                ·
                  refine ⟨9774917155262873000852369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516611436841915333901579 9774917155262873000852369)
                  ·
                    refine ⟨7331187866447154750639277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9774917155262873000852369 7331187866447154750639277)
                    ·
                      refine ⟨2749195449917683031489729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7331187866447154750639277 2749195449917683031489729)
                      ·
                        rfl

theorem cell23_5354039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_5354039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354039 prefixEnd_5354039 := by exact prefixLift 5354039
  have htrace : WordTrace (prefixWord ++ tailWord_5354039) baseStart_5354039 baseEnd_5354039 := by
    simpa [prefixWord, tailWord_5354039, baseEnd_5354039] using wordTrace_append hprefix tailTrace_5354039
  have hstable : (prefixWord ++ tailWord_5354039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354039).length < 2 ^ (prefixWord ++ tailWord_5354039).sum := by decide
  have hdescent : baseEnd_5354039 < baseStart_5354039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354053 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 1, 2, 2]
def baseStart_5354053 : Nat := 118140960795 + 5354053 * 2 ^ 59
def prefixEnd_5354053 : Nat := 4983230072969 + 3 ^ 40 * 5354053 * 2
def baseEnd_5354053 : Nat := 2749202638646845976714665

theorem tailTrace_5354053 : CollatzResearch.WordTrace tailWord_5354053 prefixEnd_5354053 2749202638646845976714665 := by
  unfold tailWord_5354053
  simp only [CollatzResearch.WordTrace]
  refine ⟨195278355672187855298450813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130185570448125236865633875 195278355672187855298450813)
  ·
    refine ⟨73229383377070445736919055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195278355672187855298450813 73229383377070445736919055)
    ·
      refine ⟨109844075065605668605378583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73229383377070445736919055 109844075065605668605378583)
      ·
        refine ⟨164766112598408502908067875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109844075065605668605378583 164766112598408502908067875)
        ·
          refine ⟨247149168897612754362101813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164766112598408502908067875 247149168897612754362101813)
          ·
            refine ⟨23170234584151195721447045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247149168897612754362101813 23170234584151195721447045)
            ·
              refine ⟨4344418984528349197771321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23170234584151195721447045 4344418984528349197771321)
              ·
                refine ⟨3258314238396261898328491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344418984528349197771321 3258314238396261898328491)
                ·
                  refine ⟨4887471357594392847492737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258314238396261898328491 4887471357594392847492737)
                  ·
                    refine ⟨3665603518195794635619553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4887471357594392847492737 3665603518195794635619553)
                    ·
                      refine ⟨2749202638646845976714665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665603518195794635619553 2749202638646845976714665)
                      ·
                        rfl

theorem cell23_5354053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_5354053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354053 prefixEnd_5354053 := by exact prefixLift 5354053
  have htrace : WordTrace (prefixWord ++ tailWord_5354053) baseStart_5354053 baseEnd_5354053 := by
    simpa [prefixWord, tailWord_5354053, baseEnd_5354053] using wordTrace_append hprefix tailTrace_5354053
  have hstable : (prefixWord ++ tailWord_5354053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354053).length < 2 ^ (prefixWord ++ tailWord_5354053).sum := by decide
  have hdescent : baseEnd_5354053 < baseStart_5354053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354055 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 7]
def baseStart_5354055 : Nat := 118140960795 + 5354055 * 2 ^ 59
def prefixEnd_5354055 : Nat := 4983230072969 + 3 ^ 40 * 5354055 * 2
def baseEnd_5354055 : Nat := 916401221869384989629885

theorem tailTrace_5354055 : CollatzResearch.WordTrace tailWord_5354055 prefixEnd_5354055 916401221869384989629885 := by
  unfold tailWord_5354055
  simp only [CollatzResearch.WordTrace]
  refine ⟨195278428618180609640023619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130185619078787073093349079 195278428618180609640023619)
  ·
    refine ⟨292917642927270914460035429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195278428618180609640023619 292917642927270914460035429)
    ·
      refine ⟨54922058048863296461256643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292917642927270914460035429 54922058048863296461256643)
      ·
        refine ⟨82383087073294944691884965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54922058048863296461256643 82383087073294944691884965)
        ·
          refine ⟨15446828826242802129728431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82383087073294944691884965 15446828826242802129728431)
          ·
            refine ⟨23170243239364203194592647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15446828826242802129728431 23170243239364203194592647)
            ·
              refine ⟨34755364859046304791888971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23170243239364203194592647 34755364859046304791888971)
              ·
                refine ⟨52133047288569457187833457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34755364859046304791888971 52133047288569457187833457)
                ·
                  refine ⟨39099785466427092890875093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52133047288569457187833457 39099785466427092890875093)
                  ·
                    refine ⟨916401221869384989629885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39099785466427092890875093 916401221869384989629885)
                    ·
                      rfl

theorem cell23_5354055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_5354055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354055 prefixEnd_5354055 := by exact prefixLift 5354055
  have htrace : WordTrace (prefixWord ++ tailWord_5354055) baseStart_5354055 baseEnd_5354055 := by
    simpa [prefixWord, tailWord_5354055, baseEnd_5354055] using wordTrace_append hprefix tailTrace_5354055
  have hstable : (prefixWord ++ tailWord_5354055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354055).length < 2 ^ (prefixWord ++ tailWord_5354055).sum := by decide
  have hdescent : baseEnd_5354055 < baseStart_5354055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354069 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5354069 : Nat := 118140960795 + 5354069 * 2 ^ 59
def prefixEnd_5354069 : Nat := 4983230072969 + 3 ^ 40 * 5354069 * 2
def baseEnd_5354069 : Nat := 2749210854337317914114591

theorem tailTrace_5354069 : CollatzResearch.WordTrace tailWord_5354069 prefixEnd_5354069 2749210854337317914114591 := by
  unfold tailWord_5354069
  simp only [CollatzResearch.WordTrace]
  refine ⟨195278939240129890031033261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130185959493419926687355507 195278939240129890031033261)
  ·
    refine ⟨73229602215048708761637473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195278939240129890031033261 73229602215048708761637473)
    ·
      refine ⟨54922201661286531571228105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73229602215048708761637473 54922201661286531571228105)
      ·
        refine ⟨41191651245964898678421079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54922201661286531571228105 41191651245964898678421079)
        ·
          refine ⟨61787476868947348017631619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41191651245964898678421079 61787476868947348017631619)
          ·
            refine ⟨92681215303421022026447429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61787476868947348017631619 92681215303421022026447429)
            ·
              refine ⟨17377727869391441629958893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92681215303421022026447429 17377727869391441629958893)
              ·
                refine ⟨6516647951021790611234585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17377727869391441629958893 6516647951021790611234585)
                ·
                  refine ⟨4887485963266342958425939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6516647951021790611234585 4887485963266342958425939)
                  ·
                    refine ⟨7331228944899514437638909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4887485963266342958425939 7331228944899514437638909)
                    ·
                      refine ⟨2749210854337317914114591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7331228944899514437638909 2749210854337317914114591)
                      ·
                        rfl

theorem cell23_5354069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5354069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354069 prefixEnd_5354069 := by exact prefixLift 5354069
  have htrace : WordTrace (prefixWord ++ tailWord_5354069) baseStart_5354069 baseEnd_5354069 := by
    simpa [prefixWord, tailWord_5354069, baseEnd_5354069] using wordTrace_append hprefix tailTrace_5354069
  have hstable : (prefixWord ++ tailWord_5354069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354069).length < 2 ^ (prefixWord ++ tailWord_5354069).sum := by decide
  have hdescent : baseEnd_5354069 < baseStart_5354069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354095 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_5354095 : Nat := 118140960795 + 5354095 * 2 ^ 59
def prefixEnd_5354095 : Nat := 4983230072969 + 3 ^ 40 * 5354095 * 2
def baseEnd_5354095 : Nat := 2749224204834334812389471

theorem tailTrace_5354095 : CollatzResearch.WordTrace tailWord_5354095 prefixEnd_5354095 2749224204834334812389471 := by
  unfold tailWord_5354095
  simp only [CollatzResearch.WordTrace]
  refine ⟨195279887538035696471479739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130186591692023797647653159 195279887538035696471479739)
  ·
    refine ⟨292919831307053544707219609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195279887538035696471479739 292919831307053544707219609)
    ·
      refine ⟨219689873480290158530414707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292919831307053544707219609 219689873480290158530414707)
      ·
        refine ⟨329534810220435237795622061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219689873480290158530414707 329534810220435237795622061)
        ·
          refine ⟨123575553832663214173358273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329534810220435237795622061 123575553832663214173358273)
          ·
            refine ⟨92681665374497410630018705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123575553832663214173358273 92681665374497410630018705)
            ·
              refine ⟨69511249030873057972514029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92681665374497410630018705 69511249030873057972514029)
              ·
                refine ⟨26066718386577396739692761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69511249030873057972514029 26066718386577396739692761)
                ·
                  refine ⟨19550038789933047554769571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26066718386577396739692761 19550038789933047554769571)
                  ·
                    refine ⟨29325058184899571332154357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19550038789933047554769571 29325058184899571332154357)
                    ·
                      refine ⟨2749224204834334812389471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29325058184899571332154357 2749224204834334812389471)
                      ·
                        rfl

theorem cell23_5354095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_5354095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354095 prefixEnd_5354095 := by exact prefixLift 5354095
  have htrace : WordTrace (prefixWord ++ tailWord_5354095) baseStart_5354095 baseEnd_5354095 := by
    simpa [prefixWord, tailWord_5354095, baseEnd_5354095] using wordTrace_append hprefix tailTrace_5354095
  have hstable : (prefixWord ++ tailWord_5354095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354095).length < 2 ^ (prefixWord ++ tailWord_5354095).sum := by decide
  have hdescent : baseEnd_5354095 < baseStart_5354095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354096 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2]
def baseStart_5354096 : Nat := 118140960795 + 5354096 * 2 ^ 59
def prefixEnd_5354096 : Nat := 4983230072969 + 3 ^ 40 * 5354096 * 2
def baseEnd_5354096 : Nat := 2749224718314989308476967

theorem tailTrace_5354096 : CollatzResearch.WordTrace tailWord_5354096 prefixEnd_5354096 2749224718314989308476967 := by
  unfold tailWord_5354096
  simp only [CollatzResearch.WordTrace]
  refine ⟨97639962005516036821133071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130186616007354715761510761 97639962005516036821133071)
  ·
    refine ⟨146459943008274055231699607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97639962005516036821133071 146459943008274055231699607)
    ·
      refine ⟨219689914512411082847549411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146459943008274055231699607 219689914512411082847549411)
      ·
        refine ⟨329534871768616624271324117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219689914512411082847549411 329534871768616624271324117)
        ·
          refine ⟨7723473557076952131359159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 329534871768616624271324117 7723473557076952131359159)
          ·
            refine ⟨11585210335615428197038739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723473557076952131359159 11585210335615428197038739)
            ·
              refine ⟨17377815503423142295558109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11585210335615428197038739 17377815503423142295558109)
              ·
                refine ⟨6516680813783678360834291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17377815503423142295558109 6516680813783678360834291)
                ·
                  refine ⟨9775021220675517541251437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516680813783678360834291 9775021220675517541251437)
                  ·
                    refine ⟨3665632957753319077969289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9775021220675517541251437 3665632957753319077969289)
                    ·
                      refine ⟨2749224718314989308476967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665632957753319077969289 2749224718314989308476967)
                      ·
                        rfl

theorem cell23_5354096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 3, 2].length) (baseStart_5354096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354096 prefixEnd_5354096 := by exact prefixLift 5354096
  have htrace : WordTrace (prefixWord ++ tailWord_5354096) baseStart_5354096 baseEnd_5354096 := by
    simpa [prefixWord, tailWord_5354096, baseEnd_5354096] using wordTrace_append hprefix tailTrace_5354096
  have hstable : (prefixWord ++ tailWord_5354096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354096).length < 2 ^ (prefixWord ++ tailWord_5354096).sum := by decide
  have hdescent : baseEnd_5354096 < baseStart_5354096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354115 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 7]
def baseStart_5354115 : Nat := 118140960795 + 5354115 * 2 ^ 59
def prefixEnd_5354115 : Nat := 4983230072969 + 3 ^ 40 * 5354115 * 2
def baseEnd_5354115 : Nat := 305470497160824970459931

theorem tailTrace_5354115 : CollatzResearch.WordTrace tailWord_5354115 prefixEnd_5354115 305470497160824970459931 := by
  unfold tailWord_5354115
  simp only [CollatzResearch.WordTrace]
  refine ⟨195280616997963239887207799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130187077998642159924805199 195280616997963239887207799)
  ·
    refine ⟨292920925496944859830811699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195280616997963239887207799 292920925496944859830811699)
    ·
      refine ⟨439381388245417289746217549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292920925496944859830811699 439381388245417289746217549)
      ·
        refine ⟨164768020592031483654831581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439381388245417289746217549 164768020592031483654831581)
        ·
          refine ⟨61788007722011806370561843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164768020592031483654831581 61788007722011806370561843)
          ·
            refine ⟨92682011583017709555842765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61788007722011806370561843 92682011583017709555842765)
            ·
              refine ⟨34755754343631641083441037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92682011583017709555842765 34755754343631641083441037)
              ·
                refine ⟨13033407878861865406290389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34755754343631641083441037 13033407878861865406290389)
                ·
                  refine ⟨305470497160824970459931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13033407878861865406290389 305470497160824970459931)
                  ·
                    rfl

theorem cell23_5354115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 7].length) (baseStart_5354115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354115 prefixEnd_5354115 := by exact prefixLift 5354115
  have htrace : WordTrace (prefixWord ++ tailWord_5354115) baseStart_5354115 baseEnd_5354115 := by
    simpa [prefixWord, tailWord_5354115, baseEnd_5354115] using wordTrace_append hprefix tailTrace_5354115
  have hstable : (prefixWord ++ tailWord_5354115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354115).length < 2 ^ (prefixWord ++ tailWord_5354115).sum := by decide
  have hdescent : baseEnd_5354115 < baseStart_5354115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354172 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5354172 : Nat := 118140960795 + 5354172 * 2 ^ 59
def prefixEnd_5354172 : Nat := 4983230072969 + 3 ^ 40 * 5354172 * 2
def baseEnd_5354172 : Nat := 2749263742844731011126617

theorem tailTrace_5354172 : CollatzResearch.WordTrace tailWord_5354172 prefixEnd_5354172 2749263742844731011126617 := by
  unfold tailWord_5354172
  simp only [CollatzResearch.WordTrace]
  refine ⟨97641347979378369311016385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130188463972504492414688513 97641347979378369311016385)
  ·
    refine ⟨73231010984533776983262289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97641347979378369311016385 73231010984533776983262289)
    ·
      refine ⟨54923258238400332737446717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73231010984533776983262289 54923258238400332737446717)
      ·
        refine ⟨20596221839400124776542519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54923258238400332737446717 20596221839400124776542519)
        ·
          refine ⟨30894332759100187164813779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20596221839400124776542519 30894332759100187164813779)
          ·
            refine ⟨46341499138650280747220669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30894332759100187164813779 46341499138650280747220669)
            ·
              refine ⟨17378062176993855280207751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46341499138650280747220669 17378062176993855280207751)
              ·
                refine ⟨26067093265490782920311627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17378062176993855280207751 26067093265490782920311627)
                ·
                  refine ⟨39100639898236174380467441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26067093265490782920311627 39100639898236174380467441)
                  ·
                    refine ⟨29325479923677130785350581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39100639898236174380467441 29325479923677130785350581)
                    ·
                      refine ⟨2749263742844731011126617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29325479923677130785350581 2749263742844731011126617)
                      ·
                        rfl

theorem cell23_5354172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5354172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354172 prefixEnd_5354172 := by exact prefixLift 5354172
  have htrace : WordTrace (prefixWord ++ tailWord_5354172) baseStart_5354172 baseEnd_5354172 := by
    simpa [prefixWord, tailWord_5354172, baseEnd_5354172] using wordTrace_append hprefix tailTrace_5354172
  have hstable : (prefixWord ++ tailWord_5354172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354172).length < 2 ^ (prefixWord ++ tailWord_5354172).sum := by decide
  have hdescent : baseEnd_5354172 < baseStart_5354172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354185 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_5354185 : Nat := 118140960795 + 5354185 * 2 ^ 59
def prefixEnd_5354185 : Nat := 4983230072969 + 3 ^ 40 * 5354185 * 2
def baseEnd_5354185 : Nat := 2749270418093239460264057

theorem tailTrace_5354185 : CollatzResearch.WordTrace tailWord_5354185 prefixEnd_5354185 2749270418093239460264057 := by
  unfold tailWord_5354185
  simp only [CollatzResearch.WordTrace]
  refine ⟨195283170107709641842256009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130188780071806427894837339 195283170107709641842256009)
  ·
    refine ⟨146462377580782231381692007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195283170107709641842256009 146462377580782231381692007)
    ·
      refine ⟨219693566371173347072538011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146462377580782231381692007 219693566371173347072538011)
      ·
        refine ⟨329540349556760020608807017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219693566371173347072538011 329540349556760020608807017)
        ·
          refine ⟨247155262167570015456605263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329540349556760020608807017 247155262167570015456605263)
          ·
            refine ⟨370732893251355023184907895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247155262167570015456605263 370732893251355023184907895)
            ·
              refine ⟨556099339877032534777361843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370732893251355023184907895 556099339877032534777361843)
              ·
                refine ⟨834149009815548802166042765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556099339877032534777361843 834149009815548802166042765)
                ·
                  refine ⟨312805878680830800812266037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834149009815548802166042765 312805878680830800812266037)
                  ·
                    refine ⟨29325551126327887576149941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 312805878680830800812266037 29325551126327887576149941)
                    ·
                      refine ⟨2749270418093239460264057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29325551126327887576149941 2749270418093239460264057)
                      ·
                        rfl

theorem cell23_5354185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_5354185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354185 prefixEnd_5354185 := by exact prefixLift 5354185
  have htrace : WordTrace (prefixWord ++ tailWord_5354185) baseStart_5354185 baseEnd_5354185 := by
    simpa [prefixWord, tailWord_5354185, baseEnd_5354185] using wordTrace_append hprefix tailTrace_5354185
  have hstable : (prefixWord ++ tailWord_5354185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354185).length < 2 ^ (prefixWord ++ tailWord_5354185).sum := by decide
  have hdescent : baseEnd_5354185 < baseStart_5354185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354196 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_5354196 : Nat := 118140960795 + 5354196 * 2 ^ 59
def prefixEnd_5354196 : Nat := 4983230072969 + 3 ^ 40 * 5354196 * 2
def baseEnd_5354196 : Nat := 916425355460146305742169

theorem tailTrace_5354196 : CollatzResearch.WordTrace tailWord_5354196 prefixEnd_5354196 916425355460146305742169 := by
  unfold tailWord_5354196
  simp only [CollatzResearch.WordTrace]
  refine ⟨97641785655334895360453221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130189047540446527147270961 97641785655334895360453221)
  ·
    refine ⟨18307834810375292880084979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97641785655334895360453221 18307834810375292880084979)
    ·
      refine ⟨27461752215562939320127469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18307834810375292880084979 27461752215562939320127469)
      ·
        refine ⟨10298157080836102245047801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27461752215562939320127469 10298157080836102245047801)
        ·
          refine ⟨7723617810627076683785851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10298157080836102245047801 7723617810627076683785851)
          ·
            refine ⟨11585426715940615025678777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723617810627076683785851 11585426715940615025678777)
            ·
              refine ⟨8689070036955461269259083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11585426715940615025678777 8689070036955461269259083)
              ·
                refine ⟨13033605055433191903888625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689070036955461269259083 13033605055433191903888625)
                ·
                  refine ⟨9775203791574893927916469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13033605055433191903888625 9775203791574893927916469)
                  ·
                    refine ⟨916425355460146305742169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9775203791574893927916469 916425355460146305742169)
                    ·
                      rfl

theorem cell23_5354196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_5354196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354196 prefixEnd_5354196 := by exact prefixLift 5354196
  have htrace : WordTrace (prefixWord ++ tailWord_5354196) baseStart_5354196 baseEnd_5354196 := by
    simpa [prefixWord, tailWord_5354196, baseEnd_5354196] using wordTrace_append hprefix tailTrace_5354196
  have hstable : (prefixWord ++ tailWord_5354196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354196).length < 2 ^ (prefixWord ++ tailWord_5354196).sum := by decide
  have hdescent : baseEnd_5354196 < baseStart_5354196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354199 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_5354199 : Nat := 118140960795 + 5354199 * 2 ^ 59
def prefixEnd_5354199 : Nat := 4983230072969 + 3 ^ 40 * 5354199 * 2
def baseEnd_5354199 : Nat := 2749277606822402405488993

theorem tailTrace_5354199 : CollatzResearch.WordTrace tailWord_5354199 prefixEnd_5354199 2749277606822402405488993 := by
  unfold tailWord_5354199
  simp only [CollatzResearch.WordTrace]
  refine ⟨195283680729658922233265651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130189120486439281488843767 195283680729658922233265651)
  ·
    refine ⟨292925521094488383349898477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195283680729658922233265651 292925521094488383349898477)
    ·
      refine ⟨109847070410433143756211929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292925521094488383349898477 109847070410433143756211929)
      ·
        refine ⟨82385302807824857817158947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109847070410433143756211929 82385302807824857817158947)
        ·
          refine ⟨123577954211737286725738421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82385302807824857817158947 123577954211737286725738421)
          ·
            refine ⟨11585433207350370630537977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123577954211737286725738421 11585433207350370630537977)
            ·
              refine ⟨8689074905512777972903483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11585433207350370630537977 8689074905512777972903483)
              ·
                refine ⟨13033612358269166959355225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689074905512777972903483 13033612358269166959355225)
                ·
                  refine ⟨9775209268701875219516419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13033612358269166959355225 9775209268701875219516419)
                  ·
                    refine ⟨14662813903052812829274629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9775209268701875219516419 14662813903052812829274629)
                    ·
                      refine ⟨2749277606822402405488993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14662813903052812829274629 2749277606822402405488993)
                      ·
                        rfl

theorem cell23_5354199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_5354199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354199 prefixEnd_5354199 := by exact prefixLift 5354199
  have htrace : WordTrace (prefixWord ++ tailWord_5354199) baseStart_5354199 baseEnd_5354199 := by
    simpa [prefixWord, tailWord_5354199, baseEnd_5354199] using wordTrace_append hprefix tailTrace_5354199
  have hstable : (prefixWord ++ tailWord_5354199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354199).length < 2 ^ (prefixWord ++ tailWord_5354199).sum := by decide
  have hdescent : baseEnd_5354199 < baseStart_5354199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354249 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 3]
def baseStart_5354249 : Nat := 118140960795 + 5354249 * 2 ^ 59
def prefixEnd_5354249 : Nat := 4983230072969 + 3 ^ 40 * 5354249 * 2
def baseEnd_5354249 : Nat := 2749303280855127209863763

theorem tailTrace_5354249 : CollatzResearch.WordTrace tailWord_5354249 prefixEnd_5354249 2749303280855127209863763 := by
  unfold tailWord_5354249
  simp only [CollatzResearch.WordTrace]
  refine ⟨195285504379477780772585801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130190336252985187181723867 195285504379477780772585801)
  ·
    refine ⟨146464128284608335579439351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195285504379477780772585801 146464128284608335579439351)
    ·
      refine ⟨219696192426912503369159027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146464128284608335579439351 219696192426912503369159027)
      ·
        refine ⟨329544288640368755053738541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219696192426912503369159027 329544288640368755053738541)
        ·
          refine ⟨123579108240138283145151953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329544288640368755053738541 123579108240138283145151953)
          ·
            refine ⟨92684331180103712358863965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123579108240138283145151953 92684331180103712358863965)
            ·
              refine ⟨34756624192538892134573987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92684331180103712358863965 34756624192538892134573987)
              ·
                refine ⟨52134936288808338201860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34756624192538892134573987 52134936288808338201860981)
                ·
                  refine ⟨4887650277075781706424467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52134936288808338201860981 4887650277075781706424467)
                  ·
                    refine ⟨7331475415613672559636701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4887650277075781706424467 7331475415613672559636701)
                    ·
                      refine ⟨2749303280855127209863763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7331475415613672559636701 2749303280855127209863763)
                      ·
                        rfl

theorem cell23_5354249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_5354249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354249 prefixEnd_5354249 := by exact prefixLift 5354249
  have htrace : WordTrace (prefixWord ++ tailWord_5354249) baseStart_5354249 baseEnd_5354249 := by
    simpa [prefixWord, tailWord_5354249, baseEnd_5354249] using wordTrace_append hprefix tailTrace_5354249
  have hstable : (prefixWord ++ tailWord_5354249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354249).length < 2 ^ (prefixWord ++ tailWord_5354249).sum := by decide
  have hdescent : baseEnd_5354249 < baseStart_5354249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354259 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 5, 2]
def baseStart_5354259 : Nat := 118140960795 + 5354259 * 2 ^ 59
def prefixEnd_5354259 : Nat := 4983230072969 + 3 ^ 40 * 5354259 * 2
def baseEnd_5354259 : Nat := 2749308415661672170738717

theorem tailTrace_5354259 : CollatzResearch.WordTrace tailWord_5354259 prefixEnd_5354259 2749308415661672170738717 := by
  unfold tailWord_5354259
  simp only [CollatzResearch.WordTrace]
  refine ⟨195285869109441552480449831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130190579406294368320299887 195285869109441552480449831)
  ·
    refine ⟨292928803664162328720674747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195285869109441552480449831 292928803664162328720674747)
    ·
      refine ⟨439393205496243493081012121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292928803664162328720674747 439393205496243493081012121)
      ·
        refine ⟨329544904122182619810759091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439393205496243493081012121 329544904122182619810759091)
        ·
          refine ⟨494317356183273929716138637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329544904122182619810759091 494317356183273929716138637)
          ·
            refine ⟨185369008568727723643551989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494317356183273929716138637 185369008568727723643551989)
            ·
              refine ⟨17378344553318224091582999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185369008568727723643551989 17378344553318224091582999)
              ·
                refine ⟨26067516829977336137374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17378344553318224091582999 26067516829977336137374499)
                ·
                  refine ⟨39101275244966004206061749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26067516829977336137374499 39101275244966004206061749)
                  ·
                    refine ⟨3665744554215562894318289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39101275244966004206061749 3665744554215562894318289)
                    ·
                      refine ⟨2749308415661672170738717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665744554215562894318289 2749308415661672170738717)
                      ·
                        rfl

theorem cell23_5354259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 5, 2].length) (baseStart_5354259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354259 prefixEnd_5354259 := by exact prefixLift 5354259
  have htrace : WordTrace (prefixWord ++ tailWord_5354259) baseStart_5354259 baseEnd_5354259 := by
    simpa [prefixWord, tailWord_5354259, baseEnd_5354259] using wordTrace_append hprefix tailTrace_5354259
  have hstable : (prefixWord ++ tailWord_5354259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354259).length < 2 ^ (prefixWord ++ tailWord_5354259).sum := by decide
  have hdescent : baseEnd_5354259 < baseStart_5354259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354312 : List Nat := [2, 1, 3, 1, 1, 3, 3, 9]
def baseStart_5354312 : Nat := 118140960795 + 5354312 * 2 ^ 59
def prefixEnd_5354312 : Nat := 4983230072969 + 3 ^ 40 * 5354312 * 2
def baseEnd_5354312 : Nat := 101827245560605943087999

theorem tailTrace_5354312 : CollatzResearch.WordTrace tailWord_5354312 prefixEnd_5354312 101827245560605943087999 := by
  unfold tailWord_5354312
  simp only [CollatzResearch.WordTrace]
  refine ⟨97643901089124771266064595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130191868118833028354752793 97643901089124771266064595)
  ·
    refine ⟨146465851633687156899096893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97643901089124771266064595 146465851633687156899096893)
    ·
      refine ⟨54924694362632683837161335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146465851633687156899096893 54924694362632683837161335)
      ·
        refine ⟨82387041543949025755742003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54924694362632683837161335 82387041543949025755742003)
        ·
          refine ⟨123580562315923538633613005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82387041543949025755742003 123580562315923538633613005)
          ·
            refine ⟨46342710868471326987604877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123580562315923538633613005 46342710868471326987604877)
            ·
              refine ⟨17378516575676747620351829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46342710868471326987604877 17378516575676747620351829)
              ·
                refine ⟨101827245560605943087999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17378516575676747620351829 101827245560605943087999)
                ·
                  rfl

theorem cell23_5354312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 9].length) (baseStart_5354312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354312 prefixEnd_5354312 := by exact prefixLift 5354312
  have htrace : WordTrace (prefixWord ++ tailWord_5354312) baseStart_5354312 baseEnd_5354312 := by
    simpa [prefixWord, tailWord_5354312, baseEnd_5354312] using wordTrace_append hprefix tailTrace_5354312
  have hstable : (prefixWord ++ tailWord_5354312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354312).length < 2 ^ (prefixWord ++ tailWord_5354312).sum := by decide
  have hdescent : baseEnd_5354312 < baseStart_5354312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354340 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_5354340 : Nat := 118140960795 + 5354340 * 2 ^ 59
def prefixEnd_5354340 : Nat := 4983230072969 + 3 ^ 40 * 5354340 * 2
def baseEnd_5354340 : Nat := 2749350007594686353825845

theorem tailTrace_5354340 : CollatzResearch.WordTrace tailWord_5354340 prefixEnd_5354340 2749350007594686353825845 := by
  unfold tailWord_5354340
  simp only [CollatzResearch.WordTrace]
  refine ⟨97644411711074051657074237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130192548948098735542765649 97644411711074051657074237)
  ·
    refine ⟨36616654391652769371402839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97644411711074051657074237 36616654391652769371402839)
    ·
      refine ⟨54924981587479154057104259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36616654391652769371402839 54924981587479154057104259)
      ·
        refine ⟨82387472381218731085656389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54924981587479154057104259 82387472381218731085656389)
        ·
          refine ⟨15447651071478512078560573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82387472381218731085656389 15447651071478512078560573)
          ·
            refine ⟨5792869151804442029460215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15447651071478512078560573 5792869151804442029460215)
            ·
              refine ⟨8689303727706663044190323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792869151804442029460215 8689303727706663044190323)
              ·
                refine ⟨13033955591559994566285485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689303727706663044190323 13033955591559994566285485)
                ·
                  refine ⟨4887733346834997962357057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13033955591559994566285485 4887733346834997962357057)
                  ·
                    refine ⟨3665800010126248471767793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4887733346834997962357057 3665800010126248471767793)
                    ·
                      refine ⟨2749350007594686353825845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665800010126248471767793 2749350007594686353825845)
                      ·
                        rfl

theorem cell23_5354340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_5354340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354340 prefixEnd_5354340 := by exact prefixLift 5354340
  have htrace : WordTrace (prefixWord ++ tailWord_5354340) baseStart_5354340 baseEnd_5354340 := by
    simpa [prefixWord, tailWord_5354340, baseEnd_5354340] using wordTrace_append hprefix tailTrace_5354340
  have hstable : (prefixWord ++ tailWord_5354340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354340).length < 2 ^ (prefixWord ++ tailWord_5354340).sum := by decide
  have hdescent : baseEnd_5354340 < baseStart_5354340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354362 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_5354362 : Nat := 118140960795 + 5354362 * 2 ^ 59
def prefixEnd_5354362 : Nat := 4983230072969 + 3 ^ 40 * 5354362 * 2
def baseEnd_5354362 : Nat := 2749361304169085267750743

theorem tailTrace_5354362 : CollatzResearch.WordTrace tailWord_5354362 prefixEnd_5354362 2749361304169085267750743 := by
  unfold tailWord_5354362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48822406457017100267862335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130193083885378934047632893 48822406457017100267862335)
  ·
    refine ⟨73233609685525650401793503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48822406457017100267862335 73233609685525650401793503)
    ·
      refine ⟨109850414528288475602690255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73233609685525650401793503 109850414528288475602690255)
      ·
        refine ⟨164775621792432713404035383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109850414528288475602690255 164775621792432713404035383)
        ·
          refine ⟨247163432688649070106053075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164775621792432713404035383 247163432688649070106053075)
          ·
            refine ⟨370745149032973605159079613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247163432688649070106053075 370745149032973605159079613)
            ·
              refine ⟨139029430887365101934654855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370745149032973605159079613 139029430887365101934654855)
              ·
                refine ⟨208544146331047652901982283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139029430887365101934654855 208544146331047652901982283)
                ·
                  refine ⟨312816219496571479352973425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208544146331047652901982283 312816219496571479352973425)
                  ·
                    refine ⟨234612164622428609514730069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312816219496571479352973425 234612164622428609514730069)
                    ·
                      refine ⟨2749361304169085267750743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 234612164622428609514730069 2749361304169085267750743)
                      ·
                        rfl

theorem cell23_5354362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_5354362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354362 prefixEnd_5354362 := by exact prefixLift 5354362
  have htrace : WordTrace (prefixWord ++ tailWord_5354362) baseStart_5354362 baseEnd_5354362 := by
    simpa [prefixWord, tailWord_5354362, baseEnd_5354362] using wordTrace_append hprefix tailTrace_5354362
  have hstable : (prefixWord ++ tailWord_5354362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354362).length < 2 ^ (prefixWord ++ tailWord_5354362).sum := by decide
  have hdescent : baseEnd_5354362 < baseStart_5354362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354370 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5354370 : Nat := 118140960795 + 5354370 * 2 ^ 59
def prefixEnd_5354370 : Nat := 4983230072969 + 3 ^ 40 * 5354370 * 2
def baseEnd_5354370 : Nat := 2749365412014321236450707

theorem tailTrace_5354370 : CollatzResearch.WordTrace tailWord_5354370 prefixEnd_5354370 2749365412014321236450707 := by
  unfold tailWord_5354370
  simp only [CollatzResearch.WordTrace]
  refine ⟨48822479403009854609435141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130193278408026278958493709 48822479403009854609435141)
  ·
    refine ⟨9154214888064347739269089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48822479403009854609435141 9154214888064347739269089)
    ·
      refine ⟨6865661166048260804451817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9154214888064347739269089 6865661166048260804451817)
      ·
        refine ⟨5149245874536195603338863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865661166048260804451817 5149245874536195603338863)
        ·
          refine ⟨7723868811804293405008295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149245874536195603338863 7723868811804293405008295)
          ·
            refine ⟨11585803217706440107512443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723868811804293405008295 11585803217706440107512443)
            ·
              refine ⟨17378704826559660161268665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11585803217706440107512443 17378704826559660161268665)
              ·
                refine ⟨13034028619919745120951499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17378704826559660161268665 13034028619919745120951499)
                ·
                  refine ⟨19551042929879617681427249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13034028619919745120951499 19551042929879617681427249)
                  ·
                    refine ⟨14663282197409713261070437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19551042929879617681427249 14663282197409713261070437)
                    ·
                      refine ⟨2749365412014321236450707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14663282197409713261070437 2749365412014321236450707)
                      ·
                        rfl

theorem cell23_5354370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5354370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354370 prefixEnd_5354370 := by exact prefixLift 5354370
  have htrace : WordTrace (prefixWord ++ tailWord_5354370) baseStart_5354370 baseEnd_5354370 := by
    simpa [prefixWord, tailWord_5354370, baseEnd_5354370] using wordTrace_append hprefix tailTrace_5354370
  have hstable : (prefixWord ++ tailWord_5354370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354370).length < 2 ^ (prefixWord ++ tailWord_5354370).sum := by decide
  have hdescent : baseEnd_5354370 < baseStart_5354370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354409 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_5354409 : Nat := 118140960795 + 5354409 * 2 ^ 59
def prefixEnd_5354409 : Nat := 4983230072969 + 3 ^ 40 * 5354409 * 2
def baseEnd_5354409 : Nat := 2749385437759846583863027

theorem tailTrace_5354409 : CollatzResearch.WordTrace tailWord_5354409 prefixEnd_5354409 2749385437759846583863027 := by
  unfold tailWord_5354409
  simp only [CollatzResearch.WordTrace]
  refine ⟨195291340058898128098410281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130194226705932085398940187 195291340058898128098410281)
  ·
    refine ⟨146468505044173596073807711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195291340058898128098410281 146468505044173596073807711)
    ·
      refine ⟨219702757566260394110711567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146468505044173596073807711 219702757566260394110711567)
      ·
        refine ⟨329554136349390591166067351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219702757566260394110711567 329554136349390591166067351)
        ·
          refine ⟨494331204524085886749101027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329554136349390591166067351 494331204524085886749101027)
          ·
            refine ⟨741496806786128830123651541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494331204524085886749101027 741496806786128830123651541)
            ·
              refine ⟨17378831409049894456023083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 741496806786128830123651541 17378831409049894456023083)
              ·
                refine ⟨26068247113574841684034625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17378831409049894456023083 26068247113574841684034625)
                ·
                  refine ⟨19551185335181131263025969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26068247113574841684034625 19551185335181131263025969)
                  ·
                    refine ⟨14663389001385848447269477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19551185335181131263025969 14663389001385848447269477)
                    ·
                      refine ⟨2749385437759846583863027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14663389001385848447269477 2749385437759846583863027)
                      ·
                        rfl

theorem cell23_5354409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_5354409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354409 prefixEnd_5354409 := by exact prefixLift 5354409
  have htrace : WordTrace (prefixWord ++ tailWord_5354409) baseStart_5354409 baseEnd_5354409 := by
    simpa [prefixWord, tailWord_5354409, baseEnd_5354409] using wordTrace_append hprefix tailTrace_5354409
  have hstable : (prefixWord ++ tailWord_5354409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354409).length < 2 ^ (prefixWord ++ tailWord_5354409).sum := by decide
  have hdescent : baseEnd_5354409 < baseStart_5354409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354446 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_5354446 : Nat := 118140960795 + 5354446 * 2 ^ 59
def prefixEnd_5354446 : Nat := 4983230072969 + 3 ^ 40 * 5354446 * 2
def baseEnd_5354446 : Nat := 2749404436544062939100357

theorem tailTrace_5354446 : CollatzResearch.WordTrace tailWord_5354446 prefixEnd_5354446 2749404436544062939100357 := by
  unfold tailWord_5354446
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411586194970510427188399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130195126373176055611671461 24411586194970510427188399)
  ·
    refine ⟨36617379292455765640782599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24411586194970510427188399 36617379292455765640782599)
    ·
      refine ⟨54926068938683648461173899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36617379292455765640782599 54926068938683648461173899)
      ·
        refine ⟨82389103408025472691760849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54926068938683648461173899 82389103408025472691760849)
        ·
          refine ⟨61791827556019104518820637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82389103408025472691760849 61791827556019104518820637)
          ·
            refine ⟨23171935333507164194557739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61791827556019104518820637 23171935333507164194557739)
            ·
              refine ⟨34757903000260746291836609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23171935333507164194557739 34757903000260746291836609)
              ·
                refine ⟨26068427250195559718877457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34757903000260746291836609 26068427250195559718877457)
                ·
                  refine ⟨19551320437646669789158093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26068427250195559718877457 19551320437646669789158093)
                  ·
                    refine ⟨7331745164117501170934285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19551320437646669789158093 7331745164117501170934285)
                    ·
                      refine ⟨2749404436544062939100357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7331745164117501170934285 2749404436544062939100357)
                      ·
                        rfl

theorem cell23_5354446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_5354446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354446 prefixEnd_5354446 := by exact prefixLift 5354446
  have htrace : WordTrace (prefixWord ++ tailWord_5354446) baseStart_5354446 baseEnd_5354446 := by
    simpa [prefixWord, tailWord_5354446, baseEnd_5354446] using wordTrace_append hprefix tailTrace_5354446
  have hstable : (prefixWord ++ tailWord_5354446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354446).length < 2 ^ (prefixWord ++ tailWord_5354446).sum := by decide
  have hdescent : baseEnd_5354446 < baseStart_5354446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354449 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_5354449 : Nat := 118140960795 + 5354449 * 2 ^ 59
def prefixEnd_5354449 : Nat := 4983230072969 + 3 ^ 40 * 5354449 * 2
def baseEnd_5354449 : Nat := 916468658995342142454281

theorem tailTrace_5354449 : CollatzResearch.WordTrace tailWord_5354449 prefixEnd_5354449 916468658995342142454281 := by
  unfold tailWord_5354449
  simp only [CollatzResearch.WordTrace]
  refine ⟨195292798978753214929866401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130195199319168809953244267 195292798978753214929866401)
  ·
    refine ⟨146469599234064911197399801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195292798978753214929866401 146469599234064911197399801)
    ·
      refine ⟨109852199425548683398049851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146469599234064911197399801 109852199425548683398049851)
      ·
        refine ⟨164778299138323025097074777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109852199425548683398049851 164778299138323025097074777)
        ·
          refine ⟨123583724353742268822806083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164778299138323025097074777 123583724353742268822806083)
          ·
            refine ⟨185375586530613403234209125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123583724353742268822806083 185375586530613403234209125)
            ·
              refine ⟨34757922474490013106414211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185375586530613403234209125 34757922474490013106414211)
              ·
                refine ⟨52136883711735019659621317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34757922474490013106414211 52136883711735019659621317)
                ·
                  refine ⟨9775665695950316186178997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52136883711735019659621317 9775665695950316186178997)
                  ·
                    refine ⟨916468658995342142454281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9775665695950316186178997 916468658995342142454281)
                    ·
                      rfl

theorem cell23_5354449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_5354449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354449 prefixEnd_5354449 := by exact prefixLift 5354449
  have htrace : WordTrace (prefixWord ++ tailWord_5354449) baseStart_5354449 baseEnd_5354449 := by
    simpa [prefixWord, tailWord_5354449, baseEnd_5354449] using wordTrace_append hprefix tailTrace_5354449
  have hstable : (prefixWord ++ tailWord_5354449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354449).length < 2 ^ (prefixWord ++ tailWord_5354449).sum := by decide
  have hdescent : baseEnd_5354449 < baseStart_5354449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354513 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 1, 4]
def baseStart_5354513 : Nat := 118140960795 + 5354513 * 2 ^ 59
def prefixEnd_5354513 : Nat := 4983230072969 + 3 ^ 40 * 5354513 * 2
def baseEnd_5354513 : Nat := 916479613249304725654183

theorem tailTrace_5354513 : CollatzResearch.WordTrace tailWord_5354513 prefixEnd_5354513 916479613249304725654183 := by
  unfold tailWord_5354513
  simp only [CollatzResearch.WordTrace]
  refine ⟨195295133250521353860196193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130196755500347569240130795 195295133250521353860196193)
  ·
    refine ⟨146471349937891015395147145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195295133250521353860196193 146471349937891015395147145)
    ·
      refine ⟨109853512453418261546360359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146471349937891015395147145 109853512453418261546360359)
      ·
        refine ⟨164780268680127392319540539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109853512453418261546360359 164780268680127392319540539)
        ·
          refine ⟨247170403020191088479310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164780268680127392319540539 247170403020191088479310809)
          ·
            refine ⟨185377802265143316359483107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247170403020191088479310809 185377802265143316359483107)
            ·
              refine ⟨278066703397714974539224661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185377802265143316359483107 278066703397714974539224661)
              ·
                refine ⟨3258594180441972357881539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 278066703397714974539224661 3258594180441972357881539)
                ·
                  refine ⟨4887891270662958536822309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258594180441972357881539 4887891270662958536822309)
                  ·
                    refine ⟨916479613249304725654183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4887891270662958536822309 916479613249304725654183)
                    ·
                      rfl

theorem cell23_5354513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_5354513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354513 prefixEnd_5354513 := by exact prefixLift 5354513
  have htrace : WordTrace (prefixWord ++ tailWord_5354513) baseStart_5354513 baseEnd_5354513 := by
    simpa [prefixWord, tailWord_5354513, baseEnd_5354513] using wordTrace_append hprefix tailTrace_5354513
  have hstable : (prefixWord ++ tailWord_5354513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354513).length < 2 ^ (prefixWord ++ tailWord_5354513).sum := by decide
  have hdescent : baseEnd_5354513 < baseStart_5354513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354563 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 2, 3, 2]
def baseStart_5354563 : Nat := 118140960795 + 5354563 * 2 ^ 59
def prefixEnd_5354563 : Nat := 4983230072969 + 3 ^ 40 * 5354563 * 2
def baseEnd_5354563 : Nat := 2749464513780638981337319

theorem tailTrace_5354563 : CollatzResearch.WordTrace tailWord_5354563 prefixEnd_5354563 2749464513780638981337319 := by
  unfold tailWord_5354563
  simp only [CollatzResearch.WordTrace]
  refine ⟨195296956900340212399516343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130197971266893474933010895 195296956900340212399516343)
  ·
    refine ⟨292945435350510318599274515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195296956900340212399516343 292945435350510318599274515)
    ·
      refine ⟨439418153025765477898911773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292945435350510318599274515 439418153025765477898911773)
      ·
        refine ⟨164781807384662054212091915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439418153025765477898911773 164781807384662054212091915)
        ·
          refine ⟨247172711076993081318137873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164781807384662054212091915 247172711076993081318137873)
          ·
            refine ⟨185379533307744810988603405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247172711076993081318137873 185379533307744810988603405)
            ·
              refine ⟨69517324990404304120726277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185379533307744810988603405 69517324990404304120726277)
              ·
                refine ⟨13034498435700807022636177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69517324990404304120726277 13034498435700807022636177)
                ·
                  refine ⟨9775873826775605266977133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13034498435700807022636177 9775873826775605266977133)
                  ·
                    refine ⟨3665952685040851975116425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9775873826775605266977133 3665952685040851975116425)
                    ·
                      refine ⟨2749464513780638981337319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665952685040851975116425 2749464513780638981337319)
                      ·
                        rfl

theorem cell23_5354563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_5354563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354563 prefixEnd_5354563 := by exact prefixLift 5354563
  have htrace : WordTrace (prefixWord ++ tailWord_5354563) baseStart_5354563 baseEnd_5354563 := by
    simpa [prefixWord, tailWord_5354563, baseEnd_5354563] using wordTrace_append hprefix tailTrace_5354563
  have hstable : (prefixWord ++ tailWord_5354563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354563).length < 2 ^ (prefixWord ++ tailWord_5354563).sum := by decide
  have hdescent : baseEnd_5354563 < baseStart_5354563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354573 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5354573 : Nat := 118140960795 + 5354573 * 2 ^ 59
def prefixEnd_5354573 : Nat := 4983230072969 + 3 ^ 40 * 5354573 * 2
def baseEnd_5354573 : Nat := 916489882862394647404091

theorem tailTrace_5354573 : CollatzResearch.WordTrace tailWord_5354573 prefixEnd_5354573 916489882862394647404091 := by
  unfold tailWord_5354573
  simp only [CollatzResearch.WordTrace]
  refine ⟨195297321630303984107380373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130198214420202656071586915 195297321630303984107380373)
  ·
    refine ⟨9154561951420499255033455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195297321630303984107380373 9154561951420499255033455)
    ·
      refine ⟨13731842927130748882550183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9154561951420499255033455 13731842927130748882550183)
      ·
        refine ⟨20597764390696123323825275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731842927130748882550183 20597764390696123323825275)
        ·
          refine ⟨30896646586044184985737913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20597764390696123323825275 30896646586044184985737913)
          ·
            refine ⟨23172484939533138739303435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30896646586044184985737913 23172484939533138739303435)
            ·
              refine ⟨34758727409299708108955153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23172484939533138739303435 34758727409299708108955153)
              ·
                refine ⟨26069045556974781081716365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34758727409299708108955153 26069045556974781081716365)
                ·
                  refine ⟨9775892083865542905643637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26069045556974781081716365 9775892083865542905643637)
                  ·
                    refine ⟨916489882862394647404091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9775892083865542905643637 916489882862394647404091)
                    ·
                      rfl

theorem cell23_5354573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5354573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354573 prefixEnd_5354573 := by exact prefixLift 5354573
  have htrace : WordTrace (prefixWord ++ tailWord_5354573) baseStart_5354573 baseEnd_5354573 := by
    simpa [prefixWord, tailWord_5354573, baseEnd_5354573] using wordTrace_append hprefix tailTrace_5354573
  have hstable : (prefixWord ++ tailWord_5354573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354573).length < 2 ^ (prefixWord ++ tailWord_5354573).sum := by decide
  have hdescent : baseEnd_5354573 < baseStart_5354573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354610 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_5354610 : Nat := 118140960795 + 5354610 * 2 ^ 59
def prefixEnd_5354610 : Nat := 4983230072969 + 3 ^ 40 * 5354610 * 2
def baseEnd_5354610 : Nat := 2749488647371400297449603

theorem tailTrace_5354610 : CollatzResearch.WordTrace tailWord_5354610 prefixEnd_5354610 2749488647371400297449603 := by
  unfold tailWord_5354610
  simp only [CollatzResearch.WordTrace]
  refine ⟨48824667782792484856619321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130199114087446626284318189 48824667782792484856619321)
  ·
    refine ⟨36618500837094363642464491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48824667782792484856619321 36618500837094363642464491)
    ·
      refine ⟨54927751255641545463696737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36618500837094363642464491 54927751255641545463696737)
      ·
        refine ⟨41195813441731159097772553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54927751255641545463696737 41195813441731159097772553)
        ·
          refine ⟨30896860081298369323329415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41195813441731159097772553 30896860081298369323329415)
          ·
            refine ⟨46345290121947553984994123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30896860081298369323329415 46345290121947553984994123)
            ·
              refine ⟨69517935182921330977491185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46345290121947553984994123 69517935182921330977491185)
              ·
                refine ⟨52138451387190998233118389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69517935182921330977491185 52138451387190998233118389)
                ·
                  refine ⟨4887979817549156084354849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52138451387190998233118389 4887979817549156084354849)
                  ·
                    refine ⟨3665984863161867063266137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4887979817549156084354849 3665984863161867063266137)
                    ·
                      refine ⟨2749488647371400297449603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665984863161867063266137 2749488647371400297449603)
                      ·
                        rfl

theorem cell23_5354610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_5354610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354610 prefixEnd_5354610 := by exact prefixLift 5354610
  have htrace : WordTrace (prefixWord ++ tailWord_5354610) baseStart_5354610 baseEnd_5354610 := by
    simpa [prefixWord, tailWord_5354610, baseEnd_5354610] using wordTrace_append hprefix tailTrace_5354610
  have hstable : (prefixWord ++ tailWord_5354610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354610).length < 2 ^ (prefixWord ++ tailWord_5354610).sum := by decide
  have hdescent : baseEnd_5354610 < baseStart_5354610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354627 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 1, 2, 2]
def baseStart_5354627 : Nat := 118140960795 + 5354627 * 2 ^ 59
def prefixEnd_5354627 : Nat := 4983230072969 + 3 ^ 40 * 5354627 * 2
def baseEnd_5354627 : Nat := 2749497376542526730937025

theorem tailTrace_5354627 : CollatzResearch.WordTrace tailWord_5354627 prefixEnd_5354627 2749497376542526730937025 := by
  unfold tailWord_5354627
  simp only [CollatzResearch.WordTrace]
  refine ⟨195299291172108351329846135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130199527448072234219897423 195299291172108351329846135)
  ·
    refine ⟨292948936758162526994769203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195299291172108351329846135 292948936758162526994769203)
    ·
      refine ⟨439423405137243790492153805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292948936758162526994769203 439423405137243790492153805)
      ·
        refine ⟨164783776926466421434557677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439423405137243790492153805 164783776926466421434557677)
        ·
          refine ⟨61793916347424908037959129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164783776926466421434557677 61793916347424908037959129)
          ·
            refine ⟨46345437260568681028469347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61793916347424908037959129 46345437260568681028469347)
            ·
              refine ⟨69518155890853021542704021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46345437260568681028469347 69518155890853021542704021)
              ·
                refine ⟨3258663557383735384814251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69518155890853021542704021 3258663557383735384814251)
                ·
                  refine ⟨4887995336075603077221377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258663557383735384814251 4887995336075603077221377)
                  ·
                    refine ⟨3665996502056702307916033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4887995336075603077221377 3665996502056702307916033)
                    ·
                      refine ⟨2749497376542526730937025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3665996502056702307916033 2749497376542526730937025)
                      ·
                        rfl

theorem cell23_5354627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_5354627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354627 prefixEnd_5354627 := by exact prefixLift 5354627
  have htrace : WordTrace (prefixWord ++ tailWord_5354627) baseStart_5354627 baseEnd_5354627 := by
    simpa [prefixWord, tailWord_5354627, baseEnd_5354627] using wordTrace_append hprefix tailTrace_5354627
  have hstable : (prefixWord ++ tailWord_5354627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354627).length < 2 ^ (prefixWord ++ tailWord_5354627).sum := by decide
  have hdescent : baseEnd_5354627 < baseStart_5354627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354643 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3]
def baseStart_5354643 : Nat := 118140960795 + 5354643 * 2 ^ 59
def prefixEnd_5354643 : Nat := 4983230072969 + 3 ^ 40 * 5354643 * 2
def baseEnd_5354643 : Nat := 2749505592232998668336951

theorem tailTrace_5354643 : CollatzResearch.WordTrace tailWord_5354643 prefixEnd_5354643 2749505592232998668336951 := by
  unfold tailWord_5354643
  simp only [CollatzResearch.WordTrace]
  refine ⟨195299874740050386062428583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130199916493366924041619055 195299874740050386062428583)
  ·
    refine ⟨292949812110075579093642875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195299874740050386062428583 292949812110075579093642875)
    ·
      refine ⟨439424718165113368640464313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292949812110075579093642875 439424718165113368640464313)
      ·
        refine ⟨329568538623835026480348235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439424718165113368640464313 329568538623835026480348235)
        ·
          refine ⟨494352807935752539720522353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329568538623835026480348235 494352807935752539720522353)
          ·
            refine ⟨370764605951814404790391765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494352807935752539720522353 370764605951814404790391765)
            ·
              refine ⟨8689795451995650112274807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 370764605951814404790391765 8689795451995650112274807)
              ·
                refine ⟨13034693177993475168412211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689795451995650112274807 13034693177993475168412211)
                ·
                  refine ⟨19552039766990212752618317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13034693177993475168412211 19552039766990212752618317)
                  ·
                    refine ⟨7332014912621329782231869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19552039766990212752618317 7332014912621329782231869)
                    ·
                      refine ⟨2749505592232998668336951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332014912621329782231869 2749505592232998668336951)
                      ·
                        rfl

theorem cell23_5354643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_5354643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354643 prefixEnd_5354643 := by exact prefixLift 5354643
  have htrace : WordTrace (prefixWord ++ tailWord_5354643) baseStart_5354643 baseEnd_5354643 := by
    simpa [prefixWord, tailWord_5354643, baseEnd_5354643] using wordTrace_append hprefix tailTrace_5354643
  have hstable : (prefixWord ++ tailWord_5354643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354643).length < 2 ^ (prefixWord ++ tailWord_5354643).sum := by decide
  have hdescent : baseEnd_5354643 < baseStart_5354643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354650 : List Nat := [3, 1, 1, 5, 1, 3, 2, 7]
def baseStart_5354650 : Nat := 118140960795 + 5354650 * 2 ^ 59
def prefixEnd_5354650 : Nat := 4983230072969 + 3 ^ 40 * 5354650 * 2
def baseEnd_5354650 : Nat := 101833673577688153368497

theorem tailTrace_5354650 : CollatzResearch.WordTrace tailWord_5354650 prefixEnd_5354650 101833673577688153368497 := by
  unfold tailWord_5354650
  simp only [CollatzResearch.WordTrace]
  refine ⟨48825032512756256564483351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130200086700683350838622269 48825032512756256564483351)
  ·
    refine ⟨73237548769134384846725027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48825032512756256564483351 73237548769134384846725027)
    ·
      refine ⟨109856323153701577270087541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73237548769134384846725027 109856323153701577270087541)
      ·
        refine ⟨10299030295659522869070707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109856323153701577270087541 10299030295659522869070707)
        ·
          refine ⟨15448545443489284303606061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10299030295659522869070707 15448545443489284303606061)
          ·
            refine ⟨5793204541308481613852273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15448545443489284303606061 5793204541308481613852273)
            ·
              refine ⟨4344903405981361210389205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5793204541308481613852273 4344903405981361210389205)
              ·
                refine ⟨101833673577688153368497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4344903405981361210389205 101833673577688153368497)
                ·
                  rfl

theorem cell23_5354650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_5354650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354650 prefixEnd_5354650 := by exact prefixLift 5354650
  have htrace : WordTrace (prefixWord ++ tailWord_5354650) baseStart_5354650 baseEnd_5354650 := by
    simpa [prefixWord, tailWord_5354650, baseEnd_5354650] using wordTrace_append hprefix tailTrace_5354650
  have hstable : (prefixWord ++ tailWord_5354650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354650).length < 2 ^ (prefixWord ++ tailWord_5354650).sum := by decide
  have hdescent : baseEnd_5354650 < baseStart_5354650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354656 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5354656 : Nat := 118140960795 + 5354656 * 2 ^ 59
def prefixEnd_5354656 : Nat := 4983230072969 + 3 ^ 40 * 5354656 * 2
def baseEnd_5354656 : Nat := 2749512267481507117474391

theorem tailTrace_5354656 : CollatzResearch.WordTrace tailWord_5354656 prefixEnd_5354656 2749512267481507117474391 := by
  unfold tailWord_5354656
  simp only [CollatzResearch.WordTrace]
  refine ⟨97650174444501644641325911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130200232592668859521767881 97650174444501644641325911)
  ·
    refine ⟨146475261666752466961988867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97650174444501644641325911 146475261666752466961988867)
    ·
      refine ⟨219712892500128700442983301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146475261666752466961988867 219712892500128700442983301)
      ·
        refine ⟨41196167343774131333059369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219712892500128700442983301 41196167343774131333059369)
        ·
          refine ⟨30897125507830598499794527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41196167343774131333059369 30897125507830598499794527)
          ·
            refine ⟨46345688261745897749691791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30897125507830598499794527 46345688261745897749691791)
            ·
              refine ⟨69518532392618846624537687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46345688261745897749691791 69518532392618846624537687)
              ·
                refine ⟨104277798588928269936806531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69518532392618846624537687 104277798588928269936806531)
                ·
                  refine ⟨156416697883392404905209797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104277798588928269936806531 156416697883392404905209797)
                  ·
                    refine ⟨29328130853136075919726837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156416697883392404905209797 29328130853136075919726837)
                    ·
                      refine ⟨2749512267481507117474391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29328130853136075919726837 2749512267481507117474391)
                      ·
                        rfl

theorem cell23_5354656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5354656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354656 prefixEnd_5354656 := by exact prefixLift 5354656
  have htrace : WordTrace (prefixWord ++ tailWord_5354656) baseStart_5354656 baseEnd_5354656 := by
    simpa [prefixWord, tailWord_5354656, baseEnd_5354656] using wordTrace_append hprefix tailTrace_5354656
  have hstable : (prefixWord ++ tailWord_5354656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354656).length < 2 ^ (prefixWord ++ tailWord_5354656).sum := by decide
  have hdescent : baseEnd_5354656 < baseStart_5354656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354660 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_5354660 : Nat := 118140960795 + 5354660 * 2 ^ 59
def prefixEnd_5354660 : Nat := 4983230072969 + 3 ^ 40 * 5354660 * 2
def baseEnd_5354660 : Nat := 2749514321404125101824373

theorem tailTrace_5354660 : CollatzResearch.WordTrace tailWord_5354660 prefixEnd_5354660 2749514321404125101824373 := by
  unfold tailWord_5354660
  simp only [CollatzResearch.WordTrace]
  refine ⟨97650247390494398982898717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130200329853992531977198289 97650247390494398982898717)
  ·
    refine ⟨36618842771435399618587019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97650247390494398982898717 36618842771435399618587019)
    ·
      refine ⟨54928264157153099427880529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36618842771435399618587019 54928264157153099427880529)
      ·
        refine ⟨41196198117864824570910397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54928264157153099427880529 41196198117864824570910397)
        ·
          refine ⟨15448574294199309214091399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41196198117864824570910397 15448574294199309214091399)
          ·
            refine ⟨23172861441298963821137099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15448574294199309214091399 23172861441298963821137099)
            ·
              refine ⟨34759292161948445731705649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23172861441298963821137099 34759292161948445731705649)
              ·
                refine ⟨26069469121461334298779237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34759292161948445731705649 26069469121461334298779237)
                ·
                  refine ⟨4888025460274000181021107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26069469121461334298779237 4888025460274000181021107)
                  ·
                    refine ⟨7332038190411000271531661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888025460274000181021107 7332038190411000271531661)
                    ·
                      refine ⟨2749514321404125101824373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332038190411000271531661 2749514321404125101824373)
                      ·
                        rfl

theorem cell23_5354660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_5354660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354660 prefixEnd_5354660 := by exact prefixLift 5354660
  have htrace : WordTrace (prefixWord ++ tailWord_5354660) baseStart_5354660 baseEnd_5354660 := by
    simpa [prefixWord, tailWord_5354660, baseEnd_5354660] using wordTrace_append hprefix tailTrace_5354660
  have hstable : (prefixWord ++ tailWord_5354660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354660).length < 2 ^ (prefixWord ++ tailWord_5354660).sum := by decide
  have hdescent : baseEnd_5354660 < baseStart_5354660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354678 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5354678 : Nat := 118140960795 + 5354678 * 2 ^ 59
def prefixEnd_5354678 : Nat := 4983230072969 + 3 ^ 40 * 5354678 * 2
def baseEnd_5354678 : Nat := 2749523564055906031399291

theorem tailTrace_5354678 : CollatzResearch.WordTrace tailWord_5354678 prefixEnd_5354678 2749523564055906031399291 := by
  unfold tailWord_5354678
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206321955932724189997043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130200767529949058026635125 12206321955932724189997043)
  ·
    refine ⟨18309482933899086284995565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12206321955932724189997043 18309482933899086284995565)
    ·
      refine ⟨6866056100212157356873337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18309482933899086284995565 6866056100212157356873337)
      ·
        refine ⟨5149542075159118017655003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6866056100212157356873337 5149542075159118017655003)
        ·
          refine ⟨7724313112738677026482505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149542075159118017655003 7724313112738677026482505)
          ·
            refine ⟨5793234834554007769861879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7724313112738677026482505 5793234834554007769861879)
            ·
              refine ⟨8689852251831011654792819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793234834554007769861879 8689852251831011654792819)
              ·
                refine ⟨13034778377746517482189229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689852251831011654792819 13034778377746517482189229)
                ·
                  refine ⟨4888041891654944055820961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13034778377746517482189229 4888041891654944055820961)
                  ·
                    refine ⟨3666031418741208041865721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888041891654944055820961 3666031418741208041865721)
                    ·
                      refine ⟨2749523564055906031399291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666031418741208041865721 2749523564055906031399291)
                      ·
                        rfl

theorem cell23_5354678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5354678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354678 prefixEnd_5354678 := by exact prefixLift 5354678
  have htrace : WordTrace (prefixWord ++ tailWord_5354678) baseStart_5354678 baseEnd_5354678 := by
    simpa [prefixWord, tailWord_5354678, baseEnd_5354678] using wordTrace_append hprefix tailTrace_5354678
  have hstable : (prefixWord ++ tailWord_5354678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354678).length < 2 ^ (prefixWord ++ tailWord_5354678).sum := by decide
  have hdescent : baseEnd_5354678 < baseStart_5354678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354683 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 5, 4, 2]
def baseStart_5354683 : Nat := 118140960795 + 5354683 * 2 ^ 59
def prefixEnd_5354683 : Nat := 4983230072969 + 3 ^ 40 * 5354683 * 2
def baseEnd_5354683 : Nat := 2749526131459178511836767

theorem tailTrace_5354683 : CollatzResearch.WordTrace tailWord_5354683 prefixEnd_5354683 2749526131459178511836767 := by
  unfold tailWord_5354683
  simp only [CollatzResearch.WordTrace]
  refine ⟨195301333659905472893884703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130200889106603648595923135 195301333659905472893884703)
  ·
    refine ⟨292952000489858209340827055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195301333659905472893884703 292952000489858209340827055)
    ·
      refine ⟨439428000734787314011240583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292952000489858209340827055 439428000734787314011240583)
      ·
        refine ⟨659142001102180971016860875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439428000734787314011240583 659142001102180971016860875)
        ·
          refine ⟨988713001653271456525291313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659142001102180971016860875 988713001653271456525291313)
          ·
            refine ⟨741534751239953592393968485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988713001653271456525291313 741534751239953592393968485)
            ·
              refine ⟨139037765857491298573869091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 741534751239953592393968485 139037765857491298573869091)
              ·
                refine ⟨208556648786236947860803637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139037765857491298573869091 208556648786236947860803637)
                ·
                  refine ⟨19552185823709713861950341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208556648786236947860803637 19552185823709713861950341)
                  ·
                    refine ⟨3666034841945571349115689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19552185823709713861950341 3666034841945571349115689)
                    ·
                      refine ⟨2749526131459178511836767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666034841945571349115689 2749526131459178511836767)
                      ·
                        rfl

theorem cell23_5354683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4, 2].length) (baseStart_5354683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354683 prefixEnd_5354683 := by exact prefixLift 5354683
  have htrace : WordTrace (prefixWord ++ tailWord_5354683) baseStart_5354683 baseEnd_5354683 := by
    simpa [prefixWord, tailWord_5354683, baseEnd_5354683] using wordTrace_append hprefix tailTrace_5354683
  have hstable : (prefixWord ++ tailWord_5354683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354683).length < 2 ^ (prefixWord ++ tailWord_5354683).sum := by decide
  have hdescent : baseEnd_5354683 < baseStart_5354683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354736 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_5354736 : Nat := 118140960795 + 5354736 * 2 ^ 59
def prefixEnd_5354736 : Nat := 4983230072969 + 3 ^ 40 * 5354736 * 2
def baseEnd_5354736 : Nat := 916517781977955601491341

theorem tailTrace_5354736 : CollatzResearch.WordTrace tailWord_5354736 prefixEnd_5354736 916517781977955601491341 := by
  unfold tailWord_5354736
  simp only [CollatzResearch.WordTrace]
  refine ⟨97651633364356731472782031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130202177819142308630376041 97651633364356731472782031)
  ·
    refine ⟨146477450046535097209173047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97651633364356731472782031 146477450046535097209173047)
    ·
      refine ⟨219716175069802645813759571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146477450046535097209173047 219716175069802645813759571)
      ·
        refine ⟨329574262604703968720639357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219716175069802645813759571 329574262604703968720639357)
        ·
          refine ⟨123590348476763988270239759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329574262604703968720639357 123590348476763988270239759)
          ·
            refine ⟨185385522715145982405359639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123590348476763988270239759 185385522715145982405359639)
            ·
              refine ⟨278078284072718973608039459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185385522715145982405359639 278078284072718973608039459)
              ·
                refine ⟨417117426109078460412059189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278078284072718973608039459 417117426109078460412059189)
                ·
                  refine ⟨39104758697726105663630549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 417117426109078460412059189 39104758697726105663630549)
                  ·
                    refine ⟨916517781977955601491341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39104758697726105663630549 916517781977955601491341)
                    ·
                      rfl

theorem cell23_5354736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_5354736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354736 prefixEnd_5354736 := by exact prefixLift 5354736
  have htrace : WordTrace (prefixWord ++ tailWord_5354736) baseStart_5354736 baseEnd_5354736 := by
    simpa [prefixWord, tailWord_5354736, baseEnd_5354736] using wordTrace_append hprefix tailTrace_5354736
  have hstable : (prefixWord ++ tailWord_5354736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354736).length < 2 ^ (prefixWord ++ tailWord_5354736).sum := by decide
  have hdescent : baseEnd_5354736 < baseStart_5354736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354750 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_5354750 : Nat := 118140960795 + 5354750 * 2 ^ 59
def prefixEnd_5354750 : Nat := 4983230072969 + 3 ^ 40 * 5354750 * 2
def baseEnd_5354750 : Nat := 2749560534663029749698959

theorem tailTrace_5354750 : CollatzResearch.WordTrace tailWord_5354750 prefixEnd_5354750 2749560534663029749698959 := by
  unfold tailWord_5354750
  simp only [CollatzResearch.WordTrace]
  refine ⟨24412972168832842917071713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130202518233775162224382469 24412972168832842917071713)
  ·
    refine ⟨18309729126624632187803785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24412972168832842917071713 18309729126624632187803785)
    ·
      refine ⟨13732296844968474140852839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18309729126624632187803785 13732296844968474140852839)
      ·
        refine ⟨20598445267452711211279259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13732296844968474140852839 20598445267452711211279259)
        ·
          refine ⟨30897667901179066816918889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20598445267452711211279259 30897667901179066816918889)
          ·
            refine ⟨23173250925884300112689167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30897667901179066816918889 23173250925884300112689167)
            ·
              refine ⟨34759876388826450169033751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23173250925884300112689167 34759876388826450169033751)
              ·
                refine ⟨52139814583239675253550627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34759876388826450169033751 52139814583239675253550627)
                ·
                  refine ⟨78209721874859512880325941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52139814583239675253550627 78209721874859512880325941)
                  ·
                    refine ⟨7332161425768079332530557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78209721874859512880325941 7332161425768079332530557)
                    ·
                      refine ⟨2749560534663029749698959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332161425768079332530557 2749560534663029749698959)
                      ·
                        rfl

theorem cell23_5354750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_5354750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354750 prefixEnd_5354750 := by exact prefixLift 5354750
  have htrace : WordTrace (prefixWord ++ tailWord_5354750) baseStart_5354750 baseEnd_5354750 := by
    simpa [prefixWord, tailWord_5354750, baseEnd_5354750] using wordTrace_append hprefix tailTrace_5354750
  have hstable : (prefixWord ++ tailWord_5354750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354750).length < 2 ^ (prefixWord ++ tailWord_5354750).sum := by decide
  have hdescent : baseEnd_5354750 < baseStart_5354750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354800 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_5354800 : Nat := 118140960795 + 5354800 * 2 ^ 59
def prefixEnd_5354800 : Nat := 4983230072969 + 3 ^ 40 * 5354800 * 2
def baseEnd_5354800 : Nat := 916528736231918184691243

theorem tailTrace_5354800 : CollatzResearch.WordTrace tailWord_5354800 prefixEnd_5354800 916528736231918184691243 := by
  unfold tailWord_5354800
  simp only [CollatzResearch.WordTrace]
  refine ⟨97652800500240800937946927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130203734000321067917262569 97652800500240800937946927)
  ·
    refine ⟨146479200750361201406920391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97652800500240800937946927 146479200750361201406920391)
    ·
      refine ⟨219718801125541802110380587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146479200750361201406920391 219718801125541802110380587)
      ·
        refine ⟨329578201688312703165570881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219718801125541802110380587 329578201688312703165570881)
        ·
          refine ⟨247183651266234527374178161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329578201688312703165570881 247183651266234527374178161)
          ·
            refine ⟨185387738449675895530633621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247183651266234527374178161 185387738449675895530633621)
            ·
              refine ⟨8690050239828557602998451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185387738449675895530633621 8690050239828557602998451)
              ·
                refine ⟨13035075359742836404497677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690050239828557602998451 13035075359742836404497677)
                ·
                  refine ⟨4888153259903563651686629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13035075359742836404497677 4888153259903563651686629)
                  ·
                    refine ⟨916528736231918184691243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4888153259903563651686629 916528736231918184691243)
                    ·
                      rfl

theorem cell23_5354800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_5354800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354800 prefixEnd_5354800 := by exact prefixLift 5354800
  have htrace : WordTrace (prefixWord ++ tailWord_5354800) baseStart_5354800 baseEnd_5354800 := by
    simpa [prefixWord, tailWord_5354800, baseEnd_5354800] using wordTrace_append hprefix tailTrace_5354800
  have hstable : (prefixWord ++ tailWord_5354800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354800).length < 2 ^ (prefixWord ++ tailWord_5354800).sum := by decide
  have hdescent : baseEnd_5354800 < baseStart_5354800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354817 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5354817 : Nat := 118140960795 + 5354817 * 2 ^ 59
def prefixEnd_5354817 : Nat := 4983230072969 + 3 ^ 40 * 5354817 * 2
def baseEnd_5354817 : Nat := 916531645955626995853717

theorem tailTrace_5354817 : CollatzResearch.WordTrace tailWord_5354817 prefixEnd_5354817 916531645955626995853717 := by
  unfold tailWord_5354817
  simp only [CollatzResearch.WordTrace]
  refine ⟨195306221041420013779262705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130204147360946675852841803 195306221041420013779262705)
  ·
    refine ⟨146479665781065010334447029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195306221041420013779262705 146479665781065010334447029)
    ·
      refine ⟨13732468666974844718854409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146479665781065010334447029 13732468666974844718854409)
      ·
        refine ⟨10299351500231133539140807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13732468666974844718854409 10299351500231133539140807)
        ·
          refine ⟨15449027250346700308711211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10299351500231133539140807 15449027250346700308711211)
          ·
            refine ⟨23173540875520050463066817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15449027250346700308711211 23173540875520050463066817)
            ·
              refine ⟨17380155656640037847300113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23173540875520050463066817 17380155656640037847300113)
              ·
                refine ⟨13035116742480028385475085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17380155656640037847300113 13035116742480028385475085)
                ·
                  refine ⟨4888168778430010644553157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13035116742480028385475085 4888168778430010644553157)
                  ·
                    refine ⟨916531645955626995853717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4888168778430010644553157 916531645955626995853717)
                    ·
                      rfl

theorem cell23_5354817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5354817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354817 prefixEnd_5354817 := by exact prefixLift 5354817
  have htrace : WordTrace (prefixWord ++ tailWord_5354817) baseStart_5354817 baseEnd_5354817 := by
    simpa [prefixWord, tailWord_5354817, baseEnd_5354817] using wordTrace_append hprefix tailTrace_5354817
  have hstable : (prefixWord ++ tailWord_5354817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354817).length < 2 ^ (prefixWord ++ tailWord_5354817).sum := by decide
  have hdescent : baseEnd_5354817 < baseStart_5354817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354880 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2]
def baseStart_5354880 : Nat := 118140960795 + 5354880 * 2 ^ 59
def prefixEnd_5354880 : Nat := 4983230072969 + 3 ^ 40 * 5354880 * 2
def baseEnd_5354880 : Nat := 2749627287148114241073361

theorem tailTrace_5354880 : CollatzResearch.WordTrace tailWord_5354880 prefixEnd_5354880 2749627287148114241073361 := by
  unfold tailWord_5354880
  simp only [CollatzResearch.WordTrace]
  refine ⟨97654259420095887769403047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130205679226794517025870729 97654259420095887769403047)
  ·
    refine ⟨146481389130143831654104571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97654259420095887769403047 146481389130143831654104571)
    ·
      refine ⟨219722083695215747481156857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146481389130143831654104571 219722083695215747481156857)
      ·
        refine ⟨164791562771411810610867643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219722083695215747481156857 164791562771411810610867643)
        ·
          refine ⟨247187344157117715916301465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164791562771411810610867643 247187344157117715916301465)
          ·
            refine ⟨185390508117838286937226099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247187344157117715916301465 185390508117838286937226099)
            ·
              refine ⟨278085762176757430405839149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185390508117838286937226099 278085762176757430405839149)
              ·
                refine ⟨104282160816284036402189681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278085762176757430405839149 104282160816284036402189681)
                ·
                  refine ⟨78211620612213027301642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104282160816284036402189681 78211620612213027301642261)
                  ·
                    refine ⟨3666169716197485654764481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78211620612213027301642261 3666169716197485654764481)
                    ·
                      refine ⟨2749627287148114241073361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666169716197485654764481 2749627287148114241073361)
                      ·
                        rfl

theorem cell23_5354880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_5354880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354880 prefixEnd_5354880 := by exact prefixLift 5354880
  have htrace : WordTrace (prefixWord ++ tailWord_5354880) baseStart_5354880 baseEnd_5354880 := by
    simpa [prefixWord, tailWord_5354880, baseEnd_5354880] using wordTrace_append hprefix tailTrace_5354880
  have hstable : (prefixWord ++ tailWord_5354880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354880).length < 2 ^ (prefixWord ++ tailWord_5354880).sum := by decide
  have hdescent : baseEnd_5354880 < baseStart_5354880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354884 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_5354884 : Nat := 118140960795 + 5354884 * 2 ^ 59
def prefixEnd_5354884 : Nat := 4983230072969 + 3 ^ 40 * 5354884 * 2
def baseEnd_5354884 : Nat := 2749629341070732225423343

theorem tailTrace_5354884 : CollatzResearch.WordTrace tailWord_5354884 prefixEnd_5354884 2749629341070732225423343 := by
  unfold tailWord_5354884
  simp only [CollatzResearch.WordTrace]
  refine ⟨97654332366088642110975853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130205776488118189481301137 97654332366088642110975853)
  ·
    refine ⟨36620374637283240791615945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97654332366088642110975853 36620374637283240791615945)
    ·
      refine ⟨27465280977962430593711959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36620374637283240791615945 27465280977962430593711959)
      ·
        refine ⟨41197921466943645890567939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27465280977962430593711959 41197921466943645890567939)
        ·
          refine ⟨61796882200415468835851909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41197921466943645890567939 61796882200415468835851909)
          ·
            refine ⟨11586915412577900406722233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61796882200415468835851909 11586915412577900406722233)
            ·
              refine ⟨8690186559433425305041675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11586915412577900406722233 8690186559433425305041675)
              ·
                refine ⟨13035279839150137957562513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690186559433425305041675 13035279839150137957562513)
                ·
                  refine ⟨9776459879362603468171885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13035279839150137957562513 9776459879362603468171885)
                  ·
                    refine ⟨3666172454760976300564457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9776459879362603468171885 3666172454760976300564457)
                    ·
                      refine ⟨2749629341070732225423343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666172454760976300564457 2749629341070732225423343)
                      ·
                        rfl

theorem cell23_5354884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_5354884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354884 prefixEnd_5354884 := by exact prefixLift 5354884
  have htrace : WordTrace (prefixWord ++ tailWord_5354884) baseStart_5354884 baseEnd_5354884 := by
    simpa [prefixWord, tailWord_5354884, baseEnd_5354884] using wordTrace_append hprefix tailTrace_5354884
  have hstable : (prefixWord ++ tailWord_5354884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354884).length < 2 ^ (prefixWord ++ tailWord_5354884).sum := by decide
  have hdescent : baseEnd_5354884 < baseStart_5354884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354897 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_5354897 : Nat := 118140960795 + 5354897 * 2 ^ 59
def prefixEnd_5354897 : Nat := 4983230072969 + 3 ^ 40 * 5354897 * 2
def baseEnd_5354897 : Nat := 2749636016319240674560783

theorem tailTrace_5354897 : CollatzResearch.WordTrace tailWord_5354897 prefixEnd_5354897 2749636016319240674560783 := by
  unfold tailWord_5354897
  simp only [CollatzResearch.WordTrace]
  refine ⟨195309138881130187442174945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130206092587420124961449963 195309138881130187442174945)
  ·
    refine ⟨146481854160847640581631209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195309138881130187442174945 146481854160847640581631209)
    ·
      refine ⟨109861390620635730436223407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146481854160847640581631209 109861390620635730436223407)
      ·
        refine ⟨164792085930953595654335111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109861390620635730436223407 164792085930953595654335111)
        ·
          refine ⟨247188128896430393481502667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164792085930953595654335111 247188128896430393481502667)
          ·
            refine ⟨370782193344645590222254001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247188128896430393481502667 370782193344645590222254001)
            ·
              refine ⟨278086645008484192666690501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370782193344645590222254001 278086645008484192666690501)
              ·
                refine ⟨52141245939090786125004469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278086645008484192666690501 52141245939090786125004469)
                ·
                  refine ⟨4888241806789761199219169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52141245939090786125004469 4888241806789761199219169)
                  ·
                    refine ⟨3666181355092320899414377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888241806789761199219169 3666181355092320899414377)
                    ·
                      refine ⟨2749636016319240674560783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666181355092320899414377 2749636016319240674560783)
                      ·
                        rfl

theorem cell23_5354897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_5354897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354897 prefixEnd_5354897 := by exact prefixLift 5354897
  have htrace : WordTrace (prefixWord ++ tailWord_5354897) baseStart_5354897 baseEnd_5354897 := by
    simpa [prefixWord, tailWord_5354897, baseEnd_5354897] using wordTrace_append hprefix tailTrace_5354897
  have hstable : (prefixWord ++ tailWord_5354897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354897).length < 2 ^ (prefixWord ++ tailWord_5354897).sum := by decide
  have hdescent : baseEnd_5354897 < baseStart_5354897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354908 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5354908 : Nat := 118140960795 + 5354908 * 2 ^ 59
def prefixEnd_5354908 : Nat := 4983230072969 + 3 ^ 40 * 5354908 * 2
def baseEnd_5354908 : Nat := 2749641664606440131523233

theorem tailTrace_5354908 : CollatzResearch.WordTrace tailWord_5354908 prefixEnd_5354908 2749641664606440131523233 := by
  unfold tailWord_5354908
  simp only [CollatzResearch.WordTrace]
  refine ⟨97654770042045168160412689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130206360056060224213883585 97654770042045168160412689)
  ·
    refine ⟨73241077531533876120309517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97654770042045168160412689 73241077531533876120309517)
    ·
      refine ⟨27465404074325203545116069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73241077531533876120309517 27465404074325203545116069)
      ·
        refine ⟨5149763263935975664709263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27465404074325203545116069 5149763263935975664709263)
        ·
          refine ⟨7724644895903963497063895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149763263935975664709263 7724644895903963497063895)
          ·
            refine ⟨11586967343855945245595843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724644895903963497063895 11586967343855945245595843)
            ·
              refine ⟨17380451015783917868393765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11586967343855945245595843 17380451015783917868393765)
              ·
                refine ⟨3258834565459484600323831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17380451015783917868393765 3258834565459484600323831)
                ·
                  refine ⟨4888251848189226900485747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258834565459484600323831 4888251848189226900485747)
                  ·
                    refine ⟨7332377772283840350728621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888251848189226900485747 7332377772283840350728621)
                    ·
                      refine ⟨2749641664606440131523233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332377772283840350728621 2749641664606440131523233)
                      ·
                        rfl

theorem cell23_5354908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5354908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354908 prefixEnd_5354908 := by exact prefixLift 5354908
  have htrace : WordTrace (prefixWord ++ tailWord_5354908) baseStart_5354908 baseEnd_5354908 := by
    simpa [prefixWord, tailWord_5354908, baseEnd_5354908] using wordTrace_append hprefix tailTrace_5354908
  have hstable : (prefixWord ++ tailWord_5354908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354908).length < 2 ^ (prefixWord ++ tailWord_5354908).sum := by decide
  have hdescent : baseEnd_5354908 < baseStart_5354908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354937 : List Nat := [1, 2, 1, 4, 4, 1, 3, 7]
def baseStart_5354937 : Nat := 118140960795 + 5354937 * 2 ^ 59
def prefixEnd_5354937 : Nat := 4983230072969 + 3 ^ 40 * 5354937 * 2
def baseEnd_5354937 : Nat := 101839131686867426594837

theorem tailTrace_5354937 : CollatzResearch.WordTrace tailWord_5354937 prefixEnd_5354937 101839131686867426594837 := by
  unfold tailWord_5354937
  simp only [CollatzResearch.WordTrace]
  refine ⟨195310597800985274273631065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130207065200656849515754043 195310597800985274273631065)
  ·
    refine ⟨146482948350738955705223299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195310597800985274273631065 146482948350738955705223299)
    ·
      refine ⟨219724422526108433557834949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146482948350738955705223299 219724422526108433557834949)
      ·
        refine ⟨41198329223645331292094053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219724422526108433557834949 41198329223645331292094053)
        ·
          refine ⟨7724686729433499617267635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41198329223645331292094053 7724686729433499617267635)
          ·
            refine ⟨11587030094150249425901453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724686729433499617267635 11587030094150249425901453)
            ·
              refine ⟨4345136285306343534713045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11587030094150249425901453 4345136285306343534713045)
              ·
                refine ⟨101839131686867426594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4345136285306343534713045 101839131686867426594837)
                ·
                  rfl

theorem cell23_5354937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 7].length) (baseStart_5354937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354937 prefixEnd_5354937 := by exact prefixLift 5354937
  have htrace : WordTrace (prefixWord ++ tailWord_5354937) baseStart_5354937 baseEnd_5354937 := by
    simpa [prefixWord, tailWord_5354937, baseEnd_5354937] using wordTrace_append hprefix tailTrace_5354937
  have hstable : (prefixWord ++ tailWord_5354937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354937).length < 2 ^ (prefixWord ++ tailWord_5354937).sum := by decide
  have hdescent : baseEnd_5354937 < baseStart_5354937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354948 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5354948 : Nat := 118140960795 + 5354948 * 2 ^ 59
def prefixEnd_5354948 : Nat := 4983230072969 + 3 ^ 40 * 5354948 * 2
def baseEnd_5354948 : Nat := 2749662203832619975023049

theorem tailTrace_5354948 : CollatzResearch.WordTrace tailWord_5354948 prefixEnd_5354948 2749662203832619975023049 := by
  unfold tailWord_5354948
  simp only [CollatzResearch.WordTrace]
  refine ⟨97655499501972711576140749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130207332669296948768187665 97655499501972711576140749)
  ·
    refine ⟨36620812313239766841052781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97655499501972711576140749 36620812313239766841052781)
    ·
      refine ⟨13732804617464912565394793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36620812313239766841052781 13732804617464912565394793)
      ·
        refine ⟨10299603463098684424046095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13732804617464912565394793 10299603463098684424046095)
        ·
          refine ⟨15449405194648026636069143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10299603463098684424046095 15449405194648026636069143)
          ·
            refine ⟨23174107791972039954103715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15449405194648026636069143 23174107791972039954103715)
            ·
              refine ⟨34761161687958059931155573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23174107791972039954103715 34761161687958059931155573)
              ·
                refine ⟨3258858908246068118545835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34761161687958059931155573 3258858908246068118545835)
                ·
                  refine ⟨4888288362369102177818753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258858908246068118545835 4888288362369102177818753)
                  ·
                    refine ⟨3666216271776826633364065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888288362369102177818753 3666216271776826633364065)
                    ·
                      refine ⟨2749662203832619975023049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666216271776826633364065 2749662203832619975023049)
                      ·
                        rfl

theorem cell23_5354948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5354948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354948 prefixEnd_5354948 := by exact prefixLift 5354948
  have htrace : WordTrace (prefixWord ++ tailWord_5354948) baseStart_5354948 baseEnd_5354948 := by
    simpa [prefixWord, tailWord_5354948, baseEnd_5354948] using wordTrace_append hprefix tailTrace_5354948
  have hstable : (prefixWord ++ tailWord_5354948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354948).length < 2 ^ (prefixWord ++ tailWord_5354948).sum := by decide
  have hdescent : baseEnd_5354948 < baseStart_5354948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354963 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 12]
def baseStart_5354963 : Nat := 118140960795 + 5354963 * 2 ^ 59
def prefixEnd_5354963 : Nat := 4983230072969 + 3 ^ 40 * 5354963 * 2
def baseEnd_5354963 : Nat := 916556635347479138778493

theorem tailTrace_5354963 : CollatzResearch.WordTrace tailWord_5354963 prefixEnd_5354963 916556635347479138778493 := by
  unfold tailWord_5354963
  simp only [CollatzResearch.WordTrace]
  refine ⟨195311546098891080714077543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130207697399260720476051695 195311546098891080714077543)
  ·
    refine ⟨292967319148336621071116315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195311546098891080714077543 292967319148336621071116315)
    ·
      refine ⟨439450978722504931606674473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292967319148336621071116315 439450978722504931606674473)
      ·
        refine ⟨329588234041878698705005855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439450978722504931606674473 329588234041878698705005855)
        ·
          refine ⟨494382351062818048057508783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329588234041878698705005855 494382351062818048057508783)
          ·
            refine ⟨741573526594227072086263175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494382351062818048057508783 741573526594227072086263175)
            ·
              refine ⟨1112360289891340608129394763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741573526594227072086263175 1112360289891340608129394763)
              ·
                refine ⟨1668540434837010912194092145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112360289891340608129394763 1668540434837010912194092145)
                ·
                  refine ⟨1251405326127758184145569109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668540434837010912194092145 1251405326127758184145569109)
                  ·
                    refine ⟨916556635347479138778493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1251405326127758184145569109 916556635347479138778493)
                    ·
                      rfl

theorem cell23_5354963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_5354963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354963 prefixEnd_5354963 := by exact prefixLift 5354963
  have htrace : WordTrace (prefixWord ++ tailWord_5354963) baseStart_5354963 baseEnd_5354963 := by
    simpa [prefixWord, tailWord_5354963, baseEnd_5354963] using wordTrace_append hprefix tailTrace_5354963
  have hstable : (prefixWord ++ tailWord_5354963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354963).length < 2 ^ (prefixWord ++ tailWord_5354963).sum := by decide
  have hdescent : baseEnd_5354963 < baseStart_5354963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5354987 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 1, 4, 2]
def baseStart_5354987 : Nat := 118140960795 + 5354987 * 2 ^ 59
def prefixEnd_5354987 : Nat := 4983230072969 + 3 ^ 40 * 5354987 * 2
def baseEnd_5354987 : Nat := 2749682229578145322435369

theorem tailTrace_5354987 : CollatzResearch.WordTrace tailWord_5354987 prefixEnd_5354987 2749682229578145322435369 := by
  unfold tailWord_5354987
  simp only [CollatzResearch.WordTrace]
  refine ⟨195312421450804132812951215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130208280967202755208634143 195312421450804132812951215)
  ·
    refine ⟨292968632176206199219426823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195312421450804132812951215 292968632176206199219426823)
    ·
      refine ⟨439452948264309298829140235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292968632176206199219426823 439452948264309298829140235)
      ·
        refine ⟨659179422396463948243710353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439452948264309298829140235 659179422396463948243710353)
        ·
          refine ⟨494384566797347961182782765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 659179422396463948243710353 494384566797347961182782765)
          ·
            refine ⟨185394212549005485443543537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494384566797347961182782765 185394212549005485443543537)
            ·
              refine ⟨139045659411754114082657653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185394212549005485443543537 139045659411754114082657653)
              ·
                refine ⟨13035530569851948195249155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139045659411754114082657653 13035530569851948195249155)
                ·
                  refine ⟨19553295854777922292873733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13035530569851948195249155 19553295854777922292873733)
                  ·
                    refine ⟨3666242972770860429913825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19553295854777922292873733 3666242972770860429913825)
                    ·
                      refine ⟨2749682229578145322435369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666242972770860429913825 2749682229578145322435369)
                      ·
                        rfl

theorem cell23_5354987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 4, 2].length) (baseStart_5354987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5354987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5354987 prefixEnd_5354987 := by exact prefixLift 5354987
  have htrace : WordTrace (prefixWord ++ tailWord_5354987) baseStart_5354987 baseEnd_5354987 := by
    simpa [prefixWord, tailWord_5354987, baseEnd_5354987] using wordTrace_append hprefix tailTrace_5354987
  have hstable : (prefixWord ++ tailWord_5354987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5354987).length < 2 ^ (prefixWord ++ tailWord_5354987).sum := by decide
  have hdescent : baseEnd_5354987 < baseStart_5354987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5354987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355004 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_5355004 : Nat := 118140960795 + 5355004 * 2 ^ 59
def prefixEnd_5355004 : Nat := 4983230072969 + 3 ^ 40 * 5355004 * 2
def baseEnd_5355004 : Nat := 2749690958749271755922791

theorem tailTrace_5355004 : CollatzResearch.WordTrace tailWord_5355004 prefixEnd_5355004 2749690958749271755922791 := by
  unfold tailWord_5355004
  simp only [CollatzResearch.WordTrace]
  refine ⟨97656520745871272358160033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130208694327828363144213377 97656520745871272358160033)
  ·
    refine ⟨73242390559403454268620025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97656520745871272358160033 73242390559403454268620025)
    ·
      refine ⟨54931792919552590701465019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73242390559403454268620025 54931792919552590701465019)
      ·
        refine ⟨82397689379328886052197529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54931792919552590701465019 82397689379328886052197529)
        ·
          refine ⟨61798267034496664539148147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82397689379328886052197529 61798267034496664539148147)
          ·
            refine ⟨92697400551744996808722221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61798267034496664539148147 92697400551744996808722221)
            ·
              refine ⟨34761525206904373803270833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92697400551744996808722221 34761525206904373803270833)
              ·
                refine ⟨26071143905178280352453125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34761525206904373803270833 26071143905178280352453125)
                ·
                  refine ⟨4888339482220927566084961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26071143905178280352453125 4888339482220927566084961)
                  ·
                    refine ⟨3666254611665695674563721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888339482220927566084961 3666254611665695674563721)
                    ·
                      refine ⟨2749690958749271755922791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666254611665695674563721 2749690958749271755922791)
                      ·
                        rfl

theorem cell23_5355004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_5355004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355004 prefixEnd_5355004 := by exact prefixLift 5355004
  have htrace : WordTrace (prefixWord ++ tailWord_5355004) baseStart_5355004 baseEnd_5355004 := by
    simpa [prefixWord, tailWord_5355004, baseEnd_5355004] using wordTrace_append hprefix tailTrace_5355004
  have hstable : (prefixWord ++ tailWord_5355004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355004).length < 2 ^ (prefixWord ++ tailWord_5355004).sum := by decide
  have hdescent : baseEnd_5355004 < baseStart_5355004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355027 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 7]
def baseStart_5355027 : Nat := 118140960795 + 5355027 * 2 ^ 59
def prefixEnd_5355027 : Nat := 4983230072969 + 3 ^ 40 * 5355027 * 2
def baseEnd_5355027 : Nat := 305522529867147240659465

theorem tailTrace_5355027 : CollatzResearch.WordTrace tailWord_5355027 prefixEnd_5355027 305522529867147240659465 := by
  unfold tailWord_5355027
  simp only [CollatzResearch.WordTrace]
  refine ⟨195313880370659219644407335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130209253580439479762938223 195313880370659219644407335)
  ·
    refine ⟨292970820555988829466611003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195313880370659219644407335 292970820555988829466611003)
    ·
      refine ⟨439456230833983244199916505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292970820555988829466611003 439456230833983244199916505)
      ·
        refine ⟨329592173125487433149937379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439456230833983244199916505 329592173125487433149937379)
        ·
          refine ⟨494388259688231149724906069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329592173125487433149937379 494388259688231149724906069)
          ·
            refine ⟨5793612418221458785838743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 494388259688231149724906069 5793612418221458785838743)
            ·
              refine ⟨8690418627332188178758115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793612418221458785838743 8690418627332188178758115)
              ·
                refine ⟨13035627940998282268137173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690418627332188178758115 13035627940998282268137173)
                ·
                  refine ⟨305522529867147240659465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13035627940998282268137173 305522529867147240659465)
                  ·
                    rfl

theorem cell23_5355027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 7].length) (baseStart_5355027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355027 prefixEnd_5355027 := by exact prefixLift 5355027
  have htrace : WordTrace (prefixWord ++ tailWord_5355027) baseStart_5355027 baseEnd_5355027 := by
    simpa [prefixWord, tailWord_5355027, baseEnd_5355027] using wordTrace_append hprefix tailTrace_5355027
  have hstable : (prefixWord ++ tailWord_5355027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355027).length < 2 ^ (prefixWord ++ tailWord_5355027).sum := by decide
  have hdescent : baseEnd_5355027 < baseStart_5355027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355037 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_5355037 : Nat := 118140960795 + 5355037 * 2 ^ 59
def prefixEnd_5355037 : Nat := 4983230072969 + 3 ^ 40 * 5355037 * 2
def baseEnd_5355037 : Nat := 2749707903610870126810139

theorem tailTrace_5355037 : CollatzResearch.WordTrace tailWord_5355037 prefixEnd_5355037 2749707903610870126810139 := by
  unfold tailWord_5355037
  simp only [CollatzResearch.WordTrace]
  refine ⟨195314245100622991352271365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130209496733748660901514243 195314245100622991352271365)
  ·
    refine ⟨36621420956366810878550881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195314245100622991352271365 36621420956366810878550881)
    ·
      refine ⟨27466065717275108158913161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36621420956366810878550881 27466065717275108158913161)
      ·
        refine ⟨20599549287956331119184871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466065717275108158913161 20599549287956331119184871)
        ·
          refine ⟨30899323931934496678777307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599549287956331119184871 30899323931934496678777307)
          ·
            refine ⟨46348985897901745018165961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30899323931934496678777307 46348985897901745018165961)
            ·
              refine ⟨34761739423426308763624471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46348985897901745018165961 34761739423426308763624471)
              ·
                refine ⟨52142609135139463145436707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34761739423426308763624471 52142609135139463145436707)
                ·
                  refine ⟨78213913702709194718155061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52142609135139463145436707 78213913702709194718155061)
                  ·
                    refine ⟨7332554409628987004827037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78213913702709194718155061 7332554409628987004827037)
                    ·
                      refine ⟨2749707903610870126810139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332554409628987004827037 2749707903610870126810139)
                      ·
                        rfl

theorem cell23_5355037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_5355037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355037 prefixEnd_5355037 := by exact prefixLift 5355037
  have htrace : WordTrace (prefixWord ++ tailWord_5355037) baseStart_5355037 baseEnd_5355037 := by
    simpa [prefixWord, tailWord_5355037, baseEnd_5355037] using wordTrace_append hprefix tailTrace_5355037
  have hstable : (prefixWord ++ tailWord_5355037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355037).length < 2 ^ (prefixWord ++ tailWord_5355037).sum := by decide
  have hdescent : baseEnd_5355037 < baseStart_5355037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355077 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_5355077 : Nat := 118140960795 + 5355077 * 2 ^ 59
def prefixEnd_5355077 : Nat := 4983230072969 + 3 ^ 40 * 5355077 * 2
def baseEnd_5355077 : Nat := 2749728442837049970309955

theorem tailTrace_5355077 : CollatzResearch.WordTrace tailWord_5355077 prefixEnd_5355077 2749728442837049970309955 := by
  unfold tailWord_5355077
  simp only [CollatzResearch.WordTrace]
  refine ⟨195315704020478078183727485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130210469346985385455818323 195315704020478078183727485)
  ·
    refine ⟨73243389007679279318897807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195315704020478078183727485 73243389007679279318897807)
    ·
      refine ⟨109865083511518918978346711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73243389007679279318897807 109865083511518918978346711)
      ·
        refine ⟨164797625267278378467520067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109865083511518918978346711 164797625267278378467520067)
        ·
          refine ⟨247196437900917567701280101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164797625267278378467520067 247196437900917567701280101)
          ·
            refine ⟨46349332106422043943990019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247196437900917567701280101 46349332106422043943990019)
            ·
              refine ⟨69523998159633065915985029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46349332106422043943990019 69523998159633065915985029)
              ·
                refine ⟨13035749654931199859247193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69523998159633065915985029 13035749654931199859247193)
                ·
                  refine ⟨9776812241198399894435395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13035749654931199859247193 9776812241198399894435395)
                  ·
                    refine ⟨14665218361797599841653093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9776812241198399894435395 14665218361797599841653093)
                    ·
                      refine ⟨2749728442837049970309955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14665218361797599841653093 2749728442837049970309955)
                      ·
                        rfl

theorem cell23_5355077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_5355077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355077 prefixEnd_5355077 := by exact prefixLift 5355077
  have htrace : WordTrace (prefixWord ++ tailWord_5355077) baseStart_5355077 baseEnd_5355077 := by
    simpa [prefixWord, tailWord_5355077, baseEnd_5355077] using wordTrace_append hprefix tailTrace_5355077
  have hstable : (prefixWord ++ tailWord_5355077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355077).length < 2 ^ (prefixWord ++ tailWord_5355077).sum := by decide
  have hdescent : baseEnd_5355077 < baseStart_5355077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355078 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_5355078 : Nat := 118140960795 + 5355078 * 2 ^ 59
def prefixEnd_5355078 : Nat := 4983230072969 + 3 ^ 40 * 5355078 * 2
def baseEnd_5355078 : Nat := 305525439590856051821939

theorem tailTrace_5355078 : CollatzResearch.WordTrace tailWord_5355078 prefixEnd_5355078 305525439590856051821939 := by
  unfold tailWord_5355078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103616890421076729828559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130210493662316303569675925 6103616890421076729828559)
  ·
    refine ⟨9155425335631615094742839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6103616890421076729828559 9155425335631615094742839)
    ·
      refine ⟨13733138003447422642114259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9155425335631615094742839 13733138003447422642114259)
      ·
        refine ⟨20599707005171133963171389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13733138003447422642114259 20599707005171133963171389)
        ·
          refine ⟨7724890126939175236189271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20599707005171133963171389 7724890126939175236189271)
          ·
            refine ⟨11587335190408762854283907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724890126939175236189271 11587335190408762854283907)
            ·
              refine ⟨17381002785613144281425861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11587335190408762854283907 17381002785613144281425861)
              ·
                refine ⟨3258938022302464552767349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17381002785613144281425861 3258938022302464552767349)
                ·
                  refine ⟨305525439590856051821939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3258938022302464552767349 305525439590856051821939)
                  ·
                    rfl

theorem cell23_5355078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_5355078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355078 prefixEnd_5355078 := by exact prefixLift 5355078
  have htrace : WordTrace (prefixWord ++ tailWord_5355078) baseStart_5355078 baseEnd_5355078 := by
    simpa [prefixWord, tailWord_5355078, baseEnd_5355078] using wordTrace_append hprefix tailTrace_5355078
  have hstable : (prefixWord ++ tailWord_5355078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355078).length < 2 ^ (prefixWord ++ tailWord_5355078).sum := by decide
  have hdescent : baseEnd_5355078 < baseStart_5355078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355087 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 3, 4]
def baseStart_5355087 : Nat := 118140960795 + 5355087 * 2 ^ 59
def prefixEnd_5355087 : Nat := 4983230072969 + 3 ^ 40 * 5355087 * 2
def baseEnd_5355087 : Nat := 916577859214531643728303

theorem tailTrace_5355087 : CollatzResearch.WordTrace tailWord_5355087 prefixEnd_5355087 916577859214531643728303 := by
  unfold tailWord_5355087
  simp only [CollatzResearch.WordTrace]
  refine ⟨195316068750441849891591515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130210712500294566594394343 195316068750441849891591515)
  ·
    refine ⟨292974103125662774837387273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195316068750441849891591515 292974103125662774837387273)
    ·
      refine ⟨219730577344247081128040455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292974103125662774837387273 219730577344247081128040455)
      ·
        refine ⟨329595866016370621692060683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219730577344247081128040455 329595866016370621692060683)
        ·
          refine ⟨494393799024555932538091025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329595866016370621692060683 494393799024555932538091025)
          ·
            refine ⟨370795349268416949403568269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494393799024555932538091025 370795349268416949403568269)
            ·
              refine ⟨139048255975656356026338101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370795349268416949403568269 139048255975656356026338101)
              ·
                refine ⟨13035773997717783377469197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139048255975656356026338101 13035773997717783377469197)
                ·
                  refine ⟨4888415249144168766550949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13035773997717783377469197 4888415249144168766550949)
                  ·
                    refine ⟨916577859214531643728303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4888415249144168766550949 916577859214531643728303)
                    ·
                      rfl

theorem cell23_5355087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_5355087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355087 prefixEnd_5355087 := by exact prefixLift 5355087
  have htrace : WordTrace (prefixWord ++ tailWord_5355087) baseStart_5355087 baseEnd_5355087 := by
    simpa [prefixWord, tailWord_5355087, baseEnd_5355087] using wordTrace_append hprefix tailTrace_5355087
  have hstable : (prefixWord ++ tailWord_5355087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355087).length < 2 ^ (prefixWord ++ tailWord_5355087).sum := by decide
  have hdescent : baseEnd_5355087 < baseStart_5355087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355097 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_5355097 : Nat := 118140960795 + 5355097 * 2 ^ 59
def prefixEnd_5355097 : Nat := 4983230072969 + 3 ^ 40 * 5355097 * 2
def baseEnd_5355097 : Nat := 2749738712450139892059863

theorem tailTrace_5355097 : CollatzResearch.WordTrace tailWord_5355097 prefixEnd_5355097 2749738712450139892059863 := by
  unfold tailWord_5355097
  simp only [CollatzResearch.WordTrace]
  refine ⟨195316433480405621599455545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130210955653603747732970363 195316433480405621599455545)
  ·
    refine ⟨146487325110304216199591659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195316433480405621599455545 146487325110304216199591659)
    ·
      refine ⟨219730987665456324299387489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146487325110304216199591659 219730987665456324299387489)
      ·
        refine ⟨164798240749092243224540617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219730987665456324299387489 164798240749092243224540617)
        ·
          refine ⟨123598680561819182418405463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164798240749092243224540617 123598680561819182418405463)
          ·
            refine ⟨185398020842728773627608195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123598680561819182418405463 185398020842728773627608195)
            ·
              refine ⟨278097031264093160441412293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185398020842728773627608195 278097031264093160441412293)
              ·
                refine ⟨52143193362017467582764805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278097031264093160441412293 52143193362017467582764805)
                ·
                  refine ⟨9776848755378275171768401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52143193362017467582764805 9776848755378275171768401)
                  ·
                    refine ⟨7332636566533706378826301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9776848755378275171768401 7332636566533706378826301)
                    ·
                      refine ⟨2749738712450139892059863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332636566533706378826301 2749738712450139892059863)
                      ·
                        rfl

theorem cell23_5355097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_5355097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355097 prefixEnd_5355097 := by exact prefixLift 5355097
  have htrace : WordTrace (prefixWord ++ tailWord_5355097) baseStart_5355097 baseEnd_5355097 := by
    simpa [prefixWord, tailWord_5355097, baseEnd_5355097] using wordTrace_append hprefix tailTrace_5355097
  have hstable : (prefixWord ++ tailWord_5355097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355097).length < 2 ^ (prefixWord ++ tailWord_5355097).sum := by decide
  have hdescent : baseEnd_5355097 < baseStart_5355097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355114 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_5355114 : Nat := 118140960795 + 5355114 * 2 ^ 59
def prefixEnd_5355114 : Nat := 4983230072969 + 3 ^ 40 * 5355114 * 2
def baseEnd_5355114 : Nat := 2749747441621266325547285

theorem tailTrace_5355114 : CollatzResearch.WordTrace tailWord_5355114 prefixEnd_5355114 2749747441621266325547285 := by
  unfold tailWord_5355114
  simp only [CollatzResearch.WordTrace]
  refine ⟨48829263380336008375706099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130211369014229355668549597 48829263380336008375706099)
  ·
    refine ⟨73243895070504012563559149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48829263380336008375706099 73243895070504012563559149)
    ·
      refine ⟨27466460651439004711334681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73243895070504012563559149 27466460651439004711334681)
      ·
        refine ⟨20599845488579253533501011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466460651439004711334681 20599845488579253533501011)
        ·
          refine ⟨30899768232868880300251517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599845488579253533501011 30899768232868880300251517)
          ·
            refine ⟨11587413087325830112594319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30899768232868880300251517 11587413087325830112594319)
            ·
              refine ⟨17381119630988745168891479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11587413087325830112594319 17381119630988745168891479)
              ·
                refine ⟨26071679446483117753337219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17381119630988745168891479 26071679446483117753337219)
                ·
                  refine ⟨39107519169724676630005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26071679446483117753337219 39107519169724676630005829)
                  ·
                    refine ⟨7332659844323376868126093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39107519169724676630005829 7332659844323376868126093)
                    ·
                      refine ⟨2749747441621266325547285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332659844323376868126093 2749747441621266325547285)
                      ·
                        rfl

theorem cell23_5355114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_5355114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355114 prefixEnd_5355114 := by exact prefixLift 5355114
  have htrace : WordTrace (prefixWord ++ tailWord_5355114) baseStart_5355114 baseEnd_5355114 := by
    simpa [prefixWord, tailWord_5355114, baseEnd_5355114] using wordTrace_append hprefix tailTrace_5355114
  have hstable : (prefixWord ++ tailWord_5355114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355114).length < 2 ^ (prefixWord ++ tailWord_5355114).sum := by decide
  have hdescent : baseEnd_5355114 < baseStart_5355114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355137 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5355137 : Nat := 118140960795 + 5355137 * 2 ^ 59
def prefixEnd_5355137 : Nat := 4983230072969 + 3 ^ 40 * 5355137 * 2
def baseEnd_5355137 : Nat := 2749759251676319735559679

theorem tailTrace_5355137 : CollatzResearch.WordTrace tailWord_5355137 prefixEnd_5355137 2749759251676319735559679 := by
  unfold tailWord_5355137
  simp only [CollatzResearch.WordTrace]
  refine ⟨195317892400260708430911665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130211928266840472287274443 195317892400260708430911665)
  ·
    refine ⟨146488419300195531323183749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195317892400260708430911665 146488419300195531323183749)
    ·
      refine ⟨27466578618786662123096953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146488419300195531323183749 27466578618786662123096953)
      ·
        refine ⟨20599933964089996592322715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466578618786662123096953 20599933964089996592322715)
        ·
          refine ⟨30899900946134994888484073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599933964089996592322715 30899900946134994888484073)
          ·
            refine ⟨23174925709601246166363055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30899900946134994888484073 23174925709601246166363055)
            ·
              refine ⟨34762388564401869249544583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23174925709601246166363055 34762388564401869249544583)
              ·
                refine ⟨52143582846602803874316875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34762388564401869249544583 52143582846602803874316875)
                ·
                  refine ⟨78215374269904205811475313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52143582846602803874316875 78215374269904205811475313)
                  ·
                    refine ⟨58661530702428154358606485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78215374269904205811475313 58661530702428154358606485)
                    ·
                      refine ⟨2749759251676319735559679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58661530702428154358606485 2749759251676319735559679)
                      ·
                        rfl

theorem cell23_5355137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5355137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355137 prefixEnd_5355137 := by exact prefixLift 5355137
  have htrace : WordTrace (prefixWord ++ tailWord_5355137) baseStart_5355137 baseEnd_5355137 := by
    simpa [prefixWord, tailWord_5355137, baseEnd_5355137] using wordTrace_append hprefix tailTrace_5355137
  have hstable : (prefixWord ++ tailWord_5355137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355137).length < 2 ^ (prefixWord ++ tailWord_5355137).sum := by decide
  have hdescent : baseEnd_5355137 < baseStart_5355137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355184 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_5355184 : Nat := 118140960795 + 5355184 * 2 ^ 59
def prefixEnd_5355184 : Nat := 4983230072969 + 3 ^ 40 * 5355184 * 2
def baseEnd_5355184 : Nat := 2749783385267081051671963

theorem tailTrace_5355184 : CollatzResearch.WordTrace tailWord_5355184 prefixEnd_5355184 2749783385267081051671963 := by
  unfold tailWord_5355184
  simp only [CollatzResearch.WordTrace]
  refine ⟨97659803315545217728936303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130213071087393623638581737 97659803315545217728936303)
  ·
    refine ⟨146489704973317826593404455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97659803315545217728936303 146489704973317826593404455)
    ·
      refine ⟨219734557459976739890106683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146489704973317826593404455 219734557459976739890106683)
      ·
        refine ⟨329601836189965109835160025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219734557459976739890106683 329601836189965109835160025)
        ·
          refine ⟨247201377142473832376370019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329601836189965109835160025 247201377142473832376370019)
          ·
            refine ⟨370802065713710748564555029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247201377142473832376370019 370802065713710748564555029)
            ·
              refine ⟨17381346830330191338963517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 370802065713710748564555029 17381346830330191338963517)
              ·
                refine ⟨6518005061373821752111319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17381346830330191338963517 6518005061373821752111319)
                ·
                  refine ⟨9777007592060732628166979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518005061373821752111319 9777007592060732628166979)
                  ·
                    refine ⟨14665511388091098942250469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9777007592060732628166979 14665511388091098942250469)
                    ·
                      refine ⟨2749783385267081051671963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14665511388091098942250469 2749783385267081051671963)
                      ·
                        rfl

theorem cell23_5355184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_5355184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355184 prefixEnd_5355184 := by exact prefixLift 5355184
  have htrace : WordTrace (prefixWord ++ tailWord_5355184) baseStart_5355184 baseEnd_5355184 := by
    simpa [prefixWord, tailWord_5355184, baseEnd_5355184] using wordTrace_append hprefix tailTrace_5355184
  have hstable : (prefixWord ++ tailWord_5355184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355184).length < 2 ^ (prefixWord ++ tailWord_5355184).sum := by decide
  have hdescent : baseEnd_5355184 < baseStart_5355184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355194 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_5355194 : Nat := 118140960795 + 5355194 * 2 ^ 59
def prefixEnd_5355194 : Nat := 4983230072969 + 3 ^ 40 * 5355194 * 2
def baseEnd_5355194 : Nat := 916596173357875337515639

theorem tailTrace_5355194 : CollatzResearch.WordTrace tailWord_5355194 prefixEnd_5355194 916596173357875337515639 := by
  unfold tailWord_5355194
  simp only [CollatzResearch.WordTrace]
  refine ⟨48829992840263551791434159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130213314240702804777157757 48829992840263551791434159)
  ·
    refine ⟨73244989260395327687151239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48829992840263551791434159 73244989260395327687151239)
    ·
      refine ⟨109867483890592991530726859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73244989260395327687151239 109867483890592991530726859)
      ·
        refine ⟨164801225835889487296090289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109867483890592991530726859 164801225835889487296090289)
        ·
          refine ⟨123600919376917115472067717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164801225835889487296090289 123600919376917115472067717)
          ·
            refine ⟨23175172383171959151012697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123600919376917115472067717 23175172383171959151012697)
            ·
              refine ⟨17381379287378969363259523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23175172383171959151012697 17381379287378969363259523)
              ·
                refine ⟨26072068931068454044889285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17381379287378969363259523 26072068931068454044889285)
                ·
                  refine ⟨4888512924575335133416741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26072068931068454044889285 4888512924575335133416741)
                  ·
                    refine ⟨916596173357875337515639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4888512924575335133416741 916596173357875337515639)
                    ·
                      rfl

theorem cell23_5355194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_5355194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355194 prefixEnd_5355194 := by exact prefixLift 5355194
  have htrace : WordTrace (prefixWord ++ tailWord_5355194) baseStart_5355194 baseEnd_5355194 := by
    simpa [prefixWord, tailWord_5355194, baseEnd_5355194] using wordTrace_append hprefix tailTrace_5355194
  have hstable : (prefixWord ++ tailWord_5355194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355194).length < 2 ^ (prefixWord ++ tailWord_5355194).sum := by decide
  have hdescent : baseEnd_5355194 < baseStart_5355194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355197 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5355197 : Nat := 118140960795 + 5355197 * 2 ^ 59
def prefixEnd_5355197 : Nat := 4983230072969 + 3 ^ 40 * 5355197 * 2
def baseEnd_5355197 : Nat := 2749790060515589500809403

theorem tailTrace_5355197 : CollatzResearch.WordTrace tailWord_5355197 prefixEnd_5355197 2749790060515589500809403 := by
  unfold tailWord_5355197
  simp only [CollatzResearch.WordTrace]
  refine ⟨195320080780043338678095845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130213387186695559118730563 195320080780043338678095845)
  ·
    refine ⟨36622515146258126002142971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195320080780043338678095845 36622515146258126002142971)
    ·
      refine ⟨54933772719387189003214457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36622515146258126002142971 54933772719387189003214457)
      ·
        refine ⟨41200329539540391752410843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54933772719387189003214457 41200329539540391752410843)
        ·
          refine ⟨61800494309310587628616265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41200329539540391752410843 61800494309310587628616265)
          ·
            refine ⟨46350370731982940721462199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61800494309310587628616265 46350370731982940721462199)
            ·
              refine ⟨69525556097974411082193299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46350370731982940721462199 69525556097974411082193299)
              ·
                refine ⟨104288334146961616623289949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69525556097974411082193299 104288334146961616623289949)
                ·
                  refine ⟨39108125305110606233733731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104288334146961616623289949 39108125305110606233733731)
                  ·
                    refine ⟨58662187957665909350600597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39108125305110606233733731 58662187957665909350600597)
                    ·
                      refine ⟨2749790060515589500809403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58662187957665909350600597 2749790060515589500809403)
                      ·
                        rfl

theorem cell23_5355197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5355197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355197 prefixEnd_5355197 := by exact prefixLift 5355197
  have htrace : WordTrace (prefixWord ++ tailWord_5355197) baseStart_5355197 baseEnd_5355197 := by
    simpa [prefixWord, tailWord_5355197, baseEnd_5355197] using wordTrace_append hprefix tailTrace_5355197
  have hstable : (prefixWord ++ tailWord_5355197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355197).length < 2 ^ (prefixWord ++ tailWord_5355197).sum := by decide
  have hdescent : baseEnd_5355197 < baseStart_5355197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355202 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_5355202 : Nat := 118140960795 + 5355202 * 2 ^ 59
def prefixEnd_5355202 : Nat := 4983230072969 + 3 ^ 40 * 5355202 * 2
def baseEnd_5355202 : Nat := 305532514213206886805209

theorem tailTrace_5355202 : CollatzResearch.WordTrace tailWord_5355202 prefixEnd_5355202 305532514213206886805209 := by
  unfold tailWord_5355202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48830065786256306133006965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130213508763350149688018573 48830065786256306133006965)
  ·
    refine ⟨4577818667461528699969403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48830065786256306133006965 4577818667461528699969403)
    ·
      refine ⟨6866728001192293049954105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577818667461528699969403 6866728001192293049954105)
      ·
        refine ⟨5150046000894219787465579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6866728001192293049954105 5150046000894219787465579)
        ·
          refine ⟨7725069001341329681198369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150046000894219787465579 7725069001341329681198369)
          ·
            refine ⟨5793801751005997260898777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7725069001341329681198369 5793801751005997260898777)
            ·
              refine ⟨4345351313254497945674083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5793801751005997260898777 4345351313254497945674083)
              ·
                refine ⟨6518026969881746918511125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345351313254497945674083 6518026969881746918511125)
                ·
                  refine ⟨305532514213206886805209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6518026969881746918511125 305532514213206886805209)
                  ·
                    rfl

theorem cell23_5355202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_5355202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355202 prefixEnd_5355202 := by exact prefixLift 5355202
  have htrace : WordTrace (prefixWord ++ tailWord_5355202) baseStart_5355202 baseEnd_5355202 := by
    simpa [prefixWord, tailWord_5355202, baseEnd_5355202] using wordTrace_append hprefix tailTrace_5355202
  have hstable : (prefixWord ++ tailWord_5355202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355202).length < 2 ^ (prefixWord ++ tailWord_5355202).sum := by decide
  have hdescent : baseEnd_5355202 < baseStart_5355202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355204 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5355204 : Nat := 118140960795 + 5355204 * 2 ^ 59
def prefixEnd_5355204 : Nat := 4983230072969 + 3 ^ 40 * 5355204 * 2
def baseEnd_5355204 : Nat := 2749793654880170973421871

theorem tailTrace_5355204 : CollatzResearch.WordTrace tailWord_5355204 prefixEnd_5355204 2749793654880170973421871 := by
  unfold tailWord_5355204
  simp only [CollatzResearch.WordTrace]
  refine ⟨97660168045508989436800333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130213557394011985915733777 97660168045508989436800333)
  ·
    refine ⟨36622563017065871038800125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97660168045508989436800333 36622563017065871038800125)
    ·
      refine ⟨13733461131399701639550047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36622563017065871038800125 13733461131399701639550047)
      ·
        refine ⟨20600191697099552459325071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13733461131399701639550047 20600191697099552459325071)
        ·
          refine ⟨30900287545649328688987607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20600191697099552459325071 30900287545649328688987607)
          ·
            refine ⟨46350431318473993033481411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30900287545649328688987607 46350431318473993033481411)
            ·
              refine ⟨69525646977710989550222117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46350431318473993033481411 69525646977710989550222117)
              ·
                refine ⟨13036058808320810540666647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69525646977710989550222117 13036058808320810540666647)
                ·
                  refine ⟨19554088212481215810999971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13036058808320810540666647 19554088212481215810999971)
                  ·
                    refine ⟨29331132318721823716499957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19554088212481215810999971 29331132318721823716499957)
                    ·
                      refine ⟨2749793654880170973421871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29331132318721823716499957 2749793654880170973421871)
                      ·
                        rfl

theorem cell23_5355204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5355204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355204 prefixEnd_5355204 := by exact prefixLift 5355204
  have htrace : WordTrace (prefixWord ++ tailWord_5355204) baseStart_5355204 baseEnd_5355204 := by
    simpa [prefixWord, tailWord_5355204, baseEnd_5355204] using wordTrace_append hprefix tailTrace_5355204
  have hstable : (prefixWord ++ tailWord_5355204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355204).length < 2 ^ (prefixWord ++ tailWord_5355204).sum := by decide
  have hdescent : baseEnd_5355204 < baseStart_5355204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355207 : List Nat := [1, 1, 4, 1, 1, 1, 6, 8]
def baseStart_5355207 : Nat := 118140960795 + 5355207 * 2 ^ 59
def prefixEnd_5355207 : Nat := 4983230072969 + 3 ^ 40 * 5355207 * 2
def baseEnd_5355207 : Nat := 101844266493412387469791

theorem tailTrace_5355207 : CollatzResearch.WordTrace tailWord_5355207 prefixEnd_5355207 101844266493412387469791 := by
  unfold tailWord_5355207
  simp only [CollatzResearch.WordTrace]
  refine ⟨195320445510007110385959875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130213630340004740257306583 195320445510007110385959875)
  ·
    refine ⟨292980668265010665578939813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195320445510007110385959875 292980668265010665578939813)
    ·
      refine ⟨54933875299689499796051215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292980668265010665578939813 54933875299689499796051215)
      ·
        refine ⟨82400812949534249694076823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54933875299689499796051215 82400812949534249694076823)
        ·
          refine ⟨123601219424301374541115235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82400812949534249694076823 123601219424301374541115235)
          ·
            refine ⟨185401829136452061811672853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123601219424301374541115235 185401829136452061811672853)
            ·
              refine ⟨8690710740771190397422165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185401829136452061811672853 8690710740771190397422165)
              ·
                refine ⟨101844266493412387469791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8690710740771190397422165 101844266493412387469791)
                ·
                  rfl

theorem cell23_5355207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 8].length) (baseStart_5355207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355207 prefixEnd_5355207 := by exact prefixLift 5355207
  have htrace : WordTrace (prefixWord ++ tailWord_5355207) baseStart_5355207 baseEnd_5355207 := by
    simpa [prefixWord, tailWord_5355207, baseEnd_5355207] using wordTrace_append hprefix tailTrace_5355207
  have hstable : (prefixWord ++ tailWord_5355207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355207).length < 2 ^ (prefixWord ++ tailWord_5355207).sum := by decide
  have hdescent : baseEnd_5355207 < baseStart_5355207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355214 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_5355214 : Nat := 118140960795 + 5355214 * 2 ^ 59
def prefixEnd_5355214 : Nat := 4983230072969 + 3 ^ 40 * 5355214 * 2
def baseEnd_5355214 : Nat := 2749798789686715934296825

theorem tailTrace_5355214 : CollatzResearch.WordTrace tailWord_5355214 prefixEnd_5355214 2749798789686715934296825 := by
  unfold tailWord_5355214
  simp only [CollatzResearch.WordTrace]
  refine ⟨24415087602622718822683087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130213800547321167054309797 24415087602622718822683087)
  ·
    refine ⟨36622631403934078234024631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24415087602622718822683087 36622631403934078234024631)
    ·
      refine ⟨54933947105901117351036947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36622631403934078234024631 54933947105901117351036947)
      ·
        refine ⟨82400920658851676026555421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54933947105901117351036947 82400920658851676026555421)
        ·
          refine ⟨30900345247069378509958283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82400920658851676026555421 30900345247069378509958283)
          ·
            refine ⟨46350517870604067764937425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30900345247069378509958283 46350517870604067764937425)
            ·
              refine ⟨34762888402953050823703069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46350517870604067764937425 34762888402953050823703069)
              ·
                refine ⟨13036083151107394058888651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34762888402953050823703069 13036083151107394058888651)
                ·
                  refine ⟨19554124726661091088332977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13036083151107394058888651 19554124726661091088332977)
                  ·
                    refine ⟨14665593544995818316249733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19554124726661091088332977 14665593544995818316249733)
                    ·
                      refine ⟨2749798789686715934296825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14665593544995818316249733 2749798789686715934296825)
                      ·
                        rfl

theorem cell23_5355214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_5355214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355214 prefixEnd_5355214 := by exact prefixLift 5355214
  have htrace : WordTrace (prefixWord ++ tailWord_5355214) baseStart_5355214 baseEnd_5355214 := by
    simpa [prefixWord, tailWord_5355214, baseEnd_5355214] using wordTrace_append hprefix tailTrace_5355214
  have hstable : (prefixWord ++ tailWord_5355214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355214).length < 2 ^ (prefixWord ++ tailWord_5355214).sum := by decide
  have hdescent : baseEnd_5355214 < baseStart_5355214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355218 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5355218 : Nat := 118140960795 + 5355218 * 2 ^ 59
def prefixEnd_5355218 : Nat := 4983230072969 + 3 ^ 40 * 5355218 * 2
def baseEnd_5355218 : Nat := 2749800843609333918646807

theorem tailTrace_5355218 : CollatzResearch.WordTrace tailWord_5355218 prefixEnd_5355218 2749800843609333918646807 := by
  unfold tailWord_5355218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48830211678241814816152577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130213897808644839509740205 48830211678241814816152577)
  ·
    refine ⟨36622658758681361112114433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48830211678241814816152577 36622658758681361112114433)
    ·
      refine ⟨27466994069011020834085825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36622658758681361112114433 27466994069011020834085825)
      ·
        refine ⟨20600245551758265625564369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466994069011020834085825 20600245551758265625564369)
        ·
          refine ⟨15450184163818699219173277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20600245551758265625564369 15450184163818699219173277)
          ·
            refine ⟨5793819061432012207189979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15450184163818699219173277 5793819061432012207189979)
            ·
              refine ⟨8690728592148018310784969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793819061432012207189979 8690728592148018310784969)
              ·
                refine ⟨6518046444111013733088727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8690728592148018310784969 6518046444111013733088727)
                ·
                  refine ⟨9777069666166520599633091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518046444111013733088727 9777069666166520599633091)
                  ·
                    refine ⟨14665604499249780899449637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9777069666166520599633091 14665604499249780899449637)
                    ·
                      refine ⟨2749800843609333918646807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14665604499249780899449637 2749800843609333918646807)
                      ·
                        rfl

theorem cell23_5355218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5355218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355218 prefixEnd_5355218 := by exact prefixLift 5355218
  have htrace : WordTrace (prefixWord ++ tailWord_5355218) baseStart_5355218 baseEnd_5355218 := by
    simpa [prefixWord, tailWord_5355218, baseEnd_5355218] using wordTrace_append hprefix tailTrace_5355218
  have hstable : (prefixWord ++ tailWord_5355218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355218).length < 2 ^ (prefixWord ++ tailWord_5355218).sum := by decide
  have hdescent : baseEnd_5355218 < baseStart_5355218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355222 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5355222 : Nat := 118140960795 + 5355222 * 2 ^ 59
def prefixEnd_5355222 : Nat := 4983230072969 + 3 ^ 40 * 5355222 * 2
def baseEnd_5355222 : Nat := 2749802897531951902996789

theorem tailTrace_5355222 : CollatzResearch.WordTrace tailWord_5355222 prefixEnd_5355222 2749802897531951902996789 := by
  unfold tailWord_5355222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207562037809547996734745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130213995069968511965170613 12207562037809547996734745)
  ·
    refine ⟨9155671528357160997551059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12207562037809547996734745 9155671528357160997551059)
    ·
      refine ⟨13733507292535741496326589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9155671528357160997551059 13733507292535741496326589)
      ·
        refine ⟨5150065234700903061122471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13733507292535741496326589 5150065234700903061122471)
        ·
          refine ⟨7725097852051354591683707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150065234700903061122471 7725097852051354591683707)
          ·
            refine ⟨11587646778077031887525561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725097852051354591683707 11587646778077031887525561)
            ·
              refine ⟨8690735083557773915644171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11587646778077031887525561 8690735083557773915644171)
              ·
                refine ⟨13036102625336660873466257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690735083557773915644171 13036102625336660873466257)
                ·
                  refine ⟨9777076969002495655099693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13036102625336660873466257 9777076969002495655099693)
                  ·
                    refine ⟨3666403863375935870662385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9777076969002495655099693 3666403863375935870662385)
                    ·
                      refine ⟨2749802897531951902996789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666403863375935870662385 2749802897531951902996789)
                      ·
                        rfl

theorem cell23_5355222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5355222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355222 prefixEnd_5355222 := by exact prefixLift 5355222
  have htrace : WordTrace (prefixWord ++ tailWord_5355222) baseStart_5355222 baseEnd_5355222 := by
    simpa [prefixWord, tailWord_5355222, baseEnd_5355222] using wordTrace_append hprefix tailTrace_5355222
  have hstable : (prefixWord ++ tailWord_5355222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355222).length < 2 ^ (prefixWord ++ tailWord_5355222).sum := by decide
  have hdescent : baseEnd_5355222 < baseStart_5355222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355251 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 3]
def baseStart_5355251 : Nat := 118140960795 + 5355251 * 2 ^ 59
def prefixEnd_5355251 : Nat := 4983230072969 + 3 ^ 40 * 5355251 * 2
def baseEnd_5355251 : Nat := 2749817788470932289534155

theorem tailTrace_5355251 : CollatzResearch.WordTrace tailWord_5355251 prefixEnd_5355251 2749817788470932289534155 := by
  unfold tailWord_5355251
  simp only [CollatzResearch.WordTrace]
  refine ⟨195322050321847705900561607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130214700214565137267041071 195322050321847705900561607)
  ·
    refine ⟨292983075482771558850842411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195322050321847705900561607 292983075482771558850842411)
    ·
      refine ⟨439474613224157338276263617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292983075482771558850842411 439474613224157338276263617)
      ·
        refine ⟨329605959918118003707197713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439474613224157338276263617 329605959918118003707197713)
        ·
          refine ⟨247204469938588502780398285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329605959918118003707197713 247204469938588502780398285)
          ·
            refine ⟨92701676226970688542649357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247204469938588502780398285 92701676226970688542649357)
            ·
              refine ⟨34763128585114008203493509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92701676226970688542649357 34763128585114008203493509)
              ·
                refine ⟨6518086609708876538155033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34763128585114008203493509 6518086609708876538155033)
                ·
                  refine ⟨4888564957281657403616275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518086609708876538155033 4888564957281657403616275)
                  ·
                    refine ⟨7332847435922486105424413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888564957281657403616275 7332847435922486105424413)
                    ·
                      refine ⟨2749817788470932289534155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332847435922486105424413 2749817788470932289534155)
                      ·
                        rfl

theorem cell23_5355251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_5355251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355251 prefixEnd_5355251 := by exact prefixLift 5355251
  have htrace : WordTrace (prefixWord ++ tailWord_5355251) baseStart_5355251 baseEnd_5355251 := by
    simpa [prefixWord, tailWord_5355251, baseEnd_5355251] using wordTrace_append hprefix tailTrace_5355251
  have hstable : (prefixWord ++ tailWord_5355251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355251).length < 2 ^ (prefixWord ++ tailWord_5355251).sum := by decide
  have hdescent : baseEnd_5355251 < baseStart_5355251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355254 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5355254 : Nat := 118140960795 + 5355254 * 2 ^ 59
def prefixEnd_5355254 : Nat := 4983230072969 + 3 ^ 40 * 5355254 * 2
def baseEnd_5355254 : Nat := 916606442970965259265547

theorem tailTrace_5355254 : CollatzResearch.WordTrace tailWord_5355254 prefixEnd_5355254 916606442970965259265547 := by
  unfold tailWord_5355254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207634983802302338307551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130214773160557891608613877 12207634983802302338307551)
  ·
    refine ⟨18311452475703453507461327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12207634983802302338307551 18311452475703453507461327)
    ·
      refine ⟨27467178713555180261191991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18311452475703453507461327 27467178713555180261191991)
      ·
        refine ⟨41200768070332770391787987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27467178713555180261191991 41200768070332770391787987)
        ·
          refine ⟨61801152105499155587681981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41200768070332770391787987 61801152105499155587681981)
          ·
            refine ⟨23175432039562183345380743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61801152105499155587681981 23175432039562183345380743)
            ·
              refine ⟨34763148059343275018071115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23175432039562183345380743 34763148059343275018071115)
              ·
                refine ⟨52144722089014912527106673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34763148059343275018071115 52144722089014912527106673)
                ·
                  refine ⟨39108541566761184395330005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52144722089014912527106673 39108541566761184395330005)
                  ·
                    refine ⟨916606442970965259265547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39108541566761184395330005 916606442970965259265547)
                    ·
                      rfl

theorem cell23_5355254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5355254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355254 prefixEnd_5355254 := by exact prefixLift 5355254
  have htrace : WordTrace (prefixWord ++ tailWord_5355254) baseStart_5355254 baseEnd_5355254 := by
    simpa [prefixWord, tailWord_5355254, baseEnd_5355254] using wordTrace_append hprefix tailTrace_5355254
  have hstable : (prefixWord ++ tailWord_5355254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355254).length < 2 ^ (prefixWord ++ tailWord_5355254).sum := by decide
  have hdescent : baseEnd_5355254 < baseStart_5355254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355267 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 8]
def baseStart_5355267 : Nat := 118140960795 + 5355267 * 2 ^ 59
def prefixEnd_5355267 : Nat := 4983230072969 + 3 ^ 40 * 5355267 * 2
def baseEnd_5355267 : Nat := 916608668053801408978027

theorem tailTrace_5355267 : CollatzResearch.WordTrace tailWord_5355267 prefixEnd_5355267 916608668053801408978027 := by
  unfold tailWord_5355267
  simp only [CollatzResearch.WordTrace]
  refine ⟨195322633889789740633144055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130215089259859827088762703 195322633889789740633144055)
  ·
    refine ⟨292983950834684610949716083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195322633889789740633144055 292983950834684610949716083)
    ·
      refine ⟨439475926252026916424574125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292983950834684610949716083 439475926252026916424574125)
      ·
        refine ⟨164803472344510093659215297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439475926252026916424574125 164803472344510093659215297)
        ·
          refine ⟨123602604258382570244411473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164803472344510093659215297 123602604258382570244411473)
          ·
            refine ⟨92701953193786927683308605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123602604258382570244411473 92701953193786927683308605)
            ·
              refine ⟨34763232447670097881240727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92701953193786927683308605 34763232447670097881240727)
              ·
                refine ⟨52144848671505146821861091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34763232447670097881240727 52144848671505146821861091)
                ·
                  refine ⟨78217273007257720232791637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52144848671505146821861091 78217273007257720232791637)
                  ·
                    refine ⟨916608668053801408978027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78217273007257720232791637 916608668053801408978027)
                    ·
                      rfl

theorem cell23_5355267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_5355267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355267 prefixEnd_5355267 := by exact prefixLift 5355267
  have htrace : WordTrace (prefixWord ++ tailWord_5355267) baseStart_5355267 baseEnd_5355267 := by
    simpa [prefixWord, tailWord_5355267, baseEnd_5355267] using wordTrace_append hprefix tailTrace_5355267
  have hstable : (prefixWord ++ tailWord_5355267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355267).length < 2 ^ (prefixWord ++ tailWord_5355267).sum := by decide
  have hdescent : baseEnd_5355267 < baseStart_5355267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355268 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_5355268 : Nat := 118140960795 + 5355268 * 2 ^ 59
def prefixEnd_5355268 : Nat := 4983230072969 + 3 ^ 40 * 5355268 * 2
def baseEnd_5355268 : Nat := 2749826517642058723021577

theorem tailTrace_5355268 : CollatzResearch.WordTrace tailWord_5355268 prefixEnd_5355268 2749826517642058723021577 := by
  unfold tailWord_5355268
  simp only [CollatzResearch.WordTrace]
  refine ⟨97661335181393058901965229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130215113575190745202620305 97661335181393058901965229)
  ·
    refine ⟨36623000693022397088236961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97661335181393058901965229 36623000693022397088236961)
    ·
      refine ⟨27467250519766797816177721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36623000693022397088236961 27467250519766797816177721)
      ·
        refine ⟨20600437889825098362133291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27467250519766797816177721 20600437889825098362133291)
        ·
          refine ⟨30900656834737647543199937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20600437889825098362133291 30900656834737647543199937)
          ·
            refine ⟨23175492626053235657399953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30900656834737647543199937 23175492626053235657399953)
            ·
              refine ⟨17381619469539926743049965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23175492626053235657399953 17381619469539926743049965)
              ·
                refine ⟨6518107301077472528643737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17381619469539926743049965 6518107301077472528643737)
                ·
                  refine ⟨4888580475808104396482803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518107301077472528643737 4888580475808104396482803)
                  ·
                    refine ⟨7332870713712156594724205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888580475808104396482803 7332870713712156594724205)
                    ·
                      refine ⟨2749826517642058723021577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7332870713712156594724205 2749826517642058723021577)
                      ·
                        rfl

theorem cell23_5355268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_5355268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355268 prefixEnd_5355268 := by exact prefixLift 5355268
  have htrace : WordTrace (prefixWord ++ tailWord_5355268) baseStart_5355268 baseEnd_5355268 := by
    simpa [prefixWord, tailWord_5355268, baseEnd_5355268] using wordTrace_append hprefix tailTrace_5355268
  have hstable : (prefixWord ++ tailWord_5355268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355268).length < 2 ^ (prefixWord ++ tailWord_5355268).sum := by decide
  have hdescent : baseEnd_5355268 < baseStart_5355268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355291 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 6, 2, 2]
def baseStart_5355291 : Nat := 118140960795 + 5355291 * 2 ^ 59
def prefixEnd_5355291 : Nat := 4983230072969 + 3 ^ 40 * 5355291 * 2
def baseEnd_5355291 : Nat := 2749838327697112133033971

theorem tailTrace_5355291 : CollatzResearch.WordTrace tailWord_5355291 prefixEnd_5355291 2749838327697112133033971 := by
  unfold tailWord_5355291
  simp only [CollatzResearch.WordTrace]
  refine ⟨195323509241702792732017727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130215672827801861821345151 195323509241702792732017727)
  ·
    refine ⟨292985263862554189098026591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195323509241702792732017727 292985263862554189098026591)
    ·
      refine ⟨439477895793831283647039887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292985263862554189098026591 439477895793831283647039887)
      ·
        refine ⟨659216843690746925470559831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439477895793831283647039887 659216843690746925470559831)
        ·
          refine ⟨988825265536120388205839747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659216843690746925470559831 988825265536120388205839747)
          ·
            refine ⟨1483237898304180582308759621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988825265536120388205839747 1483237898304180582308759621)
            ·
              refine ⟨278107105932033859182892429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1483237898304180582308759621 278107105932033859182892429)
              ·
                refine ⟨104290164724512697193584661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278107105932033859182892429 104290164724512697193584661)
                ·
                  refine ⟨4888601471461532680949281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104290164724512697193584661 4888601471461532680949281)
                  ·
                    refine ⟨3666451103596149510711961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888601471461532680949281 3666451103596149510711961)
                    ·
                      refine ⟨2749838327697112133033971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666451103596149510711961 2749838327697112133033971)
                      ·
                        rfl

theorem cell23_5355291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 2, 2].length) (baseStart_5355291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355291 prefixEnd_5355291 := by exact prefixLift 5355291
  have htrace : WordTrace (prefixWord ++ tailWord_5355291) baseStart_5355291 baseEnd_5355291 := by
    simpa [prefixWord, tailWord_5355291, baseEnd_5355291] using wordTrace_append hprefix tailTrace_5355291
  have hstable : (prefixWord ++ tailWord_5355291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355291).length < 2 ^ (prefixWord ++ tailWord_5355291).sum := by decide
  have hdescent : baseEnd_5355291 < baseStart_5355291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355308 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_5355308 : Nat := 118140960795 + 5355308 * 2 ^ 59
def prefixEnd_5355308 : Nat := 4983230072969 + 3 ^ 40 * 5355308 * 2
def baseEnd_5355308 : Nat := 2749847056868238566521393

theorem tailTrace_5355308 : CollatzResearch.WordTrace tailWord_5355308 prefixEnd_5355308 2749847056868238566521393 := by
  unfold tailWord_5355308
  simp only [CollatzResearch.WordTrace]
  refine ⟨97662064641320602317693289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130216086188427469756924385 97662064641320602317693289)
  ·
    refine ⟨73246548480990451738269967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97662064641320602317693289 73246548480990451738269967)
    ·
      refine ⟨109869822721485677607404951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73246548480990451738269967 109869822721485677607404951)
      ·
        refine ⟨164804734082228516411107427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109869822721485677607404951 164804734082228516411107427)
        ·
          refine ⟨247207101123342774616661141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164804734082228516411107427 247207101123342774616661141)
          ·
            refine ⟨11587832865156692560155991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 247207101123342774616661141 11587832865156692560155991)
            ·
              refine ⟨17381749297735038840233987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11587832865156692560155991 17381749297735038840233987)
              ·
                refine ⟨26072623946602558260350981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17381749297735038840233987 26072623946602558260350981)
                ·
                  refine ⟨4888616989987979673815809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26072623946602558260350981 4888616989987979673815809)
                  ·
                    refine ⟨3666462742490984755361857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4888616989987979673815809 3666462742490984755361857)
                    ·
                      refine ⟨2749847056868238566521393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666462742490984755361857 2749847056868238566521393)
                      ·
                        rfl

theorem cell23_5355308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_5355308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355308 prefixEnd_5355308 := by exact prefixLift 5355308
  have htrace : WordTrace (prefixWord ++ tailWord_5355308) baseStart_5355308 baseEnd_5355308 := by
    simpa [prefixWord, tailWord_5355308, baseEnd_5355308] using wordTrace_append hprefix tailTrace_5355308
  have hstable : (prefixWord ++ tailWord_5355308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355308).length < 2 ^ (prefixWord ++ tailWord_5355308).sum := by decide
  have hdescent : baseEnd_5355308 < baseStart_5355308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355314 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_5355314 : Nat := 118140960795 + 5355314 * 2 ^ 59
def prefixEnd_5355314 : Nat := 4983230072969 + 3 ^ 40 * 5355314 * 2
def baseEnd_5355314 : Nat := 305538904194685060338485

theorem tailTrace_5355314 : CollatzResearch.WordTrace tailWord_5355314 prefixEnd_5355314 305538904194685060338485 := by
  unfold tailWord_5355314
  simp only [CollatzResearch.WordTrace]
  refine ⟨48831087030154866915026249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130216232080412978440069997 48831087030154866915026249)
  ·
    refine ⟨36623315272616150186269687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48831087030154866915026249 36623315272616150186269687)
    ·
      refine ⟨54934972908924225279404531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36623315272616150186269687 54934972908924225279404531)
      ·
        refine ⟨82402459363386337919106797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54934972908924225279404531 82402459363386337919106797)
        ·
          refine ⟨30900922261269876719665049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82402459363386337919106797 30900922261269876719665049)
          ·
            refine ⟨23175691695952407539748787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30900922261269876719665049 23175691695952407539748787)
            ·
              refine ⟨34763537543928611309623181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23175691695952407539748787 34763537543928611309623181)
              ·
                refine ⟨13036326578973229241108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34763537543928611309623181 13036326578973229241108693)
                ·
                  refine ⟨305538904194685060338485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13036326578973229241108693 305538904194685060338485)
                  ·
                    rfl

theorem cell23_5355314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_5355314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355314 prefixEnd_5355314 := by exact prefixLift 5355314
  have htrace : WordTrace (prefixWord ++ tailWord_5355314) baseStart_5355314 baseEnd_5355314 := by
    simpa [prefixWord, tailWord_5355314, baseEnd_5355314] using wordTrace_append hprefix tailTrace_5355314
  have hstable : (prefixWord ++ tailWord_5355314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355314).length < 2 ^ (prefixWord ++ tailWord_5355314).sum := by decide
  have hdescent : baseEnd_5355314 < baseStart_5355314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355325 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5355325 : Nat := 118140960795 + 5355325 * 2 ^ 59
def prefixEnd_5355325 : Nat := 4983230072969 + 3 ^ 40 * 5355325 * 2
def baseEnd_5355325 : Nat := 2749855786039365000008815

theorem tailTrace_5355325 : CollatzResearch.WordTrace tailWord_5355325 prefixEnd_5355325 2749855786039365000008815 := by
  unfold tailWord_5355325
  simp only [CollatzResearch.WordTrace]
  refine ⟨195324749323579616538755429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130216499549053077692503619 195324749323579616538755429)
  ·
    refine ⟨36623390498171178101016643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195324749323579616538755429 36623390498171178101016643)
    ·
      refine ⟨54935085747256767151524965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36623390498171178101016643 54935085747256767151524965)
      ·
        refine ⟨10300328577610643840910931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54935085747256767151524965 10300328577610643840910931)
        ·
          refine ⟨15450492866415965761366397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10300328577610643840910931 15450492866415965761366397)
          ·
            refine ⟨5793934824905987160512399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15450492866415965761366397 5793934824905987160512399)
            ·
              refine ⟨8690902237358980740768599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793934824905987160512399 8690902237358980740768599)
              ·
                refine ⟨13036353356038471111152899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690902237358980740768599 13036353356038471111152899)
                ·
                  refine ⟨19554530034057706666729349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13036353356038471111152899 19554530034057706666729349)
                  ·
                    refine ⟨3666474381385820000011753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19554530034057706666729349 3666474381385820000011753)
                    ·
                      refine ⟨2749855786039365000008815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666474381385820000011753 2749855786039365000008815)
                      ·
                        rfl

theorem cell23_5355325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5355325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355325 prefixEnd_5355325 := by exact prefixLift 5355325
  have htrace : WordTrace (prefixWord ++ tailWord_5355325) baseStart_5355325 baseEnd_5355325 := by
    simpa [prefixWord, tailWord_5355325, baseEnd_5355325] using wordTrace_append hprefix tailTrace_5355325
  have hstable : (prefixWord ++ tailWord_5355325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355325).length < 2 ^ (prefixWord ++ tailWord_5355325).sum := by decide
  have hdescent : baseEnd_5355325 < baseStart_5355325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355344 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_5355344 : Nat := 118140960795 + 5355344 * 2 ^ 59
def prefixEnd_5355344 : Nat := 4983230072969 + 3 ^ 40 * 5355344 * 2
def baseEnd_5355344 : Nat := 916621847390600141890409

theorem tailTrace_5355344 : CollatzResearch.WordTrace tailWord_5355344 prefixEnd_5355344 916621847390600141890409 := by
  unfold tailWord_5355344
  simp only [CollatzResearch.WordTrace]
  refine ⟨97662721155255391391848543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130216961540340521855798057 97662721155255391391848543)
  ·
    refine ⟨146494081732883087087772815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97662721155255391391848543 146494081732883087087772815)
    ·
      refine ⟨219741122599324630631659223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146494081732883087087772815 219741122599324630631659223)
      ·
        refine ⟨329611683898986945947488835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219741122599324630631659223 329611683898986945947488835)
        ·
          refine ⟨494417525848480418921233253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329611683898986945947488835 494417525848480418921233253)
          ·
            refine ⟨92703286096590078547731235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 494417525848480418921233253 92703286096590078547731235)
            ·
              refine ⟨139054929144885117821596853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92703286096590078547731235 139054929144885117821596853)
              ·
                refine ⟨13036399607332979795774705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139054929144885117821596853 13036399607332979795774705)
                ·
                  refine ⟨9777299705499734846831029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13036399607332979795774705 9777299705499734846831029)
                  ·
                    refine ⟨916621847390600141890409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9777299705499734846831029 916621847390600141890409)
                    ·
                      rfl

theorem cell23_5355344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_5355344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355344 prefixEnd_5355344 := by exact prefixLift 5355344
  have htrace : WordTrace (prefixWord ++ tailWord_5355344) baseStart_5355344 baseEnd_5355344 := by
    simpa [prefixWord, tailWord_5355344, baseEnd_5355344] using wordTrace_append hprefix tailTrace_5355344
  have hstable : (prefixWord ++ tailWord_5355344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355344).length < 2 ^ (prefixWord ++ tailWord_5355344).sum := by decide
  have hdescent : baseEnd_5355344 < baseStart_5355344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355348 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 5]
def baseStart_5355348 : Nat := 118140960795 + 5355348 * 2 ^ 59
def prefixEnd_5355348 : Nat := 4983230072969 + 3 ^ 40 * 5355348 * 2
def baseEnd_5355348 : Nat := 305540844010490934446801

theorem tailTrace_5355348 : CollatzResearch.WordTrace tailWord_5355348 prefixEnd_5355348 305540844010490934446801 := by
  unfold tailWord_5355348
  simp only [CollatzResearch.WordTrace]
  refine ⟨97662794101248145733421349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130217058801664194311228465 97662794101248145733421349)
  ·
    refine ⟨18311773893984027325016503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97662794101248145733421349 18311773893984027325016503)
    ·
      refine ⟨27467660840976040987524755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18311773893984027325016503 27467660840976040987524755)
      ·
        refine ⟨41201491261464061481287133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27467660840976040987524755 41201491261464061481287133)
        ·
          refine ⟨15450559223049023055482675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41201491261464061481287133 15450559223049023055482675)
          ·
            refine ⟨23175838834573534583224013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15450559223049023055482675 23175838834573534583224013)
            ·
              refine ⟨8690939562965075468709005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23175838834573534583224013 8690939562965075468709005)
              ·
                refine ⟨3259102336111903300765877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8690939562965075468709005 3259102336111903300765877)
                ·
                  refine ⟨305540844010490934446801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259102336111903300765877 305540844010490934446801)
                  ·
                    rfl

theorem cell23_5355348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_5355348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355348 prefixEnd_5355348 := by exact prefixLift 5355348
  have htrace : WordTrace (prefixWord ++ tailWord_5355348) baseStart_5355348 baseEnd_5355348 := by
    simpa [prefixWord, tailWord_5355348, baseEnd_5355348] using wordTrace_append hprefix tailTrace_5355348
  have hstable : (prefixWord ++ tailWord_5355348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355348).length < 2 ^ (prefixWord ++ tailWord_5355348).sum := by decide
  have hdescent : baseEnd_5355348 < baseStart_5355348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355354 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5355354 : Nat := 118140960795 + 5355354 * 2 ^ 59
def prefixEnd_5355354 : Nat := 4983230072969 + 3 ^ 40 * 5355354 * 2
def baseEnd_5355354 : Nat := 2749870676978345386546181

theorem tailTrace_5355354 : CollatzResearch.WordTrace tailWord_5355354 prefixEnd_5355354 2749870676978345386546181 := by
  unfold tailWord_5355354
  simp only [CollatzResearch.WordTrace]
  refine ⟨48831451760118638622890279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130217204693649702994374077 48831451760118638622890279)
  ·
    refine ⟨73247177640177957934335419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48831451760118638622890279 73247177640177957934335419)
    ·
      refine ⟨109870766460266936901503129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73247177640177957934335419 109870766460266936901503129)
      ·
        refine ⟨82403074845200202676127347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109870766460266936901503129 82403074845200202676127347)
        ·
          refine ⟨123604612267800304014191021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82403074845200202676127347 123604612267800304014191021)
          ·
            refine ⟨46351729600425114005321633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123604612267800304014191021 46351729600425114005321633)
            ·
              refine ⟨34763797200318835503991225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46351729600425114005321633 34763797200318835503991225)
              ·
                refine ⟨26072847900239126627993419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34763797200318835503991225 26072847900239126627993419)
                ·
                  refine ⟨39109271850358689941990129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26072847900239126627993419 39109271850358689941990129)
                  ·
                    refine ⟨29331953887769017456492597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39109271850358689941990129 29331953887769017456492597)
                    ·
                      refine ⟨2749870676978345386546181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29331953887769017456492597 2749870676978345386546181)
                      ·
                        rfl

theorem cell23_5355354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5355354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355354 prefixEnd_5355354 := by exact prefixLift 5355354
  have htrace : WordTrace (prefixWord ++ tailWord_5355354) baseStart_5355354 baseEnd_5355354 := by
    simpa [prefixWord, tailWord_5355354, baseEnd_5355354] using wordTrace_append hprefix tailTrace_5355354
  have hstable : (prefixWord ++ tailWord_5355354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355354).length < 2 ^ (prefixWord ++ tailWord_5355354).sum := by decide
  have hdescent : baseEnd_5355354 < baseStart_5355354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355381 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5355381 : Nat := 118140960795 + 5355381 * 2 ^ 59
def prefixEnd_5355381 : Nat := 4983230072969 + 3 ^ 40 * 5355381 * 2
def baseEnd_5355381 : Nat := 2749884540956016780908557

theorem tailTrace_5355381 : CollatzResearch.WordTrace tailWord_5355381 prefixEnd_5355381 2749884540956016780908557 := by
  unfold tailWord_5355381
  simp only [CollatzResearch.WordTrace]
  refine ⟨195326791811376738102793997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130217861207584492068529331 195326791811376738102793997)
  ·
    refine ⟨73247546929266276788547749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195326791811376738102793997 73247546929266276788547749)
    ·
      refine ⟨13733915049237426897852703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73247546929266276788547749 13733915049237426897852703)
      ·
        refine ⟨20600872573856140346779055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13733915049237426897852703 20600872573856140346779055)
        ·
          refine ⟨30901308860784210520168583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20600872573856140346779055 30901308860784210520168583)
          ·
            refine ⟨46351963291176315780252875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30901308860784210520168583 46351963291176315780252875)
            ·
              refine ⟨69527944936764473670379313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46351963291176315780252875 69527944936764473670379313)
              ·
                refine ⟨52145958702573355252784485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69527944936764473670379313 52145958702573355252784485)
                ·
                  refine ⟨9777367256732504109897091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52145958702573355252784485 9777367256732504109897091)
                  ·
                    refine ⟨14666050885098756164845637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9777367256732504109897091 14666050885098756164845637)
                    ·
                      refine ⟨2749884540956016780908557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14666050885098756164845637 2749884540956016780908557)
                      ·
                        rfl

theorem cell23_5355381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5355381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355381 prefixEnd_5355381 := by exact prefixLift 5355381
  have htrace : WordTrace (prefixWord ++ tailWord_5355381) baseStart_5355381 baseEnd_5355381 := by
    simpa [prefixWord, tailWord_5355381, baseEnd_5355381] using wordTrace_append hprefix tailTrace_5355381
  have hstable : (prefixWord ++ tailWord_5355381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355381).length < 2 ^ (prefixWord ++ tailWord_5355381).sum := by decide
  have hdescent : baseEnd_5355381 < baseStart_5355381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355418 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5355418 : Nat := 118140960795 + 5355418 * 2 ^ 59
def prefixEnd_5355418 : Nat := 4983230072969 + 3 ^ 40 * 5355418 * 2
def baseEnd_5355418 : Nat := 2749903539740233136145887

theorem tailTrace_5355418 : CollatzResearch.WordTrace tailWord_5355418 prefixEnd_5355418 2749903539740233136145887 := by
  unfold tailWord_5355418
  simp only [CollatzResearch.WordTrace]
  refine ⟨48832035328060673355472727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130218760874828462281260605 48832035328060673355472727)
  ·
    refine ⟨73248052992091010033209091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48832035328060673355472727 73248052992091010033209091)
    ·
      refine ⟨109872079488136515049813637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73248052992091010033209091 109872079488136515049813637)
      ·
        refine ⟨20601014904025596571840057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109872079488136515049813637 20601014904025596571840057)
        ·
          refine ⟨15450761178019197428880043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20601014904025596571840057 15450761178019197428880043)
          ·
            refine ⟨23176141767028796143320065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15450761178019197428880043 23176141767028796143320065)
            ·
              refine ⟨17382106325271597107490049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23176141767028796143320065 17382106325271597107490049)
              ·
                refine ⟨13036579743953697830617537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17382106325271597107490049 13036579743953697830617537)
                ·
                  refine ⟨9777434807965273372963153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13036579743953697830617537 9777434807965273372963153)
                  ·
                    refine ⟨7333076105973955029722365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9777434807965273372963153 7333076105973955029722365)
                    ·
                      refine ⟨2749903539740233136145887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333076105973955029722365 2749903539740233136145887)
                      ·
                        rfl

theorem cell23_5355418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5355418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355418 prefixEnd_5355418 := by exact prefixLift 5355418
  have htrace : WordTrace (prefixWord ++ tailWord_5355418) baseStart_5355418 baseEnd_5355418 := by
    simpa [prefixWord, tailWord_5355418, baseEnd_5355418] using wordTrace_append hprefix tailTrace_5355418
  have hstable : (prefixWord ++ tailWord_5355418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355418).length < 2 ^ (prefixWord ++ tailWord_5355418).sum := by decide
  have hdescent : baseEnd_5355418 < baseStart_5355418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355421 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 6]
def baseStart_5355421 : Nat := 118140960795 + 5355421 * 2 ^ 59
def prefixEnd_5355421 : Nat := 4983230072969 + 3 ^ 40 * 5355421 * 2
def baseEnd_5355421 : Nat := 305545008909132958267597

theorem tailTrace_5355421 : CollatzResearch.WordTrace tailWord_5355421 prefixEnd_5355421 305545008909132958267597 := by
  unfold tailWord_5355421
  simp only [CollatzResearch.WordTrace]
  refine ⟨195328250731231824934250117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130218833820821216622833411 195328250731231824934250117)
  ·
    refine ⟨36624047012105967175171897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195328250731231824934250117 36624047012105967175171897)
    ·
      refine ⟨27468035259079475381378923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36624047012105967175171897 27468035259079475381378923)
      ·
        refine ⟨41202052888619213072068385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27468035259079475381378923 41202052888619213072068385)
        ·
          refine ⟨30901539666464409804051289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41202052888619213072068385 30901539666464409804051289)
          ·
            refine ⟨23176154749848307353038467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30901539666464409804051289 23176154749848307353038467)
            ·
              refine ⟨34764232124772461029557701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23176154749848307353038467 34764232124772461029557701)
              ·
                refine ⟨6518293523394836443042069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34764232124772461029557701 6518293523394836443042069)
                ·
                  refine ⟨305545008909132958267597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6518293523394836443042069 305545008909132958267597)
                  ·
                    rfl

theorem cell23_5355421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_5355421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355421 prefixEnd_5355421 := by exact prefixLift 5355421
  have htrace : WordTrace (prefixWord ++ tailWord_5355421) baseStart_5355421 baseEnd_5355421 := by
    simpa [prefixWord, tailWord_5355421, baseEnd_5355421] using wordTrace_append hprefix tailTrace_5355421
  have hstable : (prefixWord ++ tailWord_5355421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355421).length < 2 ^ (prefixWord ++ tailWord_5355421).sum := by decide
  have hdescent : baseEnd_5355421 < baseStart_5355421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355424 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5355424 : Nat := 118140960795 + 5355424 * 2 ^ 59
def prefixEnd_5355424 : Nat := 4983230072969 + 3 ^ 40 * 5355424 * 2
def baseEnd_5355424 : Nat := 2749906620624160112670859

theorem tailTrace_5355424 : CollatzResearch.WordTrace tailWord_5355424 prefixEnd_5355424 2749906620624160112670859 := by
  unfold tailWord_5355424
  simp only [CollatzResearch.WordTrace]
  refine ⟨97664180075110478223304663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130218906766813970964406217 97664180075110478223304663)
  ·
    refine ⟨146496270112665717334956995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97664180075110478223304663 146496270112665717334956995)
    ·
      refine ⟨219744405168998576002435493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146496270112665717334956995 219744405168998576002435493)
      ·
        refine ⟨41202075969187233000456655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219744405168998576002435493 41202075969187233000456655)
        ·
          refine ⟨61803113953780849500684983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41202075969187233000456655 61803113953780849500684983)
          ·
            refine ⟨92704670930671274251027475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61803113953780849500684983 92704670930671274251027475)
            ·
              refine ⟨139057006396006911376541213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92704670930671274251027475 139057006396006911376541213)
              ·
                refine ⟨52146377398502591766202955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139057006396006911376541213 52146377398502591766202955)
                ·
                  refine ⟨78219566097753887649304433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52146377398502591766202955 78219566097753887649304433)
                  ·
                    refine ⟨58664674573315415736978325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78219566097753887649304433 58664674573315415736978325)
                    ·
                      refine ⟨2749906620624160112670859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58664674573315415736978325 2749906620624160112670859)
                      ·
                        rfl

theorem cell23_5355424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5355424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355424 prefixEnd_5355424 := by exact prefixLift 5355424
  have htrace : WordTrace (prefixWord ++ tailWord_5355424) baseStart_5355424 baseEnd_5355424 := by
    simpa [prefixWord, tailWord_5355424, baseEnd_5355424] using wordTrace_append hprefix tailTrace_5355424
  have hstable : (prefixWord ++ tailWord_5355424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355424).length < 2 ^ (prefixWord ++ tailWord_5355424).sum := by decide
  have hdescent : baseEnd_5355424 < baseStart_5355424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355432 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5355432 : Nat := 118140960795 + 5355432 * 2 ^ 59
def prefixEnd_5355432 : Nat := 4983230072969 + 3 ^ 40 * 5355432 * 2
def baseEnd_5355432 : Nat := 2749910728469396081370823

theorem tailTrace_5355432 : CollatzResearch.WordTrace tailWord_5355432 prefixEnd_5355432 2749910728469396081370823 := by
  unfold tailWord_5355432
  simp only [CollatzResearch.WordTrace]
  refine ⟨97664325967095986906450275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130219101289461315875267033 97664325967095986906450275)
  ·
    refine ⟨146496488950643980359675413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97664325967095986906450275 146496488950643980359675413)
    ·
      refine ⟨6867022919561436579359785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146496488950643980359675413 6867022919561436579359785)
      ·
        refine ⟨5150267189671077434519839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6867022919561436579359785 5150267189671077434519839)
        ·
          refine ⟨7725400784506616151779759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150267189671077434519839 7725400784506616151779759)
          ·
            refine ⟨11588101176759924227669639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725400784506616151779759 11588101176759924227669639)
            ·
              refine ⟨17382151765139886341504459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11588101176759924227669639 17382151765139886341504459)
              ·
                refine ⟨26073227647709829512256689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17382151765139886341504459 26073227647709829512256689)
                ·
                  refine ⟨19554920735782372134192517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26073227647709829512256689 19554920735782372134192517)
                  ·
                    refine ⟨3666547637959194775161097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19554920735782372134192517 3666547637959194775161097)
                    ·
                      refine ⟨2749910728469396081370823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666547637959194775161097 2749910728469396081370823)
                      ·
                        rfl

theorem cell23_5355432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5355432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355432 prefixEnd_5355432 := by exact prefixLift 5355432
  have htrace : WordTrace (prefixWord ++ tailWord_5355432) baseStart_5355432 baseEnd_5355432 := by
    simpa [prefixWord, tailWord_5355432, baseEnd_5355432] using wordTrace_append hprefix tailTrace_5355432
  have hstable : (prefixWord ++ tailWord_5355432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355432).length < 2 ^ (prefixWord ++ tailWord_5355432).sum := by decide
  have hdescent : baseEnd_5355432 < baseStart_5355432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355448 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_5355448 : Nat := 118140960795 + 5355448 * 2 ^ 59
def prefixEnd_5355448 : Nat := 4983230072969 + 3 ^ 40 * 5355448 * 2
def baseEnd_5355448 : Nat := 2749918944159868018770749

theorem tailTrace_5355448 : CollatzResearch.WordTrace tailWord_5355448 prefixEnd_5355448 2749918944159868018770749 := by
  unfold tailWord_5355448
  simp only [CollatzResearch.WordTrace]
  refine ⟨97664617751067004272741499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130219490334756005696988665 97664617751067004272741499)
  ·
    refine ⟨146496926626600506409112249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97664617751067004272741499 146496926626600506409112249)
    ·
      refine ⟨109872694969950379806834187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146496926626600506409112249 109872694969950379806834187)
      ·
        refine ⟨164809042454925569710251281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109872694969950379806834187 164809042454925569710251281)
        ·
          refine ⟨123606781841194177282688461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164809042454925569710251281 123606781841194177282688461)
          ·
            refine ⟨46352543190447816481008173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123606781841194177282688461 46352543190447816481008173)
            ·
              refine ⟨17382203696417931180378065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46352543190447816481008173 17382203696417931180378065)
              ·
                refine ⟨13036652772313448385283549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17382203696417931180378065 13036652772313448385283549)
                ·
                  refine ⟨4888744789617543144481331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13036652772313448385283549 4888744789617543144481331)
                  ·
                    refine ⟨7333117184426314716721997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888744789617543144481331 7333117184426314716721997)
                    ·
                      refine ⟨2749918944159868018770749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333117184426314716721997 2749918944159868018770749)
                      ·
                        rfl

theorem cell23_5355448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_5355448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355448 prefixEnd_5355448 := by exact prefixLift 5355448
  have htrace : WordTrace (prefixWord ++ tailWord_5355448) baseStart_5355448 baseEnd_5355448 := by
    simpa [prefixWord, tailWord_5355448, baseEnd_5355448] using wordTrace_append hprefix tailTrace_5355448
  have hstable : (prefixWord ++ tailWord_5355448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355448).length < 2 ^ (prefixWord ++ tailWord_5355448).sum := by decide
  have hdescent : baseEnd_5355448 < baseStart_5355448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355452 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5355452 : Nat := 118140960795 + 5355452 * 2 ^ 59
def prefixEnd_5355452 : Nat := 4983230072969 + 3 ^ 40 * 5355452 * 2
def baseEnd_5355452 : Nat := 2749920998082486003120731

theorem tailTrace_5355452 : CollatzResearch.WordTrace tailWord_5355452 prefixEnd_5355452 2749920998082486003120731 := by
  unfold tailWord_5355452
  simp only [CollatzResearch.WordTrace]
  refine ⟨97664690697059758614314305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130219587596079678152419073 97664690697059758614314305)
  ·
    refine ⟨73248518022794818960735729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97664690697059758614314305 73248518022794818960735729)
    ·
      refine ⟨54936388517096114220551797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73248518022794818960735729 54936388517096114220551797)
      ·
        refine ⟨5150286423477760708176731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54936388517096114220551797 5150286423477760708176731)
        ·
          refine ⟨7725429635216641062265097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150286423477760708176731 7725429635216641062265097)
          ·
            refine ⟨5794072226412480796698823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7725429635216641062265097 5794072226412480796698823)
            ·
              refine ⟨8691108339618721195048235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794072226412480796698823 8691108339618721195048235)
              ·
                refine ⟨13036662509428081792572353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691108339618721195048235 13036662509428081792572353)
                ·
                  refine ⟨9777496882071061344429265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13036662509428081792572353 9777496882071061344429265)
                  ·
                    refine ⟨7333122661553296008321949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9777496882071061344429265 7333122661553296008321949)
                    ·
                      refine ⟨2749920998082486003120731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333122661553296008321949 2749920998082486003120731)
                      ·
                        rfl

theorem cell23_5355452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5355452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355452 prefixEnd_5355452 := by exact prefixLift 5355452
  have htrace : WordTrace (prefixWord ++ tailWord_5355452) baseStart_5355452 baseEnd_5355452 := by
    simpa [prefixWord, tailWord_5355452, baseEnd_5355452] using wordTrace_append hprefix tailTrace_5355452
  have hstable : (prefixWord ++ tailWord_5355452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355452).length < 2 ^ (prefixWord ++ tailWord_5355452).sum := by decide
  have hdescent : baseEnd_5355452 < baseStart_5355452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355468 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_5355468 : Nat := 118140960795 + 5355468 * 2 ^ 59
def prefixEnd_5355468 : Nat := 4983230072969 + 3 ^ 40 * 5355468 * 2
def baseEnd_5355468 : Nat := 916643071257652646840219

theorem tailTrace_5355468 : CollatzResearch.WordTrace tailWord_5355468 prefixEnd_5355468 916643071257652646840219 := by
  unfold tailWord_5355468
  simp only [CollatzResearch.WordTrace]
  refine ⟨97664982481030775980605529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130219976641374367974140705 97664982481030775980605529)
  ·
    refine ⟨73248736860773081985454147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97664982481030775980605529 73248736860773081985454147)
    ·
      refine ⟨109873105291159622978181221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73248736860773081985454147 109873105291159622978181221)
      ·
        refine ⟨20601207242092429308408979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109873105291159622978181221 20601207242092429308408979)
        ·
          refine ⟨30901810863138643962613469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20601207242092429308408979 30901810863138643962613469)
          ·
            refine ⟨11588179073676991485980051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30901810863138643962613469 11588179073676991485980051)
            ·
              refine ⟨17382268610515487228970077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11588179073676991485980051 17382268610515487228970077)
              ·
                refine ⟨6518350728943307710863779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17382268610515487228970077 6518350728943307710863779)
                ·
                  refine ⟨9777526093414961566295669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518350728943307710863779 9777526093414961566295669)
                  ·
                    refine ⟨916643071257652646840219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9777526093414961566295669 916643071257652646840219)
                    ·
                      rfl

theorem cell23_5355468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_5355468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355468 prefixEnd_5355468 := by exact prefixLift 5355468
  have htrace : WordTrace (prefixWord ++ tailWord_5355468) baseStart_5355468 baseEnd_5355468 := by
    simpa [prefixWord, tailWord_5355468, baseEnd_5355468] using wordTrace_append hprefix tailTrace_5355468
  have hstable : (prefixWord ++ tailWord_5355468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355468).length < 2 ^ (prefixWord ++ tailWord_5355468).sum := by decide
  have hdescent : baseEnd_5355468 < baseStart_5355468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355491 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5355491 : Nat := 118140960795 + 5355491 * 2 ^ 59
def prefixEnd_5355491 : Nat := 4983230072969 + 3 ^ 40 * 5355491 * 2
def baseEnd_5355491 : Nat := 2749941023828011350533051

theorem tailTrace_5355491 : CollatzResearch.WordTrace tailWord_5355491 prefixEnd_5355491 2749941023828011350533051 := by
  unfold tailWord_5355491
  simp only [CollatzResearch.WordTrace]
  refine ⟨195330803840978226889298327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130220535893985484592865551 195330803840978226889298327)
  ·
    refine ⟨292996205761467340333947491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195330803840978226889298327 292996205761467340333947491)
    ·
      refine ⟨439494308642201010500921237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292996205761467340333947491 439494308642201010500921237)
      ·
        refine ⟨20601295717603172367230683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 439494308642201010500921237 20601295717603172367230683)
        ·
          refine ⟨30901943576404758550846025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20601295717603172367230683 30901943576404758550846025)
          ·
            refine ⟨23176457682303568913134519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30901943576404758550846025 23176457682303568913134519)
            ·
              refine ⟨34764686523455353369701779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23176457682303568913134519 34764686523455353369701779)
              ·
                refine ⟨52147029785183030054552669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34764686523455353369701779 52147029785183030054552669)
                ·
                  refine ⟨19555136169443636270457251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52147029785183030054552669 19555136169443636270457251)
                  ·
                    refine ⟨29332704254165454405685877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19555136169443636270457251 29332704254165454405685877)
                    ·
                      refine ⟨2749941023828011350533051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29332704254165454405685877 2749941023828011350533051)
                      ·
                        rfl

theorem cell23_5355491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5355491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355491 prefixEnd_5355491 := by exact prefixLift 5355491
  have htrace : WordTrace (prefixWord ++ tailWord_5355491) baseStart_5355491 baseEnd_5355491 := by
    simpa [prefixWord, tailWord_5355491, baseEnd_5355491] using wordTrace_append hprefix tailTrace_5355491
  have hstable : (prefixWord ++ tailWord_5355491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355491).length < 2 ^ (prefixWord ++ tailWord_5355491).sum := by decide
  have hdescent : baseEnd_5355491 < baseStart_5355491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355505 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_5355505 : Nat := 118140960795 + 5355505 * 2 ^ 59
def prefixEnd_5355505 : Nat := 4983230072969 + 3 ^ 40 * 5355505 * 2
def baseEnd_5355505 : Nat := 2749948212557174295757987

theorem tailTrace_5355505 : CollatzResearch.WordTrace tailWord_5355505 prefixEnd_5355505 2749948212557174295757987 := by
  unfold tailWord_5355505
  simp only [CollatzResearch.WordTrace]
  refine ⟨195331314462927507280307969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130220876308618338186871979 195331314462927507280307969)
  ·
    refine ⟨146498485847195630460230977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195331314462927507280307969 146498485847195630460230977)
    ·
      refine ⟨109873864385396722845173233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146498485847195630460230977 109873864385396722845173233)
      ·
        refine ⟨82405398289047542133879925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109873864385396722845173233 82405398289047542133879925)
        ·
          refine ⟨7725506089598207075051243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82405398289047542133879925 7725506089598207075051243)
          ·
            refine ⟨11588259134397310612576865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725506089598207075051243 11588259134397310612576865)
            ·
              refine ⟨8691194350797982959432649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11588259134397310612576865 8691194350797982959432649)
              ·
                refine ⟨6518395763098487219574487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8691194350797982959432649 6518395763098487219574487)
                ·
                  refine ⟨9777593644647730829361731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518395763098487219574487 9777593644647730829361731)
                  ·
                    refine ⟨14666390466971596244042597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9777593644647730829361731 14666390466971596244042597)
                    ·
                      refine ⟨2749948212557174295757987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14666390466971596244042597 2749948212557174295757987)
                      ·
                        rfl

theorem cell23_5355505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_5355505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355505 prefixEnd_5355505 := by exact prefixLift 5355505
  have htrace : WordTrace (prefixWord ++ tailWord_5355505) baseStart_5355505 baseEnd_5355505 := by
    simpa [prefixWord, tailWord_5355505, baseEnd_5355505] using wordTrace_append hprefix tailTrace_5355505
  have hstable : (prefixWord ++ tailWord_5355505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355505).length < 2 ^ (prefixWord ++ tailWord_5355505).sum := by decide
  have hdescent : baseEnd_5355505 < baseStart_5355505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355533 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5355533 : Nat := 118140960795 + 5355533 * 2 ^ 59
def prefixEnd_5355533 : Nat := 4983230072969 + 3 ^ 40 * 5355533 * 2
def baseEnd_5355533 : Nat := 2749962590015500186207859

theorem tailTrace_5355533 : CollatzResearch.WordTrace tailWord_5355533 prefixEnd_5355533 2749962590015500186207859 := by
  unfold tailWord_5355533
  simp only [CollatzResearch.WordTrace]
  refine ⟨195332335706826068062327253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130221557137884045374884835 195332335706826068062327253)
  ·
    refine ⟨4578101618128735970210795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 195332335706826068062327253 4578101618128735970210795)
    ·
      refine ⟨6867152427193103955316193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578101618128735970210795 6867152427193103955316193)
      ·
        refine ⟨5150364320394827966487145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6867152427193103955316193 5150364320394827966487145)
        ·
          refine ⟨3862773240296120974865359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5150364320394827966487145 3862773240296120974865359)
          ·
            refine ⟨5794159860444181462298039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862773240296120974865359 5794159860444181462298039)
            ·
              refine ⟨8691239790666272193447059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794159860444181462298039 8691239790666272193447059)
              ·
                refine ⟨13036859685999408290170589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691239790666272193447059 13036859685999408290170589)
                ·
                  refine ⟨4888822382249778108813971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13036859685999408290170589 4888822382249778108813971)
                  ·
                    refine ⟨7333233573374667163220957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888822382249778108813971 7333233573374667163220957)
                    ·
                      refine ⟨2749962590015500186207859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333233573374667163220957 2749962590015500186207859)
                      ·
                        rfl

theorem cell23_5355533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5355533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355533 prefixEnd_5355533 := by exact prefixLift 5355533
  have htrace : WordTrace (prefixWord ++ tailWord_5355533) baseStart_5355533 baseEnd_5355533 := by
    simpa [prefixWord, tailWord_5355533, baseEnd_5355533] using wordTrace_append hprefix tailTrace_5355533
  have hstable : (prefixWord ++ tailWord_5355533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355533).length < 2 ^ (prefixWord ++ tailWord_5355533).sum := by decide
  have hdescent : baseEnd_5355533 < baseStart_5355533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355555 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 3]
def baseStart_5355555 : Nat := 118140960795 + 5355555 * 2 ^ 59
def prefixEnd_5355555 : Nat := 4983230072969 + 3 ^ 40 * 5355555 * 2
def baseEnd_5355555 : Nat := 2749973886589899100132757

theorem tailTrace_5355555 : CollatzResearch.WordTrace tailWord_5355555 prefixEnd_5355555 2749973886589899100132757 := by
  unfold tailWord_5355555
  simp only [CollatzResearch.WordTrace]
  refine ⟨195333138112746365819628119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130222092075164243879752079 195333138112746365819628119)
  ·
    refine ⟨292999707169119548729442179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195333138112746365819628119 292999707169119548729442179)
    ·
      refine ⟨439499560753679323094163269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292999707169119548729442179 439499560753679323094163269)
      ·
        refine ⟨82406167641314873080155613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 439499560753679323094163269 82406167641314873080155613)
        ·
          refine ⟨30902312865493077405058355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82406167641314873080155613 30902312865493077405058355)
          ·
            refine ⟨46353469298239616107587533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30902312865493077405058355 46353469298239616107587533)
            ·
              refine ⟨17382550986839856040345325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46353469298239616107587533 17382550986839856040345325)
              ·
                refine ⟨6518456620064946015129497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17382550986839856040345325 6518456620064946015129497)
                ·
                  refine ⟨4888842465048709511347123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518456620064946015129497 4888842465048709511347123)
                  ·
                    refine ⟨7333263697573064267020685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4888842465048709511347123 7333263697573064267020685)
                    ·
                      refine ⟨2749973886589899100132757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333263697573064267020685 2749973886589899100132757)
                      ·
                        rfl

theorem cell23_5355555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_5355555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355555 prefixEnd_5355555 := by exact prefixLift 5355555
  have htrace : WordTrace (prefixWord ++ tailWord_5355555) baseStart_5355555 baseEnd_5355555 := by
    simpa [prefixWord, tailWord_5355555, baseEnd_5355555] using wordTrace_append hprefix tailTrace_5355555
  have hstable : (prefixWord ++ tailWord_5355555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355555).length < 2 ^ (prefixWord ++ tailWord_5355555).sum := by decide
  have hdescent : baseEnd_5355555 < baseStart_5355555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355559 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5355559 : Nat := 118140960795 + 5355559 * 2 ^ 59
def prefixEnd_5355559 : Nat := 4983230072969 + 3 ^ 40 * 5355559 * 2
def baseEnd_5355559 : Nat := 2749975940512517084482739

theorem tailTrace_5355559 : CollatzResearch.WordTrace tailWord_5355559 prefixEnd_5355559 2749975940512517084482739 := by
  unfold tailWord_5355559
  simp only [CollatzResearch.WordTrace]
  refine ⟨195333284004731874502773731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130222189336487916335182487 195333284004731874502773731)
  ·
    refine ⟨292999926007097811754160597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195333284004731874502773731 292999926007097811754160597)
    ·
      refine ⟨6867185765791354962988139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 292999926007097811754160597 6867185765791354962988139)
      ·
        refine ⟨10300778648687032444482209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867185765791354962988139 10300778648687032444482209)
        ·
          refine ⟨7725583986515274333361657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10300778648687032444482209 7725583986515274333361657)
          ·
            refine ⟨5794187989886455750021243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7725583986515274333361657 5794187989886455750021243)
            ·
              refine ⟨8691281984829683625031865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794187989886455750021243 8691281984829683625031865)
              ·
                refine ⟨6518461488622262718773899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8691281984829683625031865 6518461488622262718773899)
                ·
                  refine ⟨9777692232933394078160849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518461488622262718773899 9777692232933394078160849)
                  ·
                    refine ⟨7333269174700045558620637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9777692232933394078160849 7333269174700045558620637)
                    ·
                      refine ⟨2749975940512517084482739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333269174700045558620637 2749975940512517084482739)
                      ·
                        rfl

theorem cell23_5355559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5355559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355559 prefixEnd_5355559 := by exact prefixLift 5355559
  have htrace : WordTrace (prefixWord ++ tailWord_5355559) baseStart_5355559 baseEnd_5355559 := by
    simpa [prefixWord, tailWord_5355559, baseEnd_5355559] using wordTrace_append hprefix tailTrace_5355559
  have hstable : (prefixWord ++ tailWord_5355559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355559).length < 2 ^ (prefixWord ++ tailWord_5355559).sum := by decide
  have hdescent : baseEnd_5355559 < baseStart_5355559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355572 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5355572 : Nat := 118140960795 + 5355572 * 2 ^ 59
def prefixEnd_5355572 : Nat := 4983230072969 + 3 ^ 40 * 5355572 * 2
def baseEnd_5355572 : Nat := 2749982615761025533620179

theorem tailTrace_5355572 : CollatzResearch.WordTrace tailWord_5355572 prefixEnd_5355572 2749982615761025533620179 := by
  unfold tailWord_5355572
  simp only [CollatzResearch.WordTrace]
  refine ⟨97666879076842388861498485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130222505435789851815331313 97666879076842388861498485)
  ·
    refine ⟨9156269913453973955765483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97666879076842388861498485 9156269913453973955765483)
    ·
      refine ⟨13734404870180960933648225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9156269913453973955765483 13734404870180960933648225)
      ·
        refine ⟨10300803652635720700236169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13734404870180960933648225 10300803652635720700236169)
        ·
          refine ⟨7725602739476790525177127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10300803652635720700236169 7725602739476790525177127)
          ·
            refine ⟨11588404109215185787765691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725602739476790525177127 11588404109215185787765691)
            ·
              refine ⟨17382606163822778681648537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11588404109215185787765691 17382606163822778681648537)
              ·
                refine ⟨13036954622867084011236403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17382606163822778681648537 13036954622867084011236403)
                ·
                  refine ⟨19555431934300626016854605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13036954622867084011236403 19555431934300626016854605)
                  ·
                    refine ⟨7333286975362734756320477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19555431934300626016854605 7333286975362734756320477)
                    ·
                      refine ⟨2749982615761025533620179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333286975362734756320477 2749982615761025533620179)
                      ·
                        rfl

theorem cell23_5355572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5355572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355572 prefixEnd_5355572 := by exact prefixLift 5355572
  have htrace : WordTrace (prefixWord ++ tailWord_5355572) baseStart_5355572 baseEnd_5355572 := by
    simpa [prefixWord, tailWord_5355572, baseEnd_5355572] using wordTrace_append hprefix tailTrace_5355572
  have hstable : (prefixWord ++ tailWord_5355572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355572).length < 2 ^ (prefixWord ++ tailWord_5355572).sum := by decide
  have hdescent : baseEnd_5355572 < baseStart_5355572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355598 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_5355598 : Nat := 118140960795 + 5355598 * 2 ^ 59
def prefixEnd_5355598 : Nat := 4983230072969 + 3 ^ 40 * 5355598 * 2
def baseEnd_5355598 : Nat := 2749995966258042431895059

theorem tailTrace_5355598 : CollatzResearch.WordTrace tailWord_5355598 prefixEnd_5355598 2749995966258042431895059 := by
  unfold tailWord_5355598
  simp only [CollatzResearch.WordTrace]
  refine ⟨24416838306448823020430431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130223137634393722775628965 24416838306448823020430431)
  ·
    refine ⟨36625257459673234530645647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24416838306448823020430431 36625257459673234530645647)
    ·
      refine ⟨54937886189509851795968471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36625257459673234530645647 54937886189509851795968471)
      ·
        refine ⟨82406829284264777693952707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54937886189509851795968471 82406829284264777693952707)
        ·
          refine ⟨123610243926397166540929061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82406829284264777693952707 123610243926397166540929061)
          ·
            refine ⟨23176920736199468726424199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123610243926397166540929061 23176920736199468726424199)
            ·
              refine ⟨34765381104299203089636299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23176920736199468726424199 34765381104299203089636299)
              ·
                refine ⟨52148071656448804634454449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34765381104299203089636299 52148071656448804634454449)
                ·
                  refine ⟨39111053742336603475840837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52148071656448804634454449 39111053742336603475840837)
                  ·
                    refine ⟨7333322576688113151720157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39111053742336603475840837 7333322576688113151720157)
                    ·
                      refine ⟨2749995966258042431895059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333322576688113151720157 2749995966258042431895059)
                      ·
                        rfl

theorem cell23_5355598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_5355598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355598 prefixEnd_5355598 := by exact prefixLift 5355598
  have htrace : WordTrace (prefixWord ++ tailWord_5355598) baseStart_5355598 baseEnd_5355598 := by
    simpa [prefixWord, tailWord_5355598, baseEnd_5355598] using wordTrace_append hprefix tailTrace_5355598
  have hstable : (prefixWord ++ tailWord_5355598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355598).length < 2 ^ (prefixWord ++ tailWord_5355598).sum := by decide
  have hdescent : baseEnd_5355598 < baseStart_5355598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355601 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 7]
def baseStart_5355601 : Nat := 118140960795 + 5355601 * 2 ^ 59
def prefixEnd_5355601 : Nat := 4983230072969 + 3 ^ 40 * 5355601 * 2
def baseEnd_5355601 : Nat := 305555278522222880017505

theorem tailTrace_5355601 : CollatzResearch.WordTrace tailWord_5355601 prefixEnd_5355601 305555278522222880017505 := by
  unfold tailWord_5355601
  simp only [CollatzResearch.WordTrace]
  refine ⟨195334815870579715675802657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130223210580386477117201771 195334815870579715675802657)
  ·
    refine ⟨146501111902934786756851993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195334815870579715675802657 146501111902934786756851993)
    ·
      refine ⟨109875833927201090067638995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146501111902934786756851993 109875833927201090067638995)
      ·
        refine ⟨164813750890801635101458493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109875833927201090067638995 164813750890801635101458493)
        ·
          refine ⟨61805156584050613163046935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164813750890801635101458493 61805156584050613163046935)
          ·
            refine ⟨92707734876075919744570403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61805156584050613163046935 92707734876075919744570403)
            ·
              refine ⟨139061602314113879616855605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92707734876075919744570403 139061602314113879616855605)
              ·
                refine ⟨13037025216948176214080213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139061602314113879616855605 13037025216948176214080213)
                ·
                  refine ⟨305555278522222880017505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13037025216948176214080213 305555278522222880017505)
                  ·
                    rfl

theorem cell23_5355601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_5355601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355601 prefixEnd_5355601 := by exact prefixLift 5355601
  have htrace : WordTrace (prefixWord ++ tailWord_5355601) baseStart_5355601 baseEnd_5355601 := by
    simpa [prefixWord, tailWord_5355601, baseEnd_5355601] using wordTrace_append hprefix tailTrace_5355601
  have hstable : (prefixWord ++ tailWord_5355601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355601).length < 2 ^ (prefixWord ++ tailWord_5355601).sum := by decide
  have hdescent : baseEnd_5355601 < baseStart_5355601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355608 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5355608 : Nat := 118140960795 + 5355608 * 2 ^ 59
def prefixEnd_5355608 : Nat := 4983230072969 + 3 ^ 40 * 5355608 * 2
def baseEnd_5355608 : Nat := 2750001101064587392770013

theorem tailTrace_5355608 : CollatzResearch.WordTrace tailWord_5355608 prefixEnd_5355608 2750001101064587392770013 := by
  unfold tailWord_5355608
  simp only [CollatzResearch.WordTrace]
  refine ⟨97667535590777177935653739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130223380787702903914204985 97667535590777177935653739)
  ·
    refine ⟨146501303386165766903480609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97667535590777177935653739 146501303386165766903480609)
    ·
      refine ⟨109875977539624325177610457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146501303386165766903480609 109875977539624325177610457)
      ·
        refine ⟨82406983154718243883207843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109875977539624325177610457 82406983154718243883207843)
        ·
          refine ⟨123610474732077365824811765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82406983154718243883207843 123610474732077365824811765)
          ·
            refine ⟨11588482006132253046076103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123610474732077365824811765 11588482006132253046076103)
            ·
              refine ⟨17382723009198379569114155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11588482006132253046076103 17382723009198379569114155)
              ·
                refine ⟨26074084513797569353671233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17382723009198379569114155 26074084513797569353671233)
                ·
                  refine ⟨19555563385348177015253425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26074084513797569353671233 19555563385348177015253425)
                  ·
                    refine ⟨14666672539011132761440069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19555563385348177015253425 14666672539011132761440069)
                    ·
                      refine ⟨2750001101064587392770013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14666672539011132761440069 2750001101064587392770013)
                      ·
                        rfl

theorem cell23_5355608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5355608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355608 prefixEnd_5355608 := by exact prefixLift 5355608
  have htrace : WordTrace (prefixWord ++ tailWord_5355608) baseStart_5355608 baseEnd_5355608 := by
    simpa [prefixWord, tailWord_5355608, baseEnd_5355608] using wordTrace_append hprefix tailTrace_5355608
  have hstable : (prefixWord ++ tailWord_5355608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355608).length < 2 ^ (prefixWord ++ tailWord_5355608).sum := by decide
  have hdescent : baseEnd_5355608 < baseStart_5355608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355612 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5355612 : Nat := 118140960795 + 5355612 * 2 ^ 59
def prefixEnd_5355612 : Nat := 4983230072969 + 3 ^ 40 * 5355612 * 2
def baseEnd_5355612 : Nat := 2750003154987205377119995

theorem tailTrace_5355612 : CollatzResearch.WordTrace tailWord_5355612 prefixEnd_5355612 2750003154987205377119995 := by
  unfold tailWord_5355612
  simp only [CollatzResearch.WordTrace]
  refine ⟨97667608536769932277226545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130223478049026576369635393 97667608536769932277226545)
  ·
    refine ⟨73250706402577449207919909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97667608536769932277226545 73250706402577449207919909)
    ·
      refine ⟨13734507450483271726484983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73250706402577449207919909 13734507450483271726484983)
      ·
        refine ⟨20601761175724907589727475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13734507450483271726484983 20601761175724907589727475)
        ·
          refine ⟨30902641763587361384591213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20601761175724907589727475 30902641763587361384591213)
          ·
            refine ⟨11588490661345260519221705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30902641763587361384591213 11588490661345260519221705)
            ·
              refine ⟨8691367996008945389416279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11588490661345260519221705 8691367996008945389416279)
              ·
                refine ⟨13037051994013418084124419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691367996008945389416279 13037051994013418084124419)
                ·
                  refine ⟨19555577991020127126186629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13037051994013418084124419 19555577991020127126186629)
                  ·
                    refine ⟨3666670873316273836159993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19555577991020127126186629 3666670873316273836159993)
                    ·
                      refine ⟨2750003154987205377119995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666670873316273836159993 2750003154987205377119995)
                      ·
                        rfl

theorem cell23_5355612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5355612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355612 prefixEnd_5355612 := by exact prefixLift 5355612
  have htrace : WordTrace (prefixWord ++ tailWord_5355612) baseStart_5355612 baseEnd_5355612 := by
    simpa [prefixWord, tailWord_5355612, baseEnd_5355612] using wordTrace_append hprefix tailTrace_5355612
  have hstable : (prefixWord ++ tailWord_5355612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355612).length < 2 ^ (prefixWord ++ tailWord_5355612).sum := by decide
  have hdescent : baseEnd_5355612 < baseStart_5355612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355705 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5355705 : Nat := 118140960795 + 5355705 * 2 ^ 59
def prefixEnd_5355705 : Nat := 4983230072969 + 3 ^ 40 * 5355705 * 2
def baseEnd_5355705 : Nat := 2750050908688073513257067

theorem tailTrace_5355705 : CollatzResearch.WordTrace tailWord_5355705 prefixEnd_5355705 2750050908688073513257067 := by
  unfold tailWord_5355705
  simp only [CollatzResearch.WordTrace]
  refine ⟨195338609062202941437588569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130225739374801960958392379 195338609062202941437588569)
  ·
    refine ⟨146503956796652206078191427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195338609062202941437588569 146503956796652206078191427)
    ·
      refine ⟨219755935194978309117287141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146503956796652206078191427 219755935194978309117287141)
      ·
        refine ⟨41204237849058432959491339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219755935194978309117287141 41204237849058432959491339)
        ·
          refine ⟨61806356773587649439237009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41204237849058432959491339 61806356773587649439237009)
          ·
            refine ⟨46354767580190737079427757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61806356773587649439237009 46354767580190737079427757)
            ·
              refine ⟨17383037842571526404785409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46354767580190737079427757 17383037842571526404785409)
              ·
                refine ⟨13037278381928644803589057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17383037842571526404785409 13037278381928644803589057)
                ·
                  refine ⟨9777958786446483602691793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13037278381928644803589057 9777958786446483602691793)
                  ·
                    refine ⟨7333469089834862702018845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9777958786446483602691793 7333469089834862702018845)
                    ·
                      refine ⟨2750050908688073513257067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333469089834862702018845 2750050908688073513257067)
                      ·
                        rfl

theorem cell23_5355705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5355705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355705 prefixEnd_5355705 := by exact prefixLift 5355705
  have htrace : WordTrace (prefixWord ++ tailWord_5355705) baseStart_5355705 baseEnd_5355705 := by
    simpa [prefixWord, tailWord_5355705, baseEnd_5355705] using wordTrace_append hprefix tailTrace_5355705
  have hstable : (prefixWord ++ tailWord_5355705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355705).length < 2 ^ (prefixWord ++ tailWord_5355705).sum := by decide
  have hdescent : baseEnd_5355705 < baseStart_5355705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355712 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_5355712 : Nat := 118140960795 + 5355712 * 2 ^ 59
def prefixEnd_5355712 : Nat := 4983230072969 + 3 ^ 40 * 5355712 * 2
def baseEnd_5355712 : Nat := 916684834350884995289845

theorem tailTrace_5355712 : CollatzResearch.WordTrace tailWord_5355712 prefixEnd_5355712 916684834350884995289845 := by
  unfold tailWord_5355712
  simp only [CollatzResearch.WordTrace]
  refine ⟨97669432186588790816546695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130225909582118387755395593 97669432186588790816546695)
  ·
    refine ⟨146504148279883186224820043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97669432186588790816546695 146504148279883186224820043)
    ·
      refine ⟨219756222419824779337230065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146504148279883186224820043 219756222419824779337230065)
      ·
        refine ⟨164817166814868584502922549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219756222419824779337230065 164817166814868584502922549)
        ·
          refine ⟨15451609388893929797148989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164817166814868584502922549 15451609388893929797148989)
          ·
            refine ⟨5794353520835223673930871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15451609388893929797148989 5794353520835223673930871)
            ·
              refine ⟨8691530281252835510896307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794353520835223673930871 8691530281252835510896307)
              ·
                refine ⟨13037295421879253266344461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691530281252835510896307 13037295421879253266344461)
                ·
                  refine ⟨4888985783204719974879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13037295421879253266344461 4888985783204719974879173)
                  ·
                    refine ⟨916684834350884995289845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4888985783204719974879173 916684834350884995289845)
                    ·
                      rfl

theorem cell23_5355712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_5355712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355712 prefixEnd_5355712 := by exact prefixLift 5355712
  have htrace : WordTrace (prefixWord ++ tailWord_5355712) baseStart_5355712 baseEnd_5355712 := by
    simpa [prefixWord, tailWord_5355712, baseEnd_5355712] using wordTrace_append hprefix tailTrace_5355712
  have hstable : (prefixWord ++ tailWord_5355712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355712).length < 2 ^ (prefixWord ++ tailWord_5355712).sum := by decide
  have hdescent : baseEnd_5355712 < baseStart_5355712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355735 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_5355735 : Nat := 118140960795 + 5355735 * 2 ^ 59
def prefixEnd_5355735 : Nat := 4983230072969 + 3 ^ 40 * 5355735 * 2
def baseEnd_5355735 : Nat := 2750066313107708395881929

theorem tailTrace_5355735 : CollatzResearch.WordTrace tailWord_5355735 prefixEnd_5355735 2750066313107708395881929 := by
  unfold tailWord_5355735
  simp only [CollatzResearch.WordTrace]
  refine ⟨195339703252094256561180659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130226468834729504374120439 195339703252094256561180659)
  ·
    refine ⟨293009554878141384841770989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195339703252094256561180659 293009554878141384841770989)
    ·
      refine ⟨109878583079303019315664121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293009554878141384841770989 109878583079303019315664121)
      ·
        refine ⟨82408937309477264486748091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109878583079303019315664121 82408937309477264486748091)
        ·
          refine ⟨123613405964215896730122137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82408937309477264486748091 123613405964215896730122137)
          ·
            refine ⟨92710054473161922547591603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123613405964215896730122137 92710054473161922547591603)
            ·
              refine ⟨139065081709742883821387405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92710054473161922547591603 139065081709742883821387405)
              ·
                refine ⟨52149405641153581433020277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139065081709742883821387405 52149405641153581433020277)
                ·
                  refine ⟨4889006778858148259345651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52149405641153581433020277 4889006778858148259345651)
                  ·
                    refine ⟨7333510168287222389018477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889006778858148259345651 7333510168287222389018477)
                    ·
                      refine ⟨2750066313107708395881929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333510168287222389018477 2750066313107708395881929)
                      ·
                        rfl

theorem cell23_5355735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_5355735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355735 prefixEnd_5355735 := by exact prefixLift 5355735
  have htrace : WordTrace (prefixWord ++ tailWord_5355735) baseStart_5355735 baseEnd_5355735 := by
    simpa [prefixWord, tailWord_5355735, baseEnd_5355735] using wordTrace_append hprefix tailTrace_5355735
  have hstable : (prefixWord ++ tailWord_5355735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355735).length < 2 ^ (prefixWord ++ tailWord_5355735).sum := by decide
  have hdescent : baseEnd_5355735 < baseStart_5355735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355785 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_5355785 : Nat := 118140960795 + 5355785 * 2 ^ 59
def prefixEnd_5355785 : Nat := 4983230072969 + 3 ^ 40 * 5355785 * 2
def baseEnd_5355785 : Nat := 916697329046811066752233

theorem tailTrace_5355785 : CollatzResearch.WordTrace tailWord_5355785 prefixEnd_5355785 916697329046811066752233 := by
  unfold tailWord_5355785
  simp only [CollatzResearch.WordTrace]
  refine ⟨195341526901913115100500809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130227684601275410067000539 195341526901913115100500809)
  ·
    refine ⟨146506145176434836325375607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195341526901913115100500809 146506145176434836325375607)
    ·
      refine ⟨219759217764652254488063411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146506145176434836325375607 219759217764652254488063411)
      ·
        refine ⟨329638826646978381732095117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219759217764652254488063411 329638826646978381732095117)
        ·
          refine ⟨123614559992616893149535669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329638826646978381732095117 123614559992616893149535669)
          ·
            refine ⟨11588864999307833732768969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123614559992616893149535669 11588864999307833732768969)
            ·
              refine ⟨8691648749480875299576727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11588864999307833732768969 8691648749480875299576727)
              ·
                refine ⟨13037473124221312949365091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691648749480875299576727 13037473124221312949365091)
                ·
                  refine ⟨19556209686331969424047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13037473124221312949365091 19556209686331969424047637)
                  ·
                    refine ⟨916697329046811066752233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19556209686331969424047637 916697329046811066752233)
                    ·
                      rfl

theorem cell23_5355785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_5355785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355785 prefixEnd_5355785 := by exact prefixLift 5355785
  have htrace : WordTrace (prefixWord ++ tailWord_5355785) baseStart_5355785 baseEnd_5355785 := by
    simpa [prefixWord, tailWord_5355785, baseEnd_5355785] using wordTrace_append hprefix tailTrace_5355785
  have hstable : (prefixWord ++ tailWord_5355785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355785).length < 2 ^ (prefixWord ++ tailWord_5355785).sum := by decide
  have hdescent : baseEnd_5355785 < baseStart_5355785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355806 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5355806 : Nat := 118140960795 + 5355806 * 2 ^ 59
def prefixEnd_5355806 : Nat := 4983230072969 + 3 ^ 40 * 5355806 * 2
def baseEnd_5355806 : Nat := 916700923411392539364701

theorem tailTrace_5355806 : CollatzResearch.WordTrace tailWord_5355806 prefixEnd_5355806 916700923411392539364701 := by
  unfold tailWord_5355806
  simp only [CollatzResearch.WordTrace]
  refine ⟨24417786604354629460876909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130228195223224690458010181 24417786604354629460876909)
  ·
    refine ⟨9156669976632986047828841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24417786604354629460876909 9156669976632986047828841)
    ·
      refine ⟨6867502482474739535871631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9156669976632986047828841 6867502482474739535871631)
      ·
        refine ⟨10301253723712109303807447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867502482474739535871631 10301253723712109303807447)
        ·
          refine ⟨15451880585568163955711171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10301253723712109303807447 15451880585568163955711171)
          ·
            refine ⟨23177820878352245933566757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15451880585568163955711171 23177820878352245933566757)
            ·
              refine ⟨4345841414691046112543767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23177820878352245933566757 4345841414691046112543767)
              ·
                refine ⟨6518762122036569168815651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345841414691046112543767 6518762122036569168815651)
                ·
                  refine ⟨9778143183054853753223477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6518762122036569168815651 9778143183054853753223477)
                  ·
                    refine ⟨916700923411392539364701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9778143183054853753223477 916700923411392539364701)
                    ·
                      rfl

theorem cell23_5355806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5355806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355806 prefixEnd_5355806 := by exact prefixLift 5355806
  have htrace : WordTrace (prefixWord ++ tailWord_5355806) baseStart_5355806 baseEnd_5355806 := by
    simpa [prefixWord, tailWord_5355806, baseEnd_5355806] using wordTrace_append hprefix tailTrace_5355806
  have hstable : (prefixWord ++ tailWord_5355806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355806).length < 2 ^ (prefixWord ++ tailWord_5355806).sum := by decide
  have hdescent : baseEnd_5355806 < baseStart_5355806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355826 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_5355826 : Nat := 118140960795 + 5355826 * 2 ^ 59
def prefixEnd_5355826 : Nat := 4983230072969 + 3 ^ 40 * 5355826 * 2
def baseEnd_5355826 : Nat := 2750113039847267539844011

theorem tailTrace_5355826 : CollatzResearch.WordTrace tailWord_5355826 prefixEnd_5355826 2750113039847267539844011 := by
  unfold tailWord_5355826
  simp only [CollatzResearch.WordTrace]
  refine ⟨48835755573691144775685833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130228681529843052735162221 48835755573691144775685833)
  ·
    refine ⟨36626816680268358581764375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48835755573691144775685833 36626816680268358581764375)
    ·
      refine ⟨54940225020402537872646563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36626816680268358581764375 54940225020402537872646563)
      ·
        refine ⟨82410337530603806808969845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54940225020402537872646563 82410337530603806808969845)
        ·
          refine ⟨7725969143494106888340923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82410337530603806808969845 7725969143494106888340923)
          ·
            refine ⟨11588953715241160332511385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725969143494106888340923 11588953715241160332511385)
            ·
              refine ⟨8691715286430870249383539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11588953715241160332511385 8691715286430870249383539)
              ·
                refine ⟨13037572929646305374075309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691715286430870249383539 13037572929646305374075309)
                ·
                  refine ⟨4889089848617364515278241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13037572929646305374075309 4889089848617364515278241)
                  ·
                    refine ⟨3666817386463023386458681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4889089848617364515278241 3666817386463023386458681)
                    ·
                      refine ⟨2750113039847267539844011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666817386463023386458681 2750113039847267539844011)
                      ·
                        rfl

theorem cell23_5355826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_5355826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355826 prefixEnd_5355826 := by exact prefixLift 5355826
  have htrace : WordTrace (prefixWord ++ tailWord_5355826) baseStart_5355826 baseEnd_5355826 := by
    simpa [prefixWord, tailWord_5355826, baseEnd_5355826] using wordTrace_append hprefix tailTrace_5355826
  have hstable : (prefixWord ++ tailWord_5355826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355826).length < 2 ^ (prefixWord ++ tailWord_5355826).sum := by decide
  have hdescent : baseEnd_5355826 < baseStart_5355826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355885 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5355885 : Nat := 118140960795 + 5355885 * 2 ^ 59
def prefixEnd_5355885 : Nat := 4983230072969 + 3 ^ 40 * 5355885 * 2
def baseEnd_5355885 : Nat := 2750143335205882809006239

theorem tailTrace_5355885 : CollatzResearch.WordTrace tailWord_5355885 prefixEnd_5355885 2750143335205882809006239 := by
  unfold tailWord_5355885
  simp only [CollatzResearch.WordTrace]
  refine ⟨195345174201550832179141109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130230116134367221452760739 195345174201550832179141109)
  ·
    refine ⟨18313610081395390516794479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195345174201550832179141109 18313610081395390516794479)
    ·
      refine ⟨27470415122093085775191719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18313610081395390516794479 27470415122093085775191719)
      ·
        refine ⟨41205622683139628662787579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27470415122093085775191719 41205622683139628662787579)
        ·
          refine ⟨61808434024709442994181369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41205622683139628662787579 61808434024709442994181369)
          ·
            refine ⟨46356325518532082245636027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61808434024709442994181369 46356325518532082245636027)
            ·
              refine ⟨69534488277798123368454041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46356325518532082245636027 69534488277798123368454041)
              ·
                refine ⟨52150866208348592526340531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69534488277798123368454041 52150866208348592526340531)
                ·
                  refine ⟨78226299312522888789510797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52150866208348592526340531 78226299312522888789510797)
                  ·
                    refine ⟨29334862242196083296066549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78226299312522888789510797 29334862242196083296066549)
                    ·
                      refine ⟨2750143335205882809006239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29334862242196083296066549 2750143335205882809006239)
                      ·
                        rfl

theorem cell23_5355885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5355885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355885 prefixEnd_5355885 := by exact prefixLift 5355885
  have htrace : WordTrace (prefixWord ++ tailWord_5355885) baseStart_5355885 baseEnd_5355885 := by
    simpa [prefixWord, tailWord_5355885, baseEnd_5355885] using wordTrace_append hprefix tailTrace_5355885
  have hstable : (prefixWord ++ tailWord_5355885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355885).length < 2 ^ (prefixWord ++ tailWord_5355885).sum := by decide
  have hdescent : baseEnd_5355885 < baseStart_5355885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355893 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5355893 : Nat := 118140960795 + 5355893 * 2 ^ 59
def prefixEnd_5355893 : Nat := 4983230072969 + 3 ^ 40 * 5355893 * 2
def baseEnd_5355893 : Nat := 2750147443051118777706203

theorem tailTrace_5355893 : CollatzResearch.WordTrace tailWord_5355893 prefixEnd_5355893 2750147443051118777706203 := by
  unfold tailWord_5355893
  simp only [CollatzResearch.WordTrace]
  refine ⟨195345465985521849545432333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130230310657014566363621555 195345465985521849545432333)
  ·
    refine ⟨73254549744570693579537125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195345465985521849545432333 73254549744570693579537125)
    ·
      refine ⟨13735228077107005046163211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73254549744570693579537125 13735228077107005046163211)
      ·
        refine ⟨20602842115660507569244817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13735228077107005046163211 20602842115660507569244817)
        ·
          refine ⟨15452131586745380676933613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20602842115660507569244817 15452131586745380676933613)
          ·
            refine ⟨5794549345029517753850105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15452131586745380676933613 5794549345029517753850105)
            ·
              refine ⟨4345912008772138315387579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5794549345029517753850105 4345912008772138315387579)
              ·
                refine ⟨6518868013158207473081369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345912008772138315387579 6518868013158207473081369)
                ·
                  refine ⟨4889151009868655604811027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518868013158207473081369 4889151009868655604811027)
                  ·
                    refine ⟨7333726514802983407216541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889151009868655604811027 7333726514802983407216541)
                    ·
                      refine ⟨2750147443051118777706203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333726514802983407216541 2750147443051118777706203)
                      ·
                        rfl

theorem cell23_5355893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5355893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355893 prefixEnd_5355893 := by exact prefixLift 5355893
  have htrace : WordTrace (prefixWord ++ tailWord_5355893) baseStart_5355893 baseEnd_5355893 := by
    simpa [prefixWord, tailWord_5355893, baseEnd_5355893] using wordTrace_append hprefix tailTrace_5355893
  have hstable : (prefixWord ++ tailWord_5355893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355893).length < 2 ^ (prefixWord ++ tailWord_5355893).sum := by decide
  have hdescent : baseEnd_5355893 < baseStart_5355893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355933 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_5355933 : Nat := 118140960795 + 5355933 * 2 ^ 59
def prefixEnd_5355933 : Nat := 4983230072969 + 3 ^ 40 * 5355933 * 2
def baseEnd_5355933 : Nat := 2750167982277298621206019

theorem tailTrace_5355933 : CollatzResearch.WordTrace tailWord_5355933 prefixEnd_5355933 2750167982277298621206019 := by
  unfold tailWord_5355933
  simp only [CollatzResearch.WordTrace]
  refine ⟨195346924905376936376888453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130231283270251290917925635 195346924905376936376888453)
  ·
    refine ⟨36627548419758175570666585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195346924905376936376888453 36627548419758175570666585)
    ·
      refine ⟨27470661314818631677999939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36627548419758175570666585 27470661314818631677999939)
      ·
        refine ⟨41205991972227947516999909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27470661314818631677999939 41205991972227947516999909)
        ·
          refine ⟨7726123494792740159437483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41205991972227947516999909 7726123494792740159437483)
          ·
            refine ⟨11589185242189110239156225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726123494792740159437483 11589185242189110239156225)
            ·
              refine ⟨8691888931641832679367169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11589185242189110239156225 8691888931641832679367169)
              ·
                refine ⟨6518916698731374509525377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8691888931641832679367169 6518916698731374509525377)
                ·
                  refine ⟨4889187524048530882144033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6518916698731374509525377 4889187524048530882144033)
                  ·
                    refine ⟨3666890643036398161608025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4889187524048530882144033 3666890643036398161608025)
                    ·
                      refine ⟨2750167982277298621206019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666890643036398161608025 2750167982277298621206019)
                      ·
                        rfl

theorem cell23_5355933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_5355933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355933 prefixEnd_5355933 := by exact prefixLift 5355933
  have htrace : WordTrace (prefixWord ++ tailWord_5355933) baseStart_5355933 baseEnd_5355933 := by
    simpa [prefixWord, tailWord_5355933, baseEnd_5355933] using wordTrace_append hprefix tailTrace_5355933
  have hstable : (prefixWord ++ tailWord_5355933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355933).length < 2 ^ (prefixWord ++ tailWord_5355933).sum := by decide
  have hdescent : baseEnd_5355933 < baseStart_5355933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355939 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 5]
def baseStart_5355939 : Nat := 118140960795 + 5355939 * 2 ^ 59
def prefixEnd_5355939 : Nat := 4983230072969 + 3 ^ 40 * 5355939 * 2
def baseEnd_5355939 : Nat := 305574562573469510858999

theorem tailTrace_5355939 : CollatzResearch.WordTrace tailWord_5355939 prefixEnd_5355939 305574562573469510858999 := by
  unfold tailWord_5355939
  simp only [CollatzResearch.WordTrace]
  refine ⟨195347143743355199401606871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130231429162236799601071247 195347143743355199401606871)
  ·
    refine ⟨293020715615032799102410307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195347143743355199401606871 293020715615032799102410307)
    ·
      refine ⟨439531073422549198653615461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293020715615032799102410307 439531073422549198653615461)
      ·
        refine ⟨82412076266727974747552899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 439531073422549198653615461 82412076266727974747552899)
        ·
          refine ⟨123618114400091962121329349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82412076266727974747552899 123618114400091962121329349)
          ·
            refine ⟨23178396450017242897749253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123618114400091962121329349 23178396450017242897749253)
            ·
              refine ⟨4345949334378233043327985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23178396450017242897749253 4345949334378233043327985)
              ·
                refine ⟨3259462000783674782495989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4345949334378233043327985 3259462000783674782495989)
                ·
                  refine ⟨305574562573469510858999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259462000783674782495989 305574562573469510858999)
                  ·
                    rfl

theorem cell23_5355939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 5].length) (baseStart_5355939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355939 prefixEnd_5355939 := by exact prefixLift 5355939
  have htrace : WordTrace (prefixWord ++ tailWord_5355939) baseStart_5355939 baseEnd_5355939 := by
    simpa [prefixWord, tailWord_5355939, baseEnd_5355939] using wordTrace_append hprefix tailTrace_5355939
  have hstable : (prefixWord ++ tailWord_5355939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355939).length < 2 ^ (prefixWord ++ tailWord_5355939).sum := by decide
  have hdescent : baseEnd_5355939 < baseStart_5355939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355956 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5355956 : Nat := 118140960795 + 5355956 * 2 ^ 59
def prefixEnd_5355956 : Nat := 4983230072969 + 3 ^ 40 * 5355956 * 2
def baseEnd_5355956 : Nat := 305575532481372447913157

theorem tailTrace_5355956 : CollatzResearch.WordTrace tailWord_5355956 prefixEnd_5355956 305575532481372447913157 := by
  unfold tailWord_5355956
  simp only [CollatzResearch.WordTrace]
  refine ⟨97673881892146805652487861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130231842522862407536650481 97673881892146805652487861)
  ·
    refine ⟨9156926427388763029920737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97673881892146805652487861 9156926427388763029920737)
    ·
      refine ⟨6867694820541572272440553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9156926427388763029920737 6867694820541572272440553)
      ·
        refine ⟨5150771115406179204330415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6867694820541572272440553 5150771115406179204330415)
        ·
          refine ⟨7726156673109268806495623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150771115406179204330415 7726156673109268806495623)
          ·
            refine ⟨11589235009663903209743435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726156673109268806495623 11589235009663903209743435)
            ·
              refine ⟨17383852514495854814615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11589235009663903209743435 17383852514495854814615153)
              ·
                refine ⟨13037889385871891110961365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17383852514495854814615153 13037889385871891110961365)
                ·
                  refine ⟨305575532481372447913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13037889385871891110961365 305575532481372447913157)
                  ·
                    rfl

theorem cell23_5355956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5355956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355956 prefixEnd_5355956 := by exact prefixLift 5355956
  have htrace : WordTrace (prefixWord ++ tailWord_5355956) baseStart_5355956 baseEnd_5355956 := by
    simpa [prefixWord, tailWord_5355956, baseEnd_5355956] using wordTrace_append hprefix tailTrace_5355956
  have hstable : (prefixWord ++ tailWord_5355956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355956).length < 2 ^ (prefixWord ++ tailWord_5355956).sum := by decide
  have hdescent : baseEnd_5355956 < baseStart_5355956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355982 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_5355982 : Nat := 118140960795 + 5355982 * 2 ^ 59
def prefixEnd_5355982 : Nat := 4983230072969 + 3 ^ 40 * 5355982 * 2
def baseEnd_5355982 : Nat := 916731047609789643164431

theorem tailTrace_5355982 : CollatzResearch.WordTrace tailWord_5355982 prefixEnd_5355982 916731047609789643164431 := by
  unfold tailWord_5355982
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418589010274927218177775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130232474721466278496948133 24418589010274927218177775)
  ·
    refine ⟨36627883515412390827266663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24418589010274927218177775 36627883515412390827266663)
    ·
      refine ⟨54941825273118586240899995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36627883515412390827266663 54941825273118586240899995)
      ·
        refine ⟨82412737909677879361349993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54941825273118586240899995 82412737909677879361349993)
        ·
          refine ⟨61809553432258409521012495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82412737909677879361349993 61809553432258409521012495)
          ·
            refine ⟨92714330148387614281518743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61809553432258409521012495 92714330148387614281518743)
            ·
              refine ⟨139071495222581421422278115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92714330148387614281518743 139071495222581421422278115)
              ·
                refine ⟨208607242833872132133417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139071495222581421422278115 208607242833872132133417173)
                ·
                  refine ⟨4889232253918878096876965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 208607242833872132133417173 4889232253918878096876965)
                  ·
                    refine ⟨916731047609789643164431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889232253918878096876965 916731047609789643164431)
                    ·
                      rfl

theorem cell23_5355982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_5355982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355982 prefixEnd_5355982 := by exact prefixLift 5355982
  have htrace : WordTrace (prefixWord ++ tailWord_5355982) baseStart_5355982 baseEnd_5355982 := by
    simpa [prefixWord, tailWord_5355982, baseEnd_5355982] using wordTrace_append hprefix tailTrace_5355982
  have hstable : (prefixWord ++ tailWord_5355982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355982).length < 2 ^ (prefixWord ++ tailWord_5355982).sum := by decide
  have hdescent : baseEnd_5355982 < baseStart_5355982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355985 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_5355985 : Nat := 118140960795 + 5355985 * 2 ^ 59
def prefixEnd_5355985 : Nat := 4983230072969 + 3 ^ 40 * 5355985 * 2
def baseEnd_5355985 : Nat := 2750194683271332417755779

theorem tailTrace_5355985 : CollatzResearch.WordTrace tailWord_5355985 prefixEnd_5355985 2750194683271332417755779 := by
  unfold tailWord_5355985
  simp only [CollatzResearch.WordTrace]
  refine ⟨195348821501188549257781409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130232547667459032838520939 195348821501188549257781409)
  ·
    refine ⟨146511616125891411943336057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195348821501188549257781409 146511616125891411943336057)
    ·
      refine ⟨109883712094418558957502043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146511616125891411943336057 109883712094418558957502043)
      ·
        refine ⟨164825568141627838436253065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109883712094418558957502043 164825568141627838436253065)
        ·
          refine ⟨123619176106220878827189799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164825568141627838436253065 123619176106220878827189799)
          ·
            refine ⟨185428764159331318240784699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123619176106220878827189799 185428764159331318240784699)
            ·
              refine ⟨278143146238996977361177049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185428764159331318240784699 278143146238996977361177049)
              ·
                refine ⟨208607359679247733020882787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278143146238996977361177049 208607359679247733020882787)
                ·
                  refine ⟨312911039518871599531324181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208607359679247733020882787 312911039518871599531324181)
                  ·
                    refine ⟨14667704977447106228030821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 312911039518871599531324181 14667704977447106228030821)
                    ·
                      refine ⟨2750194683271332417755779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14667704977447106228030821 2750194683271332417755779)
                      ·
                        rfl

theorem cell23_5355985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_5355985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355985 prefixEnd_5355985 := by exact prefixLift 5355985
  have htrace : WordTrace (prefixWord ++ tailWord_5355985) baseStart_5355985 baseEnd_5355985 := by
    simpa [prefixWord, tailWord_5355985, baseEnd_5355985] using wordTrace_append hprefix tailTrace_5355985
  have hstable : (prefixWord ++ tailWord_5355985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355985).length < 2 ^ (prefixWord ++ tailWord_5355985).sum := by decide
  have hdescent : baseEnd_5355985 < baseStart_5355985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355989 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5355989 : Nat := 118140960795 + 5355989 * 2 ^ 59
def prefixEnd_5355989 : Nat := 4983230072969 + 3 ^ 40 * 5355989 * 2
def baseEnd_5355989 : Nat := 2750196737193950402105761

theorem tailTrace_5355989 : CollatzResearch.WordTrace tailWord_5355989 prefixEnd_5355989 2750196737193950402105761 := by
  unfold tailWord_5355989
  simp only [CollatzResearch.WordTrace]
  refine ⟨195348967393174057940927021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130232644928782705293951347 195348967393174057940927021)
  ·
    refine ⟨73255862772440271727847633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195348967393174057940927021 73255862772440271727847633)
    ·
      refine ⟨54941897079330203795885725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73255862772440271727847633 54941897079330203795885725)
      ·
        refine ⟨20603211404748826423457147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54941897079330203795885725 20603211404748826423457147)
        ·
          refine ⟨30904817107123239635185721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20603211404748826423457147 30904817107123239635185721)
          ·
            refine ⟨23178612830342429726389291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30904817107123239635185721 23178612830342429726389291)
            ·
              refine ⟨34767919245513644589583937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23178612830342429726389291 34767919245513644589583937)
              ·
                refine ⟨26075939434135233442187953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34767919245513644589583937 26075939434135233442187953)
                ·
                  refine ⟨19556954575601425081640965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26075939434135233442187953 19556954575601425081640965)
                  ·
                    refine ⟨3666928982925267202807681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19556954575601425081640965 3666928982925267202807681)
                    ·
                      refine ⟨2750196737193950402105761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3666928982925267202807681 2750196737193950402105761)
                      ·
                        rfl

theorem cell23_5355989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5355989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355989 prefixEnd_5355989 := by exact prefixLift 5355989
  have htrace : WordTrace (prefixWord ++ tailWord_5355989) baseStart_5355989 baseEnd_5355989 := by
    simpa [prefixWord, tailWord_5355989, baseEnd_5355989] using wordTrace_append hprefix tailTrace_5355989
  have hstable : (prefixWord ++ tailWord_5355989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355989).length < 2 ^ (prefixWord ++ tailWord_5355989).sum := by decide
  have hdescent : baseEnd_5355989 < baseStart_5355989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355992 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_5355992 : Nat := 118140960795 + 5355992 * 2 ^ 59
def prefixEnd_5355992 : Nat := 4983230072969 + 3 ^ 40 * 5355992 * 2
def baseEnd_5355992 : Nat := 2750198277635913890368247

theorem tailTrace_5355992 : CollatzResearch.WordTrace tailWord_5355992 prefixEnd_5355992 2750198277635913890368247 := by
  unfold tailWord_5355992
  simp only [CollatzResearch.WordTrace]
  refine ⟨97674538406081594726643115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130232717874775459635524153 97674538406081594726643115)
  ·
    refine ⟨146511807609122392089964673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97674538406081594726643115 146511807609122392089964673)
    ·
      refine ⟨109883855706841794067473505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146511807609122392089964673 109883855706841794067473505)
      ·
        refine ⟨82412891780131345550605129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109883855706841794067473505 82412891780131345550605129)
        ·
          refine ⟨61809668835098509162953847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82412891780131345550605129 61809668835098509162953847)
          ·
            refine ⟨92714503252647763744430771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61809668835098509162953847 92714503252647763744430771)
            ·
              refine ⟨139071754878971645616646157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92714503252647763744430771 139071754878971645616646157)
              ·
                refine ⟨52151908079614367106242309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139071754878971645616646157 52151908079614367106242309)
                ·
                  refine ⟨9778482764927693832420433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52151908079614367106242309 9778482764927693832420433)
                  ·
                    refine ⟨7333862073695770374315325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9778482764927693832420433 7333862073695770374315325)
                    ·
                      refine ⟨2750198277635913890368247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333862073695770374315325 2750198277635913890368247)
                      ·
                        rfl

theorem cell23_5355992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_5355992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355992 prefixEnd_5355992 := by exact prefixLift 5355992
  have htrace : WordTrace (prefixWord ++ tailWord_5355992) baseStart_5355992 baseEnd_5355992 := by
    simpa [prefixWord, tailWord_5355992, baseEnd_5355992] using wordTrace_append hprefix tailTrace_5355992
  have hstable : (prefixWord ++ tailWord_5355992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355992).length < 2 ^ (prefixWord ++ tailWord_5355992).sum := by decide
  have hdescent : baseEnd_5355992 < baseStart_5355992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5355999 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 3, 4]
def baseStart_5355999 : Nat := 118140960795 + 5355999 * 2 ^ 59
def prefixEnd_5355999 : Nat := 4983230072969 + 3 ^ 40 * 5355999 * 2
def baseEnd_5355999 : Nat := 916733957333498454326905

theorem tailTrace_5355999 : CollatzResearch.WordTrace tailWord_5355999 prefixEnd_5355999 916733957333498454326905 := by
  unfold tailWord_5355999
  simp only [CollatzResearch.WordTrace]
  refine ⟨195349332123137829648791051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130232888082091886432527367 195349332123137829648791051)
  ·
    refine ⟨293023998184706744473186577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195349332123137829648791051 293023998184706744473186577)
    ·
      refine ⟨219767998638530058354889933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293023998184706744473186577 219767998638530058354889933)
      ·
        refine ⟨82412999489448771883083725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219767998638530058354889933 82412999489448771883083725)
        ·
          refine ⟨30904874808543289456156397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82412999489448771883083725 30904874808543289456156397)
          ·
            refine ⟨11589328053203733546058649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30904874808543289456156397 11589328053203733546058649)
            ·
              refine ⟨8691996039902800159543987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11589328053203733546058649 8691996039902800159543987)
              ·
                refine ⟨13037994059854200239315981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8691996039902800159543987 13037994059854200239315981)
                ·
                  refine ⟨4889247772445325089743493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13037994059854200239315981 4889247772445325089743493)
                  ·
                    refine ⟨916733957333498454326905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889247772445325089743493 916733957333498454326905)
                    ·
                      rfl

theorem cell23_5355999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_5355999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5355999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5355999 prefixEnd_5355999 := by exact prefixLift 5355999
  have htrace : WordTrace (prefixWord ++ tailWord_5355999) baseStart_5355999 baseEnd_5355999 := by
    simpa [prefixWord, tailWord_5355999, baseEnd_5355999] using wordTrace_append hprefix tailTrace_5355999
  have hstable : (prefixWord ++ tailWord_5355999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5355999).length < 2 ^ (prefixWord ++ tailWord_5355999).sum := by decide
  have hdescent : baseEnd_5355999 < baseStart_5355999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5355999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356015 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_5356015 : Nat := 118140960795 + 5356015 * 2 ^ 59
def prefixEnd_5356015 : Nat := 4983230072969 + 3 ^ 40 * 5356015 * 2
def baseEnd_5356015 : Nat := 2750210087690967300380641

theorem tailTrace_5356015 : CollatzResearch.WordTrace tailWord_5356015 prefixEnd_5356015 2750210087690967300380641 := by
  unfold tailWord_5356015
  simp only [CollatzResearch.WordTrace]
  refine ⟨195349915691079864381373499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130233277127386576254248999 195349915691079864381373499)
  ·
    refine ⟨293024873536619796572060249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195349915691079864381373499 293024873536619796572060249)
    ·
      refine ⟨219768655152464847429045187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293024873536619796572060249 219768655152464847429045187)
      ·
        refine ⟨329652982728697271143567781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219768655152464847429045187 329652982728697271143567781)
        ·
          refine ⟨61809934261630738339418959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329652982728697271143567781 61809934261630738339418959)
          ·
            refine ⟨92714901392446107509128439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61809934261630738339418959 92714901392446107509128439)
            ·
              refine ⟨139072352088669161263692659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92714901392446107509128439 139072352088669161263692659)
              ·
                refine ⟨208608528133003741895538989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139072352088669161263692659 208608528133003741895538989)
                ·
                  refine ⟨78228198049876403210827121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208608528133003741895538989 78228198049876403210827121)
                  ·
                    refine ⟨58671148537407302408120341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78228198049876403210827121 58671148537407302408120341)
                    ·
                      refine ⟨2750210087690967300380641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58671148537407302408120341 2750210087690967300380641)
                      ·
                        rfl

theorem cell23_5356015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_5356015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356015 prefixEnd_5356015 := by exact prefixLift 5356015
  have htrace : WordTrace (prefixWord ++ tailWord_5356015) baseStart_5356015 baseEnd_5356015 := by
    simpa [prefixWord, tailWord_5356015, baseEnd_5356015] using wordTrace_append hprefix tailTrace_5356015
  have hstable : (prefixWord ++ tailWord_5356015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356015).length < 2 ^ (prefixWord ++ tailWord_5356015).sum := by decide
  have hdescent : baseEnd_5356015 < baseStart_5356015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356033 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5356033 : Nat := 118140960795 + 5356033 * 2 ^ 59
def prefixEnd_5356033 : Nat := 4983230072969 + 3 ^ 40 * 5356033 * 2
def baseEnd_5356033 : Nat := 916739776780916076651853

theorem tailTrace_5356033 : CollatzResearch.WordTrace tailWord_5356033 prefixEnd_5356033 916739776780916076651853 := by
  unfold tailWord_5356033
  simp only [CollatzResearch.WordTrace]
  refine ⟨195350572205014653455528753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130233714803343102303685835 195350572205014653455528753)
  ·
    refine ⟨146512929153760990091646565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195350572205014653455528753 146512929153760990091646565)
    ·
      refine ⟨27471174216330185642183731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146512929153760990091646565 27471174216330185642183731)
      ·
        refine ⟨41206761324495278463275597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27471174216330185642183731 41206761324495278463275597)
        ·
          refine ⟨15452535496685729423728349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41206761324495278463275597 15452535496685729423728349)
          ·
            refine ⟨5794700811257148533898131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15452535496685729423728349 5794700811257148533898131)
            ·
              refine ⟨8692051216885722800847197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794700811257148533898131 8692051216885722800847197)
              ·
                refine ⟨3259519206332146050317699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8692051216885722800847197 3259519206332146050317699)
                ·
                  refine ⟨4889278809498219075476549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259519206332146050317699 4889278809498219075476549)
                  ·
                    refine ⟨916739776780916076651853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889278809498219075476549 916739776780916076651853)
                    ·
                      rfl

theorem cell23_5356033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5356033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356033 prefixEnd_5356033 := by exact prefixLift 5356033
  have htrace : WordTrace (prefixWord ++ tailWord_5356033) baseStart_5356033 baseEnd_5356033 := by
    simpa [prefixWord, tailWord_5356033, baseEnd_5356033] using wordTrace_append hprefix tailTrace_5356033
  have hstable : (prefixWord ++ tailWord_5356033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356033).length < 2 ^ (prefixWord ++ tailWord_5356033).sum := by decide
  have hdescent : baseEnd_5356033 < baseStart_5356033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
