import V185TrunkScan22Chunk449

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4010502 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4010502 : Nat := 118140960795 + 4010502 * 2 ^ 59
def prefixEnd_4010502 : Nat := 4983230072969 + 3 ^ 40 * 4010502 * 2
def baseEnd_4010502 : Nat := 1372876794545315417454029

theorem tailTrace_4010502 : CollatzResearch.WordTrace tailWord_4010502 prefixEnd_4010502 1372876794545315417454029 := by
  unfold tailWord_4010502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571094528645114626747305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97516683277762445370609173 4571094528645114626747305)
  ·
    refine ⟨3428320896483835970060479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4571094528645114626747305 3428320896483835970060479)
    ·
      refine ⟨5142481344725753955090719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428320896483835970060479 5142481344725753955090719)
      ·
        refine ⟨7713722017088630932636079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142481344725753955090719 7713722017088630932636079)
        ·
          refine ⟨11570583025632946398954119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713722017088630932636079 11570583025632946398954119)
          ·
            refine ⟨17355874538449419598431179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11570583025632946398954119 17355874538449419598431179)
            ·
              refine ⟨26033811807674129397646769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17355874538449419598431179 26033811807674129397646769)
              ·
                refine ⟨19525358855755597048235077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26033811807674129397646769 19525358855755597048235077)
                ·
                  refine ⟨3661004785454174446544077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19525358855755597048235077 3661004785454174446544077)
                  ·
                    refine ⟨1372876794545315417454029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3661004785454174446544077 1372876794545315417454029)
                    ·
                      rfl

theorem cell22_4010502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4010502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010502 prefixEnd_4010502 := by exact prefixLift 4010502
  have htrace : WordTrace (prefixWord ++ tailWord_4010502) baseStart_4010502 baseEnd_4010502 := by
    simpa [prefixWord, tailWord_4010502, baseEnd_4010502] using wordTrace_append hprefix tailTrace_4010502
  have hstable : (prefixWord ++ tailWord_4010502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010502).length < 2 ^ (prefixWord ++ tailWord_4010502).sum := by decide
  have hdescent : baseEnd_4010502 < baseStart_4010502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010513 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 1, 3]
def baseStart_4010513 : Nat := 118140960795 + 4010513 * 2 ^ 59
def prefixEnd_4010513 : Nat := 4983230072969 + 3 ^ 40 * 4010513 * 2
def baseEnd_4010513 : Nat := 1372880560070115055428995

theorem tailTrace_4010513 : CollatzResearch.WordTrace tailWord_4010513 prefixEnd_4010513 1372880560070115055428995 := by
  unfold tailWord_4010513
  simp only [CollatzResearch.WordTrace]
  refine ⟨146275426119603816934564193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97516950746402544623042795 146275426119603816934564193)
  ·
    refine ⟨109706569589702862700923145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146275426119603816934564193 109706569589702862700923145)
    ·
      refine ⟨82279927192277147025692359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109706569589702862700923145 82279927192277147025692359)
      ·
        refine ⟨123419890788415720538538539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82279927192277147025692359 123419890788415720538538539)
        ·
          refine ⟨185129836182623580807807809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123419890788415720538538539 185129836182623580807807809)
          ·
            refine ⟨138847377136967685605855857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185129836182623580807807809 138847377136967685605855857)
            ·
              refine ⟨104135532852725764204391893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138847377136967685605855857 104135532852725764204391893)
              ·
                refine ⟨2440676551235760098540435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104135532852725764204391893 2440676551235760098540435)
                ·
                  refine ⟨3661014826853640147810653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440676551235760098540435 3661014826853640147810653)
                  ·
                    refine ⟨1372880560070115055428995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3661014826853640147810653 1372880560070115055428995)
                    ·
                      rfl

theorem cell22_4010513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_4010513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010513 prefixEnd_4010513 := by exact prefixLift 4010513
  have htrace : WordTrace (prefixWord ++ tailWord_4010513) baseStart_4010513 baseEnd_4010513 := by
    simpa [prefixWord, tailWord_4010513, baseEnd_4010513] using wordTrace_append hprefix tailTrace_4010513
  have hstable : (prefixWord ++ tailWord_4010513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010513).length < 2 ^ (prefixWord ++ tailWord_4010513).sum := by decide
  have hdescent : baseEnd_4010513 < baseStart_4010513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010725 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_4010725 : Nat := 118140960795 + 4010725 * 2 ^ 59
def prefixEnd_4010725 : Nat := 4983230072969 + 3 ^ 40 * 4010725 * 2
def baseEnd_4010725 : Nat := 1372953132002617169128345

theorem tailTrace_4010725 : CollatzResearch.WordTrace tailWord_4010725 prefixEnd_4010725 1372953132002617169128345 := by
  unfold tailWord_4010725
  simp only [CollatzResearch.WordTrace]
  refine ⟨146283158394835777141281629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97522105596557184760854419 146283158394835777141281629)
  ·
    refine ⟨54856184398063416427980611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146283158394835777141281629 54856184398063416427980611)
    ·
      refine ⟨82284276597095124641970917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54856184398063416427980611 82284276597095124641970917)
      ·
        refine ⟨15428301861955335870369547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82284276597095124641970917 15428301861955335870369547)
        ·
          refine ⟨23142452792933003805554321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428301861955335870369547 23142452792933003805554321)
          ·
            refine ⟨17356839594699752854165741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23142452792933003805554321 17356839594699752854165741)
            ·
              refine ⟨6508814848012407320312153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17356839594699752854165741 6508814848012407320312153)
              ·
                refine ⟨4881611136009305490234115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508814848012407320312153 4881611136009305490234115)
                ·
                  refine ⟨7322416704013958235351173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881611136009305490234115 7322416704013958235351173)
                  ·
                    refine ⟨1372953132002617169128345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322416704013958235351173 1372953132002617169128345)
                    ·
                      rfl

theorem cell22_4010725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_4010725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010725 prefixEnd_4010725 := by exact prefixLift 4010725
  have htrace : WordTrace (prefixWord ++ tailWord_4010725) baseStart_4010725 baseEnd_4010725 := by
    simpa [prefixWord, tailWord_4010725, baseEnd_4010725] using wordTrace_append hprefix tailTrace_4010725
  have hstable : (prefixWord ++ tailWord_4010725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010725).length < 2 ^ (prefixWord ++ tailWord_4010725).sum := by decide
  have hdescent : baseEnd_4010725 < baseStart_4010725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010738 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_4010738 : Nat := 118140960795 + 4010738 * 2 ^ 59
def prefixEnd_4010738 : Nat := 4983230072969 + 3 ^ 40 * 4010738 * 2
def baseEnd_4010738 : Nat := 1372957582168289468553305

theorem tailTrace_4010738 : CollatzResearch.WordTrace tailWord_4010738 prefixEnd_4010738 1372957582168289468553305 := by
  unfold tailWord_4010738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36570908135947170090376217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97522421695859120241003245 36570908135947170090376217)
  ·
    refine ⟨27428181101960377567782163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36570908135947170090376217 27428181101960377567782163)
    ·
      refine ⟨41142271652940566351673245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27428181101960377567782163 41142271652940566351673245)
      ·
        refine ⟨15428351869852712381877467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41142271652940566351673245 15428351869852712381877467)
        ·
          refine ⟨23142527804779068572816201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428351869852712381877467 23142527804779068572816201)
          ·
            refine ⟨17356895853584301429612151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23142527804779068572816201 17356895853584301429612151)
            ·
              refine ⟨26035343780376452144418227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17356895853584301429612151 26035343780376452144418227)
              ·
                refine ⟨39053015670564678216627341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26035343780376452144418227 39053015670564678216627341)
                ·
                  refine ⟨14644880876461754331235253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39053015670564678216627341 14644880876461754331235253)
                  ·
                    refine ⟨1372957582168289468553305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14644880876461754331235253 1372957582168289468553305)
                    ·
                      rfl

theorem cell22_4010738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_4010738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010738 prefixEnd_4010738 := by exact prefixLift 4010738
  have htrace : WordTrace (prefixWord ++ tailWord_4010738) baseStart_4010738 baseEnd_4010738 := by
    simpa [prefixWord, tailWord_4010738, baseEnd_4010738] using wordTrace_append hprefix tailTrace_4010738
  have hstable : (prefixWord ++ tailWord_4010738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010738).length < 2 ^ (prefixWord ++ tailWord_4010738).sum := by decide
  have hdescent : baseEnd_4010738 < baseStart_4010738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010742 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_4010742 : Nat := 118140960795 + 4010742 * 2 ^ 59
def prefixEnd_4010742 : Nat := 4983230072969 + 3 ^ 40 * 4010742 * 2
def baseEnd_4010742 : Nat := 1372958951450034791453293

theorem tailTrace_4010742 : CollatzResearch.WordTrace tailWord_4010742 prefixEnd_4010742 1372958951450034791453293 := by
  unfold tailWord_4010742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142736152235886815290655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97522518957182792696433653 9142736152235886815290655)
  ·
    refine ⟨13714104228353830222935983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9142736152235886815290655 13714104228353830222935983)
    ·
      refine ⟨20571156342530745334403975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13714104228353830222935983 20571156342530745334403975)
      ·
        refine ⟨30856734513796118001605963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20571156342530745334403975 30856734513796118001605963)
        ·
          refine ⟨46285101770694177002408945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30856734513796118001605963 46285101770694177002408945)
          ·
            refine ⟨34713826328020632751806709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46285101770694177002408945 34713826328020632751806709)
            ·
              refine ⟨3254421218251934320481879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34713826328020632751806709 3254421218251934320481879)
              ·
                refine ⟨4881631827377901480722819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254421218251934320481879 4881631827377901480722819)
                ·
                  refine ⟨7322447741066852221084229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881631827377901480722819 7322447741066852221084229)
                  ·
                    refine ⟨1372958951450034791453293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322447741066852221084229 1372958951450034791453293)
                    ·
                      rfl

theorem cell22_4010742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_4010742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010742 prefixEnd_4010742 := by exact prefixLift 4010742
  have htrace : WordTrace (prefixWord ++ tailWord_4010742) baseStart_4010742 baseEnd_4010742 := by
    simpa [prefixWord, tailWord_4010742, baseEnd_4010742] using wordTrace_append hprefix tailTrace_4010742
  have hstable : (prefixWord ++ tailWord_4010742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010742).length < 2 ^ (prefixWord ++ tailWord_4010742).sum := by decide
  have hdescent : baseEnd_4010742 < baseStart_4010742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010806 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4010806 : Nat := 118140960795 + 4010806 * 2 ^ 59
def prefixEnd_4010806 : Nat := 4983230072969 + 3 ^ 40 * 4010806 * 2
def baseEnd_4010806 : Nat := 1372980859957959957853097

theorem tailTrace_4010806 : CollatzResearch.WordTrace tailWord_4010806 prefixEnd_4010806 1372980859957959957853097 := by
  unfold tailWord_4010806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142882044221395498436267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97524075138361551983320181 9142882044221395498436267)
  ·
    refine ⟨13714323066332093247654401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9142882044221395498436267 13714323066332093247654401)
    ·
      refine ⟨10285742299749069935740801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13714323066332093247654401 10285742299749069935740801)
      ·
        refine ⟨7714306724811802451805601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10285742299749069935740801 7714306724811802451805601)
        ·
          refine ⟨5785730043608851838854201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7714306724811802451805601 5785730043608851838854201)
          ·
            refine ⟨4339297532706638879140651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5785730043608851838854201 4339297532706638879140651)
            ·
              refine ⟨6508946299059958318710977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339297532706638879140651 6508946299059958318710977)
              ·
                refine ⟨4881709724294968739033233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508946299059958318710977 4881709724294968739033233)
                ·
                  refine ⟨3661282293221226554274925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881709724294968739033233 3661282293221226554274925)
                  ·
                    refine ⟨1372980859957959957853097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3661282293221226554274925 1372980859957959957853097)
                    ·
                      rfl

theorem cell22_4010806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4010806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010806 prefixEnd_4010806 := by exact prefixLift 4010806
  have htrace : WordTrace (prefixWord ++ tailWord_4010806) baseStart_4010806 baseEnd_4010806 := by
    simpa [prefixWord, tailWord_4010806, baseEnd_4010806] using wordTrace_append hprefix tailTrace_4010806
  have hstable : (prefixWord ++ tailWord_4010806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010806).length < 2 ^ (prefixWord ++ tailWord_4010806).sum := by decide
  have hdescent : baseEnd_4010806 < baseStart_4010806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010860 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_4010860 : Nat := 118140960795 + 4010860 * 2 ^ 59
def prefixEnd_4010860 : Nat := 4983230072969 + 3 ^ 40 * 4010860 * 2
def baseEnd_4010860 : Nat := 1372999345261521817002931

theorem tailTrace_4010860 : CollatzResearch.WordTrace tailWord_4010860 prefixEnd_4010860 1372999345261521817002931 := by
  unfold tailWord_4010860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73144041124673347598723017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97525388166231130131630689 73144041124673347598723017)
  ·
    refine ⟨54858030843505010699042263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73144041124673347598723017 54858030843505010699042263)
    ·
      refine ⟨82287046265257516048563395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54858030843505010699042263 82287046265257516048563395)
      ·
        refine ⟨123430569397886274072845093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82287046265257516048563395 123430569397886274072845093)
        ·
          refine ⟨23143231762103676388658455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123430569397886274072845093 23143231762103676388658455)
          ·
            refine ⟨34714847643155514582987683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143231762103676388658455 34714847643155514582987683)
            ·
              refine ⟨52072271464733271874481525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34714847643155514582987683 52072271464733271874481525)
              ·
                refine ⟨4881775449818744238232643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52072271464733271874481525 4881775449818744238232643)
                ·
                  refine ⟨7322663174728116357348965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881775449818744238232643 7322663174728116357348965)
                  ·
                    refine ⟨1372999345261521817002931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322663174728116357348965 1372999345261521817002931)
                    ·
                      rfl

theorem cell22_4010860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_4010860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010860 prefixEnd_4010860 := by exact prefixLift 4010860
  have htrace : WordTrace (prefixWord ++ tailWord_4010860) baseStart_4010860 baseEnd_4010860 := by
    simpa [prefixWord, tailWord_4010860, baseEnd_4010860] using wordTrace_append hprefix tailTrace_4010860
  have hstable : (prefixWord ++ tailWord_4010860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010860).length < 2 ^ (prefixWord ++ tailWord_4010860).sum := by decide
  have hdescent : baseEnd_4010860 < baseStart_4010860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010875 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 4]
def baseStart_4010875 : Nat := 118140960795 + 4010875 * 2 ^ 59
def prefixEnd_4010875 : Nat := 4983230072969 + 3 ^ 40 * 4010875 * 2
def baseEnd_4010875 : Nat := 457668160022688925959295

theorem tailTrace_4010875 : CollatzResearch.WordTrace tailWord_4010875 prefixEnd_4010875 457668160022688925959295 := by
  unfold tailWord_4010875
  simp only [CollatzResearch.WordTrace]
  refine ⟨146288629344292352759242079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97525752896194901839494719 146288629344292352759242079)
  ·
    refine ⟨219432944016438529138863119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146288629344292352759242079 219432944016438529138863119)
    ·
      refine ⟨329149416024657793708294679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219432944016438529138863119 329149416024657793708294679)
      ·
        refine ⟨493724124036986690562442019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329149416024657793708294679 493724124036986690562442019)
        ·
          refine ⟨740586186055480035843663029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493724124036986690562442019 740586186055480035843663029)
          ·
            refine ⟨69429954942701253360343409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 740586186055480035843663029 69429954942701253360343409)
            ·
              refine ⟨52072466207025940020257557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69429954942701253360343409 52072466207025940020257557)
              ·
                refine ⟨2440896853454340938449573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52072466207025940020257557 2440896853454340938449573)
                ·
                  refine ⟨457668160022688925959295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440896853454340938449573 457668160022688925959295)
                  ·
                    rfl

theorem cell22_4010875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 4].length) (baseStart_4010875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010875 prefixEnd_4010875 := by exact prefixLift 4010875
  have htrace : WordTrace (prefixWord ++ tailWord_4010875) baseStart_4010875 baseEnd_4010875 := by
    simpa [prefixWord, tailWord_4010875, baseEnd_4010875] using wordTrace_append hprefix tailTrace_4010875
  have hstable : (prefixWord ++ tailWord_4010875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010875).length < 2 ^ (prefixWord ++ tailWord_4010875).sum := by decide
  have hdescent : baseEnd_4010875 < baseStart_4010875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010903 : List Nat := [1, 1, 3, 3, 1, 2, 1, 10]
def baseStart_4010903 : Nat := 118140960795 + 4010903 * 2 ^ 59
def prefixEnd_4010903 : Nat := 4983230072969 + 3 ^ 40 * 4010903 * 2
def baseEnd_4010903 : Nat := 152557118337809337575311

theorem tailTrace_4010903 : CollatzResearch.WordTrace tailWord_4010903 prefixEnd_4010903 152557118337809337575311 := by
  unfold tailWord_4010903
  simp only [CollatzResearch.WordTrace]
  refine ⟨146289650588190913541261363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97526433725460609027507575 146289650588190913541261363)
  ·
    refine ⟨219434475882286370311892045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146289650588190913541261363 219434475882286370311892045)
    ·
      refine ⟨82287928455857388866959517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219434475882286370311892045 82287928455857388866959517)
      ·
        refine ⟨30857973170946520825109819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82287928455857388866959517 30857973170946520825109819)
        ·
          refine ⟨46286959756419781237664729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30857973170946520825109819 46286959756419781237664729)
          ·
            refine ⟨34715219817314835928248547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46286959756419781237664729 34715219817314835928248547)
            ·
              refine ⟨52072829725972253892372821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34715219817314835928248547 52072829725972253892372821)
              ·
                refine ⟨152557118337809337575311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52072829725972253892372821 152557118337809337575311)
                ·
                  rfl

theorem cell22_4010903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 10].length) (baseStart_4010903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010903 prefixEnd_4010903 := by exact prefixLift 4010903
  have htrace : WordTrace (prefixWord ++ tailWord_4010903) baseStart_4010903 baseEnd_4010903 := by
    simpa [prefixWord, tailWord_4010903, baseEnd_4010903] using wordTrace_append hprefix tailTrace_4010903
  have hstable : (prefixWord ++ tailWord_4010903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010903).length < 2 ^ (prefixWord ++ tailWord_4010903).sum := by decide
  have hdescent : baseEnd_4010903 < baseStart_4010903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010969 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 1, 3]
def baseStart_4010969 : Nat := 118140960795 + 4010969 * 2 ^ 59
def prefixEnd_4010969 : Nat := 4983230072969 + 3 ^ 40 * 4010969 * 2
def baseEnd_4010969 : Nat := 1373036658189081866027597

theorem tailTrace_4010969 : CollatzResearch.WordTrace tailWord_4010969 prefixEnd_4010969 1373036658189081866027597 := by
  unfold tailWord_4010969
  simp only [CollatzResearch.WordTrace]
  refine ⟨146292057805951806813163961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97528038537301204542109307 146292057805951806813163961)
  ·
    refine ⟨109719043354463855109872971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146292057805951806813163961 109719043354463855109872971)
    ·
      refine ⟨164578565031695782664809457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109719043354463855109872971 164578565031695782664809457)
      ·
        refine ⟨123433923773771836998607093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164578565031695782664809457 123433923773771836998607093)
        ·
          refine ⟨11571930353791109718619415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123433923773771836998607093 11571930353791109718619415)
          ·
            refine ⟨17357895530686664577929123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11571930353791109718619415 17357895530686664577929123)
            ·
              refine ⟨26036843296029996866893685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17357895530686664577929123 26036843296029996866893685)
              ·
                refine ⟨2440954059002812206271283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26036843296029996866893685 2440954059002812206271283)
                ·
                  refine ⟨3661431088504218309406925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440954059002812206271283 3661431088504218309406925)
                  ·
                    refine ⟨1373036658189081866027597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3661431088504218309406925 1373036658189081866027597)
                    ·
                      rfl

theorem cell22_4010969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_4010969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4010969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4010969 prefixEnd_4010969 := by exact prefixLift 4010969
  have htrace : WordTrace (prefixWord ++ tailWord_4010969) baseStart_4010969 baseEnd_4010969 := by
    simpa [prefixWord, tailWord_4010969, baseEnd_4010969] using wordTrace_append hprefix tailTrace_4010969
  have hstable : (prefixWord ++ tailWord_4010969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010969).length < 2 ^ (prefixWord ++ tailWord_4010969).sum := by decide
  have hdescent : baseEnd_4010969 < baseStart_4010969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011025 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_4011025 : Nat := 118140960795 + 4011025 * 2 ^ 59
def prefixEnd_4011025 : Nat := 4983230072969 + 3 ^ 40 * 4011025 * 2
def baseEnd_4011025 : Nat := 1373055828133516386627425

theorem tailTrace_4011025 : CollatzResearch.WordTrace tailWord_4011025 prefixEnd_4011025 1373055828133516386627425 := by
  unfold tailWord_4011025
  simp only [CollatzResearch.WordTrace]
  refine ⟨146294100293748928377202529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97529400195832618918135019 146294100293748928377202529)
  ·
    refine ⟨109720575220311696282901897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146294100293748928377202529 109720575220311696282901897)
    ·
      refine ⟨82290431415233772212176423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109720575220311696282901897 82290431415233772212176423)
      ·
        refine ⟨123435647122850658318264635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82290431415233772212176423 123435647122850658318264635)
        ·
          refine ⟨185153470684275987477396953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123435647122850658318264635 185153470684275987477396953)
          ·
            refine ⟨138865103013206990608047715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185153470684275987477396953 138865103013206990608047715)
            ·
              refine ⟨208297654519810485912071573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138865103013206990608047715 208297654519810485912071573)
              ·
                refine ⟨9763952555616116527128355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208297654519810485912071573 9763952555616116527128355)
                ·
                  refine ⟨14645928833424174790692533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9763952555616116527128355 14645928833424174790692533)
                  ·
                    refine ⟨1373055828133516386627425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14645928833424174790692533 1373055828133516386627425)
                    ·
                      rfl

theorem cell22_4011025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_4011025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011025 prefixEnd_4011025 := by exact prefixLift 4011025
  have htrace : WordTrace (prefixWord ++ tailWord_4011025) baseStart_4011025 baseEnd_4011025 := by
    simpa [prefixWord, tailWord_4011025, baseEnd_4011025] using wordTrace_append hprefix tailTrace_4011025
  have hstable : (prefixWord ++ tailWord_4011025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011025).length < 2 ^ (prefixWord ++ tailWord_4011025).sum := by decide
  have hdescent : baseEnd_4011025 < baseStart_4011025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011044 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_4011044 : Nat := 118140960795 + 4011044 * 2 ^ 59
def prefixEnd_4011044 : Nat := 4983230072969 + 3 ^ 40 * 4011044 * 2
def baseEnd_4011044 : Nat := 457687444073935556800789

theorem tailTrace_4011044 : CollatzResearch.WordTrace tailWord_4011044 prefixEnd_4011044 457687444073935556800789 := by
  unfold tailWord_4011044
  simp only [CollatzResearch.WordTrace]
  refine ⟨73147396640340047311072093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97529862187120063081429457 73147396640340047311072093)
  ·
    refine ⟨27430273740127517741652035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73147396640340047311072093 27430273740127517741652035)
    ·
      refine ⟨41145410610191276612478053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27430273740127517741652035 41145410610191276612478053)
      ·
        refine ⟨7714764489410864364839635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41145410610191276612478053 7714764489410864364839635)
        ·
          refine ⟨11572146734116296547259453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714764489410864364839635 11572146734116296547259453)
          ·
            refine ⟨4339555025293611205222295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11572146734116296547259453 4339555025293611205222295)
            ·
              refine ⟨6509332537940416807833443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339555025293611205222295 6509332537940416807833443)
              ·
                refine ⟨9763998806910625211750165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509332537940416807833443 9763998806910625211750165)
                ·
                  refine ⟨457687444073935556800789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9763998806910625211750165 457687444073935556800789)
                  ·
                    rfl

theorem cell22_4011044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_4011044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011044 prefixEnd_4011044 := by exact prefixLift 4011044
  have htrace : WordTrace (prefixWord ++ tailWord_4011044) baseStart_4011044 baseEnd_4011044 := by
    simpa [prefixWord, tailWord_4011044, baseEnd_4011044] using wordTrace_append hprefix tailTrace_4011044
  have hstable : (prefixWord ++ tailWord_4011044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011044).length < 2 ^ (prefixWord ++ tailWord_4011044).sum := by decide
  have hdescent : baseEnd_4011044 < baseStart_4011044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011196 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_4011196 : Nat := 118140960795 + 4011196 * 2 ^ 59
def prefixEnd_4011196 : Nat := 4983230072969 + 3 ^ 40 * 4011196 * 2
def baseEnd_4011196 : Nat := 457704788309376313533967

theorem tailTrace_4011196 : CollatzResearch.WordTrace tailWord_4011196 prefixEnd_4011196 457704788309376313533967 := by
  unfold tailWord_4011196
  simp only [CollatzResearch.WordTrace]
  refine ⟨73150168588064712290838721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97533558117419616387784961 73150168588064712290838721)
  ·
    refine ⟨54862626441048534218129041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73150168588064712290838721 54862626441048534218129041)
    ·
      refine ⟨41146969830786400663596781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54862626441048534218129041 41146969830786400663596781)
      ·
        refine ⟨15430113686544900248848793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41146969830786400663596781 15430113686544900248848793)
        ·
          refine ⟨11572585264908675186636595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15430113686544900248848793 11572585264908675186636595)
          ·
            refine ⟨17358877897363012779954893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11572585264908675186636595 17358877897363012779954893)
            ·
              refine ⟨6509579211511129792483085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17358877897363012779954893 6509579211511129792483085)
              ·
                refine ⟨2441092204316673672181157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6509579211511129792483085 2441092204316673672181157)
                ·
                  refine ⟨457704788309376313533967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441092204316673672181157 457704788309376313533967)
                  ·
                    rfl

theorem cell22_4011196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_4011196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011196 prefixEnd_4011196 := by exact prefixLift 4011196
  have htrace : WordTrace (prefixWord ++ tailWord_4011196) baseStart_4011196 baseEnd_4011196 := by
    simpa [prefixWord, tailWord_4011196, baseEnd_4011196] using wordTrace_append hprefix tailTrace_4011196
  have hstable : (prefixWord ++ tailWord_4011196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011196).length < 2 ^ (prefixWord ++ tailWord_4011196).sum := by decide
  have hdescent : baseEnd_4011196 < baseStart_4011196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011224 : List Nat := [2, 1, 2, 2, 5, 1, 2, 7]
def baseStart_4011224 : Nat := 118140960795 + 4011224 * 2 ^ 59
def prefixEnd_4011224 : Nat := 4983230072969 + 3 ^ 40 * 4011224 * 2
def baseEnd_4011224 : Nat := 152569327766705133433535

theorem tailTrace_4011224 : CollatzResearch.WordTrace tailWord_4011224 prefixEnd_4011224 152569327766705133433535 := by
  unfold tailWord_4011224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73150679210013992681848363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97534238946685323575797817 73150679210013992681848363)
  ·
    refine ⟨109726018815020989022772545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73150679210013992681848363 109726018815020989022772545)
    ·
      refine ⟨82294514111265741767079409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109726018815020989022772545 82294514111265741767079409)
      ·
        refine ⟨61720885583449306325309557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82294514111265741767079409 61720885583449306325309557)
        ·
          refine ⟨5786333023448372467997771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61720885583449306325309557 5786333023448372467997771)
          ·
            refine ⟨8679499535172558701996657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786333023448372467997771 8679499535172558701996657)
            ·
              refine ⟨6509624651379419026497493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8679499535172558701996657 6509624651379419026497493)
              ·
                refine ⟨152569327766705133433535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6509624651379419026497493 152569327766705133433535)
                ·
                  rfl

theorem cell22_4011224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_4011224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011224 prefixEnd_4011224 := by exact prefixLift 4011224
  have htrace : WordTrace (prefixWord ++ tailWord_4011224) baseStart_4011224 baseEnd_4011224 := by
    simpa [prefixWord, tailWord_4011224, baseEnd_4011224] using wordTrace_append hprefix tailTrace_4011224
  have hstable : (prefixWord ++ tailWord_4011224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011224).length < 2 ^ (prefixWord ++ tailWord_4011224).sum := by decide
  have hdescent : baseEnd_4011224 < baseStart_4011224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011269 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 5]
def baseStart_4011269 : Nat := 118140960795 + 4011269 * 2 ^ 59
def prefixEnd_4011269 : Nat := 4983230072969 + 3 ^ 40 * 4011269 * 2
def baseEnd_4011269 : Nat := 457713118106660361175559

theorem tailTrace_4011269 : CollatzResearch.WordTrace tailWord_4011269 prefixEnd_4011269 457713118106660361175559 := by
  unfold tailWord_4011269
  simp only [CollatzResearch.WordTrace]
  refine ⟨146302999704864958049084861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97535333136576638699389907 146302999704864958049084861)
  ·
    refine ⟨54863624889324359268406823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146302999704864958049084861 54863624889324359268406823)
    ·
      refine ⟨82295437333986538902610235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54863624889324359268406823 82295437333986538902610235)
      ·
        refine ⟨123443156000979808353915353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82295437333986538902610235 123443156000979808353915353)
        ·
          refine ⟨92582367000734856265436515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123443156000979808353915353 92582367000734856265436515)
          ·
            refine ⟨138873550501102284398154773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92582367000734856265436515 138873550501102284398154773)
            ·
              refine ⟨6509697679739169581163505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138873550501102284398154773 6509697679739169581163505)
              ·
                refine ⟨4882273259804377185872629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509697679739169581163505 4882273259804377185872629)
                ·
                  refine ⟨457713118106660361175559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4882273259804377185872629 457713118106660361175559)
                  ·
                    rfl

theorem cell22_4011269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_4011269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011269 prefixEnd_4011269 := by exact prefixLift 4011269
  have htrace : WordTrace (prefixWord ++ tailWord_4011269) baseStart_4011269 baseEnd_4011269 := by
    simpa [prefixWord, tailWord_4011269, baseEnd_4011269] using wordTrace_append hprefix tailTrace_4011269
  have hstable : (prefixWord ++ tailWord_4011269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011269).length < 2 ^ (prefixWord ++ tailWord_4011269).sum := by decide
  have hdescent : baseEnd_4011269 < baseStart_4011269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011299 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_4011299 : Nat := 118140960795 + 4011299 * 2 ^ 59
def prefixEnd_4011299 : Nat := 4983230072969 + 3 ^ 40 * 4011299 * 2
def baseEnd_4011299 : Nat := 1373149623933071005276585

theorem tailTrace_4011299 : CollatzResearch.WordTrace tailWord_4011299 prefixEnd_4011299 1373149623933071005276585 := by
  unfold tailWord_4011299
  simp only [CollatzResearch.WordTrace]
  refine ⟨146304093894756273172676951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97536062596504182115117967 146304093894756273172676951)
  ·
    refine ⟨219456140842134409759015427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146304093894756273172676951 219456140842134409759015427)
    ·
      refine ⟨329184211263201614638523141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219456140842134409759015427 329184211263201614638523141)
      ·
        refine ⟨61722039611850302744723089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329184211263201614638523141 61722039611850302744723089)
        ·
          refine ⟨46291529708887727058542317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61722039611850302744723089 46291529708887727058542317)
          ·
            refine ⟨17359323640832897646953369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46291529708887727058542317 17359323640832897646953369)
            ·
              refine ⟨13019492730624673235215027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17359323640832897646953369 13019492730624673235215027)
              ·
                refine ⟨19529239095937009852822541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13019492730624673235215027 19529239095937009852822541)
                ·
                  refine ⟨7323464660976378694808453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19529239095937009852822541 7323464660976378694808453)
                  ·
                    refine ⟨1373149623933071005276585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7323464660976378694808453 1373149623933071005276585)
                    ·
                      rfl

theorem cell22_4011299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_4011299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011299 prefixEnd_4011299 := by exact prefixLift 4011299
  have htrace : WordTrace (prefixWord ++ tailWord_4011299) baseStart_4011299 baseEnd_4011299 := by
    simpa [prefixWord, tailWord_4011299, baseEnd_4011299] using wordTrace_append hprefix tailTrace_4011299
  have hstable : (prefixWord ++ tailWord_4011299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011299).length < 2 ^ (prefixWord ++ tailWord_4011299).sum := by decide
  have hdescent : baseEnd_4011299 < baseStart_4011299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011389 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4011389 : Nat := 118140960795 + 4011389 * 2 ^ 59
def prefixEnd_4011389 : Nat := 4983230072969 + 3 ^ 40 * 4011389 * 2
def baseEnd_4011389 : Nat := 1373180432772340770526309

theorem tailTrace_4011389 : CollatzResearch.WordTrace tailWord_4011389 prefixEnd_4011389 1373180432772340770526309 := by
  unfold tailWord_4011389
  simp only [CollatzResearch.WordTrace]
  refine ⟨146307376464430218543453221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97538250976286812362302147 146307376464430218543453221)
  ·
    refine ⟨27432633087080665976897479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146307376464430218543453221 27432633087080665976897479)
    ·
      refine ⟨41148949630620998965346219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27432633087080665976897479 41148949630620998965346219)
      ·
        refine ⟨61723424445931498448019329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41148949630620998965346219 61723424445931498448019329)
        ·
          refine ⟨46292568334448623836014497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61723424445931498448019329 46292568334448623836014497)
          ·
            refine ⟨34719426250836467877010873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46292568334448623836014497 34719426250836467877010873)
            ·
              refine ⟨26039569688127350907758155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34719426250836467877010873 26039569688127350907758155)
              ·
                refine ⟨39059354532191026361637233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26039569688127350907758155 39059354532191026361637233)
                ·
                  refine ⟨29294515899143269771227925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39059354532191026361637233 29294515899143269771227925)
                  ·
                    refine ⟨1373180432772340770526309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29294515899143269771227925 1373180432772340770526309)
                    ·
                      rfl

theorem cell22_4011389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4011389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011389 prefixEnd_4011389 := by exact prefixLift 4011389
  have htrace : WordTrace (prefixWord ++ tailWord_4011389) baseStart_4011389 baseEnd_4011389 := by
    simpa [prefixWord, tailWord_4011389, baseEnd_4011389] using wordTrace_append hprefix tailTrace_4011389
  have hstable : (prefixWord ++ tailWord_4011389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011389).length < 2 ^ (prefixWord ++ tailWord_4011389).sum := by decide
  have hdescent : baseEnd_4011389 < baseStart_4011389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011466 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_4011466 : Nat := 118140960795 + 4011466 * 2 ^ 59
def prefixEnd_4011466 : Nat := 4983230072969 + 3 ^ 40 * 4011466 * 2
def baseEnd_4011466 : Nat := 457735597148646078783691

theorem tailTrace_4011466 : CollatzResearch.WordTrace tailWord_4011466 prefixEnd_4011466 457735597148646078783691 := by
  unfold tailWord_4011466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36577546221287815173501563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97540123256767507129337501 36577546221287815173501563)
  ·
    refine ⟨54866319331931722760252345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36577546221287815173501563 54866319331931722760252345)
    ·
      refine ⟨41149739498948792070189259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54866319331931722760252345 41149739498948792070189259)
      ·
        refine ⟨61724609248423188105283889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41149739498948792070189259 61724609248423188105283889)
        ·
          refine ⟨46293456936317391078962917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61724609248423188105283889 46293456936317391078962917)
          ·
            refine ⟨8680023175559510827305547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46293456936317391078962917 8680023175559510827305547)
            ·
              refine ⟨13020034763339266240958321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680023175559510827305547 13020034763339266240958321)
              ·
                refine ⟨9765026072504449680718741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020034763339266240958321 9765026072504449680718741)
                ·
                  refine ⟨457735597148646078783691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9765026072504449680718741 457735597148646078783691)
                  ·
                    rfl

theorem cell22_4011466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_4011466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011466 prefixEnd_4011466 := by exact prefixLift 4011466
  have htrace : WordTrace (prefixWord ++ tailWord_4011466) baseStart_4011466 baseEnd_4011466 := by
    simpa [prefixWord, tailWord_4011466, baseEnd_4011466] using wordTrace_append hprefix tailTrace_4011466
  have hstable : (prefixWord ++ tailWord_4011466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011466).length < 2 ^ (prefixWord ++ tailWord_4011466).sum := by decide
  have hdescent : baseEnd_4011466 < baseStart_4011466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011481 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_4011481 : Nat := 118140960795 + 4011481 * 2 ^ 59
def prefixEnd_4011481 : Nat := 4983230072969 + 3 ^ 40 * 4011481 * 2
def baseEnd_4011481 : Nat := 1373211926252483197226027

theorem tailTrace_4011481 : CollatzResearch.WordTrace tailWord_4011481 prefixEnd_4011481 1373211926252483197226027 := by
  unfold tailWord_4011481
  simp only [CollatzResearch.WordTrace]
  refine ⟨146310731980096918255802297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97540487986731278837201531 146310731980096918255802297)
  ·
    refine ⟨109733048985072688691851723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146310731980096918255802297 109733048985072688691851723)
    ·
      refine ⟨164599573477609033037777585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109733048985072688691851723 164599573477609033037777585)
      ·
        refine ⟨123449680108206774778333189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164599573477609033037777585 123449680108206774778333189)
        ·
          refine ⟨23146815020288770270937473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123449680108206774778333189 23146815020288770270937473)
          ·
            refine ⟨17360111265216577703203105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23146815020288770270937473 17360111265216577703203105)
            ·
              refine ⟨13020083448912433277402329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360111265216577703203105 13020083448912433277402329)
              ·
                refine ⟨9765062586684324958051747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020083448912433277402329 9765062586684324958051747)
                ·
                  refine ⟨14647593880026487437077621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765062586684324958051747 14647593880026487437077621)
                  ·
                    refine ⟨1373211926252483197226027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14647593880026487437077621 1373211926252483197226027)
                    ·
                      rfl

theorem cell22_4011481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_4011481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011481 prefixEnd_4011481 := by exact prefixLift 4011481
  have htrace : WordTrace (prefixWord ++ tailWord_4011481) baseStart_4011481 baseEnd_4011481 := by
    simpa [prefixWord, tailWord_4011481, baseEnd_4011481] using wordTrace_append hprefix tailTrace_4011481
  have hstable : (prefixWord ++ tailWord_4011481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011481).length < 2 ^ (prefixWord ++ tailWord_4011481).sum := by decide
  have hdescent : baseEnd_4011481 < baseStart_4011481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011485 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4011485 : Nat := 118140960795 + 4011485 * 2 ^ 59
def prefixEnd_4011485 : Nat := 4983230072969 + 3 ^ 40 * 4011485 * 2
def baseEnd_4011485 : Nat := 1373213295534228520126015

theorem tailTrace_4011485 : CollatzResearch.WordTrace tailWord_4011485 prefixEnd_4011485 1373213295534228520126015 := by
  unfold tailWord_4011485
  simp only [CollatzResearch.WordTrace]
  refine ⟨146310877872082426938947909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97540585248054951292631939 146310877872082426938947909)
  ·
    refine ⟨27433289601015455051052733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146310877872082426938947909 27433289601015455051052733)
    ·
      refine ⟨10287483600380795644144775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27433289601015455051052733 10287483600380795644144775)
      ·
        refine ⟨15431225400571193466217163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10287483600380795644144775 15431225400571193466217163)
        ·
          refine ⟨23146838100856790199325745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15431225400571193466217163 23146838100856790199325745)
          ·
            refine ⟨17360128575642592649494309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23146838100856790199325745 17360128575642592649494309)
            ·
              refine ⟨3255024107932986121780183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17360128575642592649494309 3255024107932986121780183)
              ·
                refine ⟨4882536161899479182670275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255024107932986121780183 4882536161899479182670275)
                ·
                  refine ⟨7323804242849218774005413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882536161899479182670275 7323804242849218774005413)
                  ·
                    refine ⟨1373213295534228520126015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7323804242849218774005413 1373213295534228520126015)
                    ·
                      rfl

theorem cell22_4011485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4011485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011485 prefixEnd_4011485 := by exact prefixLift 4011485
  have htrace : WordTrace (prefixWord ++ tailWord_4011485) baseStart_4011485 baseEnd_4011485 := by
    simpa [prefixWord, tailWord_4011485, baseEnd_4011485] using wordTrace_append hprefix tailTrace_4011485
  have hstable : (prefixWord ++ tailWord_4011485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011485).length < 2 ^ (prefixWord ++ tailWord_4011485).sum := by decide
  have hdescent : baseEnd_4011485 < baseStart_4011485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011496 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4011496 : Nat := 118140960795 + 4011496 * 2 ^ 59
def prefixEnd_4011496 : Nat := 4983230072969 + 3 ^ 40 * 4011496 * 2
def baseEnd_4011496 : Nat := 1373217061059028158100981

theorem tailTrace_4011496 : CollatzResearch.WordTrace tailWord_4011496 prefixEnd_4011496 1373217061059028158100981 := by
  unfold tailWord_4011496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73155639537521287908799171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97540852716695050545065561 73155639537521287908799171)
  ·
    refine ⟨109733459306281931863198757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73155639537521287908799171 109733459306281931863198757)
    ·
      refine ⟨20575023619927862224349767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109733459306281931863198757 20575023619927862224349767)
      ·
        refine ⟨30862535429891793336524651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20575023619927862224349767 30862535429891793336524651)
        ·
          refine ⟨46293803144837690004786977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30862535429891793336524651 46293803144837690004786977)
          ·
            refine ⟨34720352358628267503590233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46293803144837690004786977 34720352358628267503590233)
            ·
              refine ⟨26040264268971200627692675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34720352358628267503590233 26040264268971200627692675)
              ·
                refine ⟨39060396403456800941539013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26040264268971200627692675 39060396403456800941539013)
                ·
                  refine ⟨7323824325648150176538565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39060396403456800941539013 7323824325648150176538565)
                  ·
                    refine ⟨1373217061059028158100981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7323824325648150176538565 1373217061059028158100981)
                    ·
                      rfl

theorem cell22_4011496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4011496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011496 prefixEnd_4011496 := by exact prefixLift 4011496
  have htrace : WordTrace (prefixWord ++ tailWord_4011496) baseStart_4011496 baseEnd_4011496 := by
    simpa [prefixWord, tailWord_4011496, baseEnd_4011496] using wordTrace_append hprefix tailTrace_4011496
  have hstable : (prefixWord ++ tailWord_4011496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011496).length < 2 ^ (prefixWord ++ tailWord_4011496).sum := by decide
  have hdescent : baseEnd_4011496 < baseStart_4011496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011573 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 5]
def baseStart_4011573 : Nat := 118140960795 + 4011573 * 2 ^ 59
def prefixEnd_4011573 : Nat := 4983230072969 + 3 ^ 40 * 4011573 * 2
def baseEnd_4011573 : Nat := 457747806577541874641915

theorem tailTrace_4011573 : CollatzResearch.WordTrace tailWord_4011573 prefixEnd_4011573 457747806577541874641915 := by
  unfold tailWord_4011573
  simp only [CollatzResearch.WordTrace]
  refine ⟨146314087495763617968151373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97542724997175745312100915 146314087495763617968151373)
  ·
    refine ⟨54867782810911356738056765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146314087495763617968151373 54867782810911356738056765)
    ·
      refine ⟨20575418554091758776771287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54867782810911356738056765 20575418554091758776771287)
      ·
        refine ⟨30863127831137638165156931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20575418554091758776771287 30863127831137638165156931)
        ·
          refine ⟨46294691746706457247735397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30863127831137638165156931 46294691746706457247735397)
          ·
            refine ⟨8680254702507460733950387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46294691746706457247735397 8680254702507460733950387)
            ·
              refine ⟨13020382053761191100925581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680254702507460733950387 13020382053761191100925581)
              ·
                refine ⟨4882643270160446662847093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13020382053761191100925581 4882643270160446662847093)
                ·
                  refine ⟨457747806577541874641915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4882643270160446662847093 457747806577541874641915)
                  ·
                    rfl

theorem cell22_4011573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_4011573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011573 prefixEnd_4011573 := by exact prefixLift 4011573
  have htrace : WordTrace (prefixWord ++ tailWord_4011573) baseStart_4011573 baseEnd_4011573 := by
    simpa [prefixWord, tailWord_4011573, baseEnd_4011573] using wordTrace_append hprefix tailTrace_4011573
  have hstable : (prefixWord ++ tailWord_4011573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011573).length < 2 ^ (prefixWord ++ tailWord_4011573).sum := by decide
  have hdescent : baseEnd_4011573 < baseStart_4011573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011616 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_4011616 : Nat := 118140960795 + 4011616 * 2 ^ 59
def prefixEnd_4011616 : Nat := 4983230072969 + 3 ^ 40 * 4011616 * 2
def baseEnd_4011616 : Nat := 1373258139511387845100613

theorem tailTrace_4011616 : CollatzResearch.WordTrace tailWord_4011616 prefixEnd_4011616 1373258139511387845100613 := by
  unfold tailWord_4011616
  simp only [CollatzResearch.WordTrace]
  refine ⟨73157827917303918155983351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97543770556405224207977801 73157827917303918155983351)
  ·
    refine ⟨109736741875955877233975027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73157827917303918155983351 109736741875955877233975027)
    ·
      refine ⟨164605112813933815850962541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109736741875955877233975027 164605112813933815850962541)
      ·
        refine ⟨61726917305225180944110953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164605112813933815850962541 61726917305225180944110953)
        ·
          refine ⟨46295187978918885708083215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61726917305225180944110953 46295187978918885708083215)
          ·
            refine ⟨69442781968378328562124823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46295187978918885708083215 69442781968378328562124823)
            ·
              refine ⟨104164172952567492843187235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69442781968378328562124823 104164172952567492843187235)
              ·
                refine ⟨156246259428851239264780853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104164172952567492843187235 156246259428851239264780853)
                ·
                  refine ⟨14648086821454803681073205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156246259428851239264780853 14648086821454803681073205)
                  ·
                    refine ⟨1373258139511387845100613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14648086821454803681073205 1373258139511387845100613)
                    ·
                      rfl

theorem cell22_4011616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_4011616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011616 prefixEnd_4011616 := by exact prefixLift 4011616
  have htrace : WordTrace (prefixWord ++ tailWord_4011616) baseStart_4011616 baseEnd_4011616 := by
    simpa [prefixWord, tailWord_4011616, baseEnd_4011616] using wordTrace_append hprefix tailTrace_4011616
  have hstable : (prefixWord ++ tailWord_4011616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011616).length < 2 ^ (prefixWord ++ tailWord_4011616).sum := by decide
  have hdescent : baseEnd_4011616 < baseStart_4011616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011631 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_4011631 : Nat := 118140960795 + 4011631 * 2 ^ 59
def prefixEnd_4011631 : Nat := 4983230072969 + 3 ^ 40 * 4011631 * 2
def baseEnd_4011631 : Nat := 1373263274317932805975567

theorem tailTrace_4011631 : CollatzResearch.WordTrace tailWord_4011631 prefixEnd_4011631 1373263274317932805975567 := by
  unfold tailWord_4011631
  simp only [CollatzResearch.WordTrace]
  refine ⟨146316202929553493873762747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97544135286368995915841831 146316202929553493873762747)
  ·
    refine ⟨219474304394330240810644121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146316202929553493873762747 219474304394330240810644121)
    ·
      refine ⟨164605728295747680607983091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219474304394330240810644121 164605728295747680607983091)
      ·
        refine ⟨246908592443621520911974637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164605728295747680607983091 246908592443621520911974637)
        ·
          refine ⟨92590722166358070341990489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246908592443621520911974637 92590722166358070341990489)
          ·
            refine ⟨69443041624768552756492867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92590722166358070341990489 69443041624768552756492867)
            ·
              refine ⟨104164562437152829134739301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69443041624768552756492867 104164562437152829134739301)
              ·
                refine ⟨19530855456966155462763619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104164562437152829134739301 19530855456966155462763619)
                ·
                  refine ⟨29296283185449233194145429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19530855456966155462763619 29296283185449233194145429)
                  ·
                    refine ⟨1373263274317932805975567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29296283185449233194145429 1373263274317932805975567)
                    ·
                      rfl

theorem cell22_4011631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_4011631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011631 prefixEnd_4011631 := by exact prefixLift 4011631
  have htrace : WordTrace (prefixWord ++ tailWord_4011631) baseStart_4011631 baseEnd_4011631 := by
    simpa [prefixWord, tailWord_4011631, baseEnd_4011631] using wordTrace_append hprefix tailTrace_4011631
  have hstable : (prefixWord ++ tailWord_4011631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011631).length < 2 ^ (prefixWord ++ tailWord_4011631).sum := by decide
  have hdescent : baseEnd_4011631 < baseStart_4011631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011652 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_4011652 : Nat := 118140960795 + 4011652 * 2 ^ 59
def prefixEnd_4011652 : Nat := 4983230072969 + 3 ^ 40 * 4011652 * 2
def baseEnd_4011652 : Nat := 457756821015698583733501

theorem tailTrace_4011652 : CollatzResearch.WordTrace tailWord_4011652 prefixEnd_4011652 457756821015698583733501 := by
  unfold tailWord_4011652
  simp only [CollatzResearch.WordTrace]
  refine ⟨73158484431238707230138605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97544645908318276306851473 73158484431238707230138605)
  ·
    refine ⟨27434431661714515211301977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73158484431238707230138605 27434431661714515211301977)
    ·
      refine ⟨20575823746285886408476483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27434431661714515211301977 20575823746285886408476483)
      ·
        refine ⟨30863735619428829612714725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20575823746285886408476483 30863735619428829612714725)
        ·
          refine ⟨5786950428642905552384011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30863735619428829612714725 5786950428642905552384011)
          ·
            refine ⟨8680425642964358328576017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786950428642905552384011 8680425642964358328576017)
            ·
              refine ⟨6510319232223268746432013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8680425642964358328576017 6510319232223268746432013)
              ·
                refine ⟨2441369712083725779912005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6510319232223268746432013 2441369712083725779912005)
                ·
                  refine ⟨457756821015698583733501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441369712083725779912005 457756821015698583733501)
                  ·
                    rfl

theorem cell22_4011652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_4011652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011652 prefixEnd_4011652 := by exact prefixLift 4011652
  have htrace : WordTrace (prefixWord ++ tailWord_4011652) baseStart_4011652 baseEnd_4011652 := by
    simpa [prefixWord, tailWord_4011652, baseEnd_4011652] using wordTrace_append hprefix tailTrace_4011652
  have hstable : (prefixWord ++ tailWord_4011652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011652).length < 2 ^ (prefixWord ++ tailWord_4011652).sum := by decide
  have hdescent : baseEnd_4011652 < baseStart_4011652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011708 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_4011708 : Nat := 118140960795 + 4011708 * 2 ^ 59
def prefixEnd_4011708 : Nat := 4983230072969 + 3 ^ 40 * 4011708 * 2
def baseEnd_4011708 : Nat := 457763210997176757266777

theorem tailTrace_4011708 : CollatzResearch.WordTrace tailWord_4011708 prefixEnd_4011708 457763210997176757266777 := by
  unfold tailWord_4011708
  simp only [CollatzResearch.WordTrace]
  refine ⟨73159505675137268012157889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97546007566849690682877185 73159505675137268012157889)
  ·
    refine ⟨54869629256352951009118417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73159505675137268012157889 54869629256352951009118417)
    ·
      refine ⟨41152221942264713256838813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54869629256352951009118417 41152221942264713256838813)
      ·
        refine ⟨15432083228349267471314555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41152221942264713256838813 15432083228349267471314555)
        ·
          refine ⟨23148124842523901206971833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15432083228349267471314555 23148124842523901206971833)
          ·
            refine ⟨17361093631892925905228875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23148124842523901206971833 17361093631892925905228875)
            ·
              refine ⟨26041640447839388857843313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361093631892925905228875 26041640447839388857843313)
              ·
                refine ⟨19531230335879541643382485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26041640447839388857843313 19531230335879541643382485)
                ·
                  refine ⟨457763210997176757266777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19531230335879541643382485 457763210997176757266777)
                  ·
                    rfl

theorem cell22_4011708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_4011708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011708 prefixEnd_4011708 := by exact prefixLift 4011708
  have htrace : WordTrace (prefixWord ++ tailWord_4011708) baseStart_4011708 baseEnd_4011708 := by
    simpa [prefixWord, tailWord_4011708, baseEnd_4011708] using wordTrace_append hprefix tailTrace_4011708
  have hstable : (prefixWord ++ tailWord_4011708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011708).length < 2 ^ (prefixWord ++ tailWord_4011708).sum := by decide
  have hdescent : baseEnd_4011708 < baseStart_4011708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011714 : List Nat := [3, 5, 1, 2, 1, 2, 8]
def baseStart_4011714 : Nat := 118140960795 + 4011714 * 2 ^ 59
def prefixEnd_4011714 : Nat := 4983230072969 + 3 ^ 40 * 4011714 * 2
def baseEnd_4011714 : Nat := 50862655070894379857419

theorem tailTrace_4011714 : CollatzResearch.WordTrace tailWord_4011714 prefixEnd_4011714 50862655070894379857419 := by
  unfold tailWord_4011714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36579807547063199762258549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97546153458835199366022797 36579807547063199762258549)
  ·
    refine ⟨3429356957537174977711739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36579807547063199762258549 3429356957537174977711739)
    ·
      refine ⟨5144035436305762466567609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429356957537174977711739 5144035436305762466567609)
      ·
        refine ⟨3858026577229321849925707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5144035436305762466567609 3858026577229321849925707)
        ·
          refine ⟨5787039865843982774888561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858026577229321849925707 5787039865843982774888561)
          ·
            refine ⟨4340279899382987081166421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787039865843982774888561 4340279899382987081166421)
            ·
              refine ⟨50862655070894379857419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4340279899382987081166421 50862655070894379857419)
              ·
                rfl

theorem cell22_4011714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 8].length) (baseStart_4011714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011714 prefixEnd_4011714 := by exact prefixLift 4011714
  have htrace : WordTrace (prefixWord ++ tailWord_4011714) baseStart_4011714 baseEnd_4011714 := by
    simpa [prefixWord, tailWord_4011714, baseEnd_4011714] using wordTrace_append hprefix tailTrace_4011714
  have hstable : (prefixWord ++ tailWord_4011714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011714).length < 2 ^ (prefixWord ++ tailWord_4011714).sum := by decide
  have hdescent : baseEnd_4011714 < baseStart_4011714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011729 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 1, 3]
def baseStart_4011729 : Nat := 118140960795 + 4011729 * 2 ^ 59
def prefixEnd_4011729 : Nat := 4983230072969 + 3 ^ 40 * 4011729 * 2
def baseEnd_4011729 : Nat := 1373296821720693217025267

theorem tailTrace_4011729 : CollatzResearch.WordTrace tailWord_4011729 prefixEnd_4011729 1373296821720693217025267 := by
  unfold tailWord_4011729
  simp only [CollatzResearch.WordTrace]
  refine ⟨146319777283198456610830241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97546518188798971073886827 146319777283198456610830241)
  ·
    refine ⟨109739832962398842458122681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146319777283198456610830241 109739832962398842458122681)
    ·
      refine ⟨82304874721799131843592011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109739832962398842458122681 82304874721799131843592011)
      ·
        refine ⟨123457312082698697765388017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82304874721799131843592011 123457312082698697765388017)
        ·
          refine ⟨92592984062024023324041013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123457312082698697765388017 92592984062024023324041013)
          ·
            refine ⟨8680592255814752186628845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92592984062024023324041013 8680592255814752186628845)
            ·
              refine ⟨3255222095930532069985817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8680592255814752186628845 3255222095930532069985817)
              ·
                refine ⟨2441416571947899052489363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255222095930532069985817 2441416571947899052489363)
                ·
                  refine ⟨3662124857921848578734045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441416571947899052489363 3662124857921848578734045)
                  ·
                    refine ⟨1373296821720693217025267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3662124857921848578734045 1373296821720693217025267)
                    ·
                      rfl

theorem cell22_4011729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_4011729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011729 prefixEnd_4011729 := by exact prefixLift 4011729
  have htrace : WordTrace (prefixWord ++ tailWord_4011729) baseStart_4011729 baseEnd_4011729 := by
    simpa [prefixWord, tailWord_4011729, baseEnd_4011729] using wordTrace_append hprefix tailTrace_4011729
  have hstable : (prefixWord ++ tailWord_4011729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011729).length < 2 ^ (prefixWord ++ tailWord_4011729).sum := by decide
  have hdescent : baseEnd_4011729 < baseStart_4011729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011755 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 1, 4]
def baseStart_4011755 : Nat := 118140960795 + 4011755 * 2 ^ 59
def prefixEnd_4011755 : Nat := 4983230072969 + 3 ^ 40 * 4011755 * 2
def baseEnd_4011755 : Nat := 1373305722052037815875187

theorem tailTrace_4011755 : CollatzResearch.WordTrace tailWord_4011755 prefixEnd_4011755 1373305722052037815875187 := by
  unfold tailWord_4011755
  simp only [CollatzResearch.WordTrace]
  refine ⟨146320725581104263051276719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97547150387402842034184479 146320725581104263051276719)
  ·
    refine ⟨219481088371656394576915079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146320725581104263051276719 219481088371656394576915079)
    ·
      refine ⟨329221632557484591865372619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219481088371656394576915079 329221632557484591865372619)
      ·
        refine ⟨493832448836226887798058929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329221632557484591865372619 493832448836226887798058929)
        ·
          refine ⟨370374336627170165848544197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493832448836226887798058929 370374336627170165848544197)
          ·
            refine ⟨69445188117594406096602037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370374336627170165848544197 69445188117594406096602037)
            ·
              refine ⟨6510486386024475571556441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69445188117594406096602037 6510486386024475571556441)
              ·
                refine ⟨4882864789518356678667331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510486386024475571556441 4882864789518356678667331)
                ·
                  refine ⟨7324297184277535018000997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882864789518356678667331 7324297184277535018000997)
                  ·
                    refine ⟨1373305722052037815875187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324297184277535018000997 1373305722052037815875187)
                    ·
                      rfl

theorem cell22_4011755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4].length) (baseStart_4011755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011755 prefixEnd_4011755 := by exact prefixLift 4011755
  have htrace : WordTrace (prefixWord ++ tailWord_4011755) baseStart_4011755 baseEnd_4011755 := by
    simpa [prefixWord, tailWord_4011755, baseEnd_4011755] using wordTrace_append hprefix tailTrace_4011755
  have hstable : (prefixWord ++ tailWord_4011755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011755).length < 2 ^ (prefixWord ++ tailWord_4011755).sum := by decide
  have hdescent : baseEnd_4011755 < baseStart_4011755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011770 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_4011770 : Nat := 118140960795 + 4011770 * 2 ^ 59
def prefixEnd_4011770 : Nat := 4983230072969 + 3 ^ 40 * 4011770 * 2
def baseEnd_4011770 : Nat := 457770285619527592250047

theorem tailTrace_4011770 : CollatzResearch.WordTrace tailWord_4011770 prefixEnd_4011770 457770285619527592250047 := by
  unfold tailWord_4011770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580318169012480153268191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97547515117366613742048509 36580318169012480153268191)
  ·
    refine ⟨54870477253518720229902287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36580318169012480153268191 54870477253518720229902287)
    ·
      refine ⟨82305715880278080344853431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54870477253518720229902287 82305715880278080344853431)
      ·
        refine ⟨123458573820417120517280147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82305715880278080344853431 123458573820417120517280147)
        ·
          refine ⟨185187860730625680775920221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123458573820417120517280147 185187860730625680775920221)
          ·
            refine ⟨69445447773984630290970083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185187860730625680775920221 69445447773984630290970083)
            ·
              refine ⟨104168171660976945436455125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69445447773984630290970083 104168171660976945436455125)
              ·
                refine ⟨2441441523304147158666917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104168171660976945436455125 2441441523304147158666917)
                ·
                  refine ⟨457770285619527592250047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441441523304147158666917 457770285619527592250047)
                  ·
                    rfl

theorem cell22_4011770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_4011770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011770 prefixEnd_4011770 := by exact prefixLift 4011770
  have htrace : WordTrace (prefixWord ++ tailWord_4011770) baseStart_4011770 baseEnd_4011770 := by
    simpa [prefixWord, tailWord_4011770, baseEnd_4011770] using wordTrace_append hprefix tailTrace_4011770
  have hstable : (prefixWord ++ tailWord_4011770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011770).length < 2 ^ (prefixWord ++ tailWord_4011770).sum := by decide
  have hdescent : baseEnd_4011770 < baseStart_4011770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011772 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_4011772 : Nat := 118140960795 + 4011772 * 2 ^ 59
def prefixEnd_4011772 : Nat := 4983230072969 + 3 ^ 40 * 4011772 * 2
def baseEnd_4011772 : Nat := 1373311541499455438200135

theorem tailTrace_4011772 : CollatzResearch.WordTrace tailWord_4011772 prefixEnd_4011772 1373311541499455438200135 := by
  unfold tailWord_4011772
  simp only [CollatzResearch.WordTrace]
  refine ⟨73160672811021337477322785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97547563748028449969763713 73160672811021337477322785)
  ·
    refine ⟨54870504608266003107992089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73160672811021337477322785 54870504608266003107992089)
    ·
      refine ⟨41152878456199502330994067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54870504608266003107992089 41152878456199502330994067)
      ·
        refine ⟨61729317684299253496491101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41152878456199502330994067 61729317684299253496491101)
        ·
          refine ⟨23148494131612220061184163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61729317684299253496491101 23148494131612220061184163)
          ·
            refine ⟨34722741197418330091776245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148494131612220061184163 34722741197418330091776245)
            ·
              refine ⟨3255256987257968446104023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34722741197418330091776245 3255256987257968446104023)
              ·
                refine ⟨4882885480886952669156035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255256987257968446104023 4882885480886952669156035)
                ·
                  refine ⟨7324328221330429003734053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882885480886952669156035 7324328221330429003734053)
                  ·
                    refine ⟨1373311541499455438200135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324328221330429003734053 1373311541499455438200135)
                    ·
                      rfl

theorem cell22_4011772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_4011772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011772 prefixEnd_4011772 := by exact prefixLift 4011772
  have htrace : WordTrace (prefixWord ++ tailWord_4011772) baseStart_4011772 baseEnd_4011772 := by
    simpa [prefixWord, tailWord_4011772, baseEnd_4011772] using wordTrace_append hprefix tailTrace_4011772
  have hstable : (prefixWord ++ tailWord_4011772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011772).length < 2 ^ (prefixWord ++ tailWord_4011772).sum := by decide
  have hdescent : baseEnd_4011772 < baseStart_4011772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011787 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 4]
def baseStart_4011787 : Nat := 118140960795 + 4011787 * 2 ^ 59
def prefixEnd_4011787 : Nat := 4983230072969 + 3 ^ 40 * 4011787 * 2
def baseEnd_4011787 : Nat := 457772225435333466358363

theorem tailTrace_4011787 : CollatzResearch.WordTrace tailWord_4011787 prefixEnd_4011787 457772225435333466358363 := by
  unfold tailWord_4011787
  simp only [CollatzResearch.WordTrace]
  refine ⟨146321892716988332516441615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97547928477992221677627743 146321892716988332516441615)
  ·
    refine ⟨219482839075482498774662423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146321892716988332516441615 219482839075482498774662423)
    ·
      refine ⟨329224258613223748161993635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219482839075482498774662423 329224258613223748161993635)
      ·
        refine ⟨493836387919835622242990453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329224258613223748161993635 493836387919835622242990453)
        ·
          refine ⟨46297161367484589585280355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 493836387919835622242990453 46297161367484589585280355)
          ·
            refine ⟨69445742051226884377920533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46297161367484589585280355 69445742051226884377920533)
            ·
              refine ⟨3255269158651260205215025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69445742051226884377920533 3255269158651260205215025)
              ·
                refine ⟨2441451868988445153911269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255269158651260205215025 2441451868988445153911269)
                ·
                  refine ⟨457772225435333466358363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441451868988445153911269 457772225435333466358363)
                  ·
                    rfl

theorem cell22_4011787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 4].length) (baseStart_4011787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011787 prefixEnd_4011787 := by exact prefixLift 4011787
  have htrace : WordTrace (prefixWord ++ tailWord_4011787) baseStart_4011787 baseEnd_4011787 := by
    simpa [prefixWord, tailWord_4011787, baseEnd_4011787] using wordTrace_append hprefix tailTrace_4011787
  have hstable : (prefixWord ++ tailWord_4011787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011787).length < 2 ^ (prefixWord ++ tailWord_4011787).sum := by decide
  have hdescent : baseEnd_4011787 < baseStart_4011787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011802 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_4011802 : Nat := 118140960795 + 4011802 * 2 ^ 59
def prefixEnd_4011802 : Nat := 4983230072969 + 3 ^ 40 * 4011802 * 2
def baseEnd_4011802 : Nat := 1373321811112545359950043

theorem tailTrace_4011802 : CollatzResearch.WordTrace tailWord_4011802 prefixEnd_4011802 1373321811112545359950043 := by
  unfold tailWord_4011802
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580609952983497519559415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97548293207955993385491773 36580609952983497519559415)
  ·
    refine ⟨54870914929475246279339123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36580609952983497519559415 54870914929475246279339123)
    ·
      refine ⟨82306372394212869419008685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54870914929475246279339123 82306372394212869419008685)
      ·
        refine ⟨30864889647829826032128257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82306372394212869419008685 30864889647829826032128257)
        ·
          refine ⟨23148667235872369524096193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30864889647829826032128257 23148667235872369524096193)
          ·
            refine ⟨17361500426904277143072145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23148667235872369524096193 17361500426904277143072145)
            ·
              refine ⟨13021125320178207857304109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17361500426904277143072145 13021125320178207857304109)
              ·
                refine ⟨4882921995066827946489041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13021125320178207857304109 4882921995066827946489041)
                ·
                  refine ⟨3662191496300120959866781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882921995066827946489041 3662191496300120959866781)
                  ·
                    refine ⟨1373321811112545359950043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3662191496300120959866781 1373321811112545359950043)
                    ·
                      rfl

theorem cell22_4011802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_4011802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011802 prefixEnd_4011802 := by exact prefixLift 4011802
  have htrace : WordTrace (prefixWord ++ tailWord_4011802) baseStart_4011802 baseEnd_4011802 := by
    simpa [prefixWord, tailWord_4011802, baseEnd_4011802] using wordTrace_append hprefix tailTrace_4011802
  have hstable : (prefixWord ++ tailWord_4011802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011802).length < 2 ^ (prefixWord ++ tailWord_4011802).sum := by decide
  have hdescent : baseEnd_4011802 < baseStart_4011802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011890 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_4011890 : Nat := 118140960795 + 4011890 * 2 ^ 59
def prefixEnd_4011890 : Nat := 4983230072969 + 3 ^ 40 * 4011890 * 2
def baseEnd_4011890 : Nat := 1373351935310942463749773

theorem tailTrace_4011890 : CollatzResearch.WordTrace tailWord_4011890 prefixEnd_4011890 1373351935310942463749773 := by
  unfold tailWord_4011890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36581412358903795276860281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97550432957076787404960749 36581412358903795276860281)
  ·
    refine ⟨27436059269177846457645211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36581412358903795276860281 27436059269177846457645211)
    ·
      refine ⟨41154088903766769686467817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27436059269177846457645211 41154088903766769686467817)
      ·
        refine ⟨30865566677825077264850863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41154088903766769686467817 30865566677825077264850863)
        ·
          refine ⟨46298350016737615897276295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30865566677825077264850863 46298350016737615897276295)
          ·
            refine ⟨69447525025106423845914443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46298350016737615897276295 69447525025106423845914443)
            ·
              refine ⟨104171287537659635768871665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69447525025106423845914443 104171287537659635768871665)
              ·
                refine ⟨78128465653244726826653749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104171287537659635768871665 78128465653244726826653749)
                ·
                  refine ⟨7324543654991693139998789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78128465653244726826653749 7324543654991693139998789)
                  ·
                    refine ⟨1373351935310942463749773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324543654991693139998789 1373351935310942463749773)
                    ·
                      rfl

theorem cell22_4011890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_4011890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011890 prefixEnd_4011890 := by exact prefixLift 4011890
  have htrace : WordTrace (prefixWord ++ tailWord_4011890) baseStart_4011890 baseEnd_4011890 := by
    simpa [prefixWord, tailWord_4011890, baseEnd_4011890] using wordTrace_append hprefix tailTrace_4011890
  have hstable : (prefixWord ++ tailWord_4011890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011890).length < 2 ^ (prefixWord ++ tailWord_4011890).sum := by decide
  have hdescent : baseEnd_4011890 < baseStart_4011890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011911 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 5]
def baseStart_4011911 : Nat := 118140960795 + 4011911 * 2 ^ 59
def prefixEnd_4011911 : Nat := 4983230072969 + 3 ^ 40 * 4011911 * 2
def baseEnd_4011911 : Nat := 457786374680035136324903

theorem tailTrace_4011911 : CollatzResearch.WordTrace tailWord_4011911 prefixEnd_4011911 457786374680035136324903 := by
  unfold tailWord_4011911
  simp only [CollatzResearch.WordTrace]
  refine ⟨146326415368539101693955587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97550943579026067795970391 146326415368539101693955587)
  ·
    refine ⟨219489623052808652540933381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146326415368539101693955587 219489623052808652540933381)
    ·
      refine ⟨41154304322401622351425009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219489623052808652540933381 41154304322401622351425009)
      ·
        refine ⟨30865728241801216763568757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41154304322401622351425009 30865728241801216763568757)
        ·
          refine ⟨2893662022668864071584571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30865728241801216763568757 2893662022668864071584571)
          ·
            refine ⟨4340493034003296107376857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893662022668864071584571 4340493034003296107376857)
            ·
              refine ⟨3255369775502472080532643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340493034003296107376857 3255369775502472080532643)
              ·
                refine ⟨4883054663253708120798965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255369775502472080532643 4883054663253708120798965)
                ·
                  refine ⟨457786374680035136324903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4883054663253708120798965 457786374680035136324903)
                  ·
                    rfl

theorem cell22_4011911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 5].length) (baseStart_4011911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011911 prefixEnd_4011911 := by exact prefixLift 4011911
  have htrace : WordTrace (prefixWord ++ tailWord_4011911) baseStart_4011911 baseEnd_4011911 := by
    simpa [prefixWord, tailWord_4011911, baseEnd_4011911] using wordTrace_append hprefix tailTrace_4011911
  have hstable : (prefixWord ++ tailWord_4011911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011911).length < 2 ^ (prefixWord ++ tailWord_4011911).sum := by decide
  have hdescent : baseEnd_4011911 < baseStart_4011911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011924 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4011924 : Nat := 118140960795 + 4011924 * 2 ^ 59
def prefixEnd_4011924 : Nat := 4983230072969 + 3 ^ 40 * 4011924 * 2
def baseEnd_4011924 : Nat := 1373363574205777708399669

theorem tailTrace_4011924 : CollatzResearch.WordTrace tailWord_4011924 prefixEnd_4011924 1373363574205777708399669 := by
  unfold tailWord_4011924
  simp only [CollatzResearch.WordTrace]
  refine ⟨73163444758746002457089413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97551259678328003276119217 73163444758746002457089413)
  ·
    refine ⟨13718145892264875460704265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73163444758746002457089413 13718145892264875460704265)
    ·
      refine ⟨10288609419198656595528199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13718145892264875460704265 10288609419198656595528199)
      ·
        refine ⟨15432914128797984893292299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10288609419198656595528199 15432914128797984893292299)
        ·
          refine ⟨23149371193196977339938449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15432914128797984893292299 23149371193196977339938449)
          ·
            refine ⟨17362028394897733004953837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23149371193196977339938449 17362028394897733004953837)
            ·
              refine ⟨6510760648086649876857689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17362028394897733004953837 6510760648086649876857689)
              ·
                refine ⟨4883070486064987407643267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510760648086649876857689 4883070486064987407643267)
                ·
                  refine ⟨7324605729097481111464901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883070486064987407643267 7324605729097481111464901)
                  ·
                    refine ⟨1373363574205777708399669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324605729097481111464901 1373363574205777708399669)
                    ·
                      rfl

theorem cell22_4011924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4011924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011924 prefixEnd_4011924 := by exact prefixLift 4011924
  have htrace : WordTrace (prefixWord ++ tailWord_4011924) baseStart_4011924 baseEnd_4011924 := by
    simpa [prefixWord, tailWord_4011924, baseEnd_4011924] using wordTrace_append hprefix tailTrace_4011924
  have hstable : (prefixWord ++ tailWord_4011924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011924).length < 2 ^ (prefixWord ++ tailWord_4011924).sum := by decide
  have hdescent : baseEnd_4011924 < baseStart_4011924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011986 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_4011986 : Nat := 118140960795 + 4011986 * 2 ^ 59
def prefixEnd_4011986 : Nat := 4983230072969 + 3 ^ 40 * 4011986 * 2
def baseEnd_4011986 : Nat := 1373384798072830213349479

theorem tailTrace_4011986 : CollatzResearch.WordTrace tailWord_4011986 prefixEnd_4011986 1373384798072830213349479 := by
  unfold tailWord_4011986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582287710816847375733953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97552767228844926335290541 36582287710816847375733953)
  ·
    refine ⟨27436715783112635531800465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36582287710816847375733953 27436715783112635531800465)
    ·
      refine ⟨20577536837334476648850349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27436715783112635531800465 20577536837334476648850349)
      ·
        refine ⟨7716576314000428743318881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20577536837334476648850349 7716576314000428743318881)
        ·
          refine ⟨5787432235500321557489161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7716576314000428743318881 5787432235500321557489161)
          ·
            refine ⟨4340574176625241168116871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787432235500321557489161 4340574176625241168116871)
            ·
              refine ⟨6510861264937861752175307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340574176625241168116871 6510861264937861752175307)
              ·
                refine ⟨9766291897406792628262961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510861264937861752175307 9766291897406792628262961)
                ·
                  refine ⟨7324718923055094471197221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766291897406792628262961 7324718923055094471197221)
                  ·
                    refine ⟨1373384798072830213349479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324718923055094471197221 1373384798072830213349479)
                    ·
                      rfl

theorem cell22_4011986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_4011986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4011986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4011986 prefixEnd_4011986 := by exact prefixLift 4011986
  have htrace : WordTrace (prefixWord ++ tailWord_4011986) baseStart_4011986 baseEnd_4011986 := by
    simpa [prefixWord, tailWord_4011986, baseEnd_4011986] using wordTrace_append hprefix tailTrace_4011986
  have hstable : (prefixWord ++ tailWord_4011986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011986).length < 2 ^ (prefixWord ++ tailWord_4011986).sum := by decide
  have hdescent : baseEnd_4011986 < baseStart_4011986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012074 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_4012074 : Nat := 118140960795 + 4012074 * 2 ^ 59
def prefixEnd_4012074 : Nat := 4983230072969 + 3 ^ 40 * 4012074 * 2
def baseEnd_4012074 : Nat := 457804974090409105716403

theorem tailTrace_4012074 : CollatzResearch.WordTrace tailWord_4012074 prefixEnd_4012074 457804974090409105716403 := by
  unfold tailWord_4012074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583090116737145133034819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97554906977965720354759517 36583090116737145133034819)
  ·
    refine ⟨54874635175105717699552229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36583090116737145133034819 54874635175105717699552229)
    ·
      refine ⟨10288994095332322068666043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54874635175105717699552229 10288994095332322068666043)
      ·
        refine ⟨15433491142998483102999065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10288994095332322068666043 15433491142998483102999065)
        ·
          refine ⟨11575118357248862327249299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15433491142998483102999065 11575118357248862327249299)
          ·
            refine ⟨17362677535873293490873949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11575118357248862327249299 17362677535873293490873949)
            ·
              refine ⟨6511004075952485059077731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17362677535873293490873949 6511004075952485059077731)
              ·
                refine ⟨9766506113928727588616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511004075952485059077731 9766506113928727588616597)
                ·
                  refine ⟨457804974090409105716403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9766506113928727588616597 457804974090409105716403)
                  ·
                    rfl

theorem cell22_4012074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_4012074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012074 prefixEnd_4012074 := by exact prefixLift 4012074
  have htrace : WordTrace (prefixWord ++ tailWord_4012074) baseStart_4012074 baseEnd_4012074 := by
    simpa [prefixWord, tailWord_4012074, baseEnd_4012074] using wordTrace_append hprefix tailTrace_4012074
  have hstable : (prefixWord ++ tailWord_4012074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012074).length < 2 ^ (prefixWord ++ tailWord_4012074).sum := by decide
  have hdescent : baseEnd_4012074 < baseStart_4012074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012125 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 4]
def baseStart_4012125 : Nat := 118140960795 + 4012125 * 2 ^ 59
def prefixEnd_4012125 : Nat := 4983230072969 + 3 ^ 40 * 4012125 * 2
def baseEnd_4012125 : Nat := 457810793537826728041351

theorem tailTrace_4012125 : CollatzResearch.WordTrace tailWord_4012125 prefixEnd_4012125 457810793537826728041351 := by
  unfold tailWord_4012125
  simp only [CollatzResearch.WordTrace]
  refine ⟨146334220589763816242245829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97556147059842544161497219 146334220589763816242245829)
  ·
    refine ⟨27437666360580715545421093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146334220589763816242245829 27437666360580715545421093)
    ·
      refine ⟨5144562442608884164766455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27437666360580715545421093 5144562442608884164766455)
      ·
        refine ⟨7716843663913326247149683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144562442608884164766455 7716843663913326247149683)
        ·
          refine ⟨11575265495869989370724525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716843663913326247149683 11575265495869989370724525)
          ·
            refine ⟨4340724560951246014021697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11575265495869989370724525 4340724560951246014021697)
            ·
              refine ⟨3255543420713434510516273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340724560951246014021697 3255543420713434510516273)
              ·
                refine ⟨2441657565535075882887205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255543420713434510516273 2441657565535075882887205)
                ·
                  refine ⟨457810793537826728041351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441657565535075882887205 457810793537826728041351)
                  ·
                    rfl

theorem cell22_4012125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_4012125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012125 prefixEnd_4012125 := by exact prefixLift 4012125
  have htrace : WordTrace (prefixWord ++ tailWord_4012125) baseStart_4012125 baseEnd_4012125 := by
    simpa [prefixWord, tailWord_4012125, baseEnd_4012125] using wordTrace_append hprefix tailTrace_4012125
  have hstable : (prefixWord ++ tailWord_4012125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012125).length < 2 ^ (prefixWord ++ tailWord_4012125).sum := by decide
  have hdescent : baseEnd_4012125 < baseStart_4012125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012132 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4012132 : Nat := 118140960795 + 4012132 * 2 ^ 59
def prefixEnd_4012132 : Nat := 4983230072969 + 3 ^ 40 * 4012132 * 2
def baseEnd_4012132 : Nat := 1373434776856534499199031

theorem tailTrace_4012132 : CollatzResearch.WordTrace tailWord_4012132 prefixEnd_4012132 1373434776856534499199031 := by
  unfold tailWord_4012132
  simp only [CollatzResearch.WordTrace]
  refine ⟨73167237950369228218875325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97556317267158970958500433 73167237950369228218875325)
  ·
    refine ⟨27437714231388460582078247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73167237950369228218875325 27437714231388460582078247)
    ·
      refine ⟨41156571347082690873117371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27437714231388460582078247 41156571347082690873117371)
      ·
        refine ⟨61734857020624036309676057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41156571347082690873117371 61734857020624036309676057)
        ·
          refine ⟨46301142765468027232257043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61734857020624036309676057 46301142765468027232257043)
          ·
            refine ⟨69451714148202040848385565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46301142765468027232257043 69451714148202040848385565)
            ·
              refine ⟨26044392805575765318144587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69451714148202040848385565 26044392805575765318144587)
              ·
                refine ⟨39066589208363647977216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26044392805575765318144587 39066589208363647977216881)
                ·
                  refine ⟨29299941906272735982912661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39066589208363647977216881 29299941906272735982912661)
                  ·
                    refine ⟨1373434776856534499199031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29299941906272735982912661 1373434776856534499199031)
                    ·
                      rfl

theorem cell22_4012132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4012132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012132 prefixEnd_4012132 := by exact prefixLift 4012132
  have htrace : WordTrace (prefixWord ++ tailWord_4012132) baseStart_4012132 baseEnd_4012132 := by
    simpa [prefixWord, tailWord_4012132, baseEnd_4012132] using wordTrace_append hprefix tailTrace_4012132
  have hstable : (prefixWord ++ tailWord_4012132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012132).length < 2 ^ (prefixWord ++ tailWord_4012132).sum := by decide
  have hdescent : baseEnd_4012132 < baseStart_4012132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012168 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 1, 3]
def baseStart_4012168 : Nat := 118140960795 + 4012168 * 2 ^ 59
def prefixEnd_4012168 : Nat := 4983230072969 + 3 ^ 40 * 4012168 * 2
def baseEnd_4012168 : Nat := 1373447100392242405298921

theorem tailTrace_4012168 : CollatzResearch.WordTrace tailWord_4012168 prefixEnd_4012168 1373447100392242405298921 := by
  unfold tailWord_4012168
  simp only [CollatzResearch.WordTrace]
  refine ⟨73167894464304017293030579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97557192619072023057374105 73167894464304017293030579)
  ·
    refine ⟨109751841696456025939545869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73167894464304017293030579 109751841696456025939545869)
    ·
      refine ⟨41156940636171009727329701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109751841696456025939545869 41156940636171009727329701)
      ·
        refine ⟨7716926369282064323874319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41156940636171009727329701 7716926369282064323874319)
        ·
          refine ⟨11575389553923096485811479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716926369282064323874319 11575389553923096485811479)
          ·
            refine ⟨17363084330884644728717219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11575389553923096485811479 17363084330884644728717219)
            ·
              refine ⟨26044626496326967093075829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17363084330884644728717219 26044626496326967093075829)
              ·
                refine ⟨2441683734030653164975859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26044626496326967093075829 2441683734030653164975859)
                ·
                  refine ⟨3662525601045979747463789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441683734030653164975859 3662525601045979747463789)
                  ·
                    refine ⟨1373447100392242405298921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3662525601045979747463789 1373447100392242405298921)
                    ·
                      rfl

theorem cell22_4012168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_4012168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012168 prefixEnd_4012168 := by exact prefixLift 4012168
  have htrace : WordTrace (prefixWord ++ tailWord_4012168) baseStart_4012168 baseEnd_4012168 := by
    simpa [prefixWord, tailWord_4012168, baseEnd_4012168] using wordTrace_append hprefix tailTrace_4012168
  have hstable : (prefixWord ++ tailWord_4012168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012168).length < 2 ^ (prefixWord ++ tailWord_4012168).sum := by decide
  have hdescent : baseEnd_4012168 < baseStart_4012168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012239 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_4012239 : Nat := 118140960795 + 4012239 * 2 ^ 59
def prefixEnd_4012239 : Nat := 4983230072969 + 3 ^ 40 * 4012239 * 2
def baseEnd_4012239 : Nat := 1373471405143221886773703

theorem tailTrace_4012239 : CollatzResearch.WordTrace tailWord_4012239 prefixEnd_4012239 1373471405143221886773703 := by
  unfold tailWord_4012239
  simp only [CollatzResearch.WordTrace]
  refine ⟨146338378511350813711895771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97558919007567209141263847 146338378511350813711895771)
  ·
    refine ⟨219507567767026220567843657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146338378511350813711895771 219507567767026220567843657)
    ·
      refine ⟨164630675825269665425882743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219507567767026220567843657 164630675825269665425882743)
      ·
        refine ⟨246946013737904498138824115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164630675825269665425882743 246946013737904498138824115)
        ·
          refine ⟨370419020606856747208236173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246946013737904498138824115 370419020606856747208236173)
          ·
            refine ⟨138907132727571280203088565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370419020606856747208236173 138907132727571280203088565)
            ·
              refine ⟨13022543693209807519039553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138907132727571280203088565 13022543693209807519039553)
              ·
                refine ⟨9766907769907355639279665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13022543693209807519039553 9766907769907355639279665)
                ·
                  refine ⟨7325180827430516729459749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766907769907355639279665 7325180827430516729459749)
                  ·
                    refine ⟨1373471405143221886773703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7325180827430516729459749 1373471405143221886773703)
                    ·
                      rfl

theorem cell22_4012239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_4012239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012239 prefixEnd_4012239 := by exact prefixLift 4012239
  have htrace : WordTrace (prefixWord ++ tailWord_4012239) baseStart_4012239 baseEnd_4012239 := by
    simpa [prefixWord, tailWord_4012239, baseEnd_4012239] using wordTrace_append hprefix tailTrace_4012239
  have hstable : (prefixWord ++ tailWord_4012239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012239).length < 2 ^ (prefixWord ++ tailWord_4012239).sum := by decide
  have hdescent : baseEnd_4012239 < baseStart_4012239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012391 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_4012391 : Nat := 118140960795 + 4012391 * 2 ^ 59
def prefixEnd_4012391 : Nat := 4983230072969 + 3 ^ 40 * 4012391 * 2
def baseEnd_4012391 : Nat := 1373523437849544156973237

theorem tailTrace_4012391 : CollatzResearch.WordTrace tailWord_4012391 prefixEnd_4012391 1373523437849544156973237 := by
  unfold tailWord_4012391
  simp only [CollatzResearch.WordTrace]
  refine ⟨146343922406800143671429027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97562614937866762447619351 146343922406800143671429027)
  ·
    refine ⟨219515883610200215507143541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146343922406800143671429027 219515883610200215507143541)
    ·
      refine ⟨20579614088456270203794707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219515883610200215507143541 20579614088456270203794707)
      ·
        refine ⟨30869421132684405305692061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20579614088456270203794707 30869421132684405305692061)
        ·
          refine ⟨11576032924756651989634523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30869421132684405305692061 11576032924756651989634523)
          ·
            refine ⟨17364049387134977984451785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576032924756651989634523 17364049387134977984451785)
            ·
              refine ⟨13023037040351233488338839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17364049387134977984451785 13023037040351233488338839)
              ·
                refine ⟨19534555560526850232508259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023037040351233488338839 19534555560526850232508259)
                ·
                  refine ⟨29301833340790275348762389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19534555560526850232508259 29301833340790275348762389)
                  ·
                    refine ⟨1373523437849544156973237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29301833340790275348762389 1373523437849544156973237)
                    ·
                      rfl

theorem cell22_4012391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_4012391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012391 prefixEnd_4012391 := by exact prefixLift 4012391
  have htrace : WordTrace (prefixWord ++ tailWord_4012391) baseStart_4012391 baseEnd_4012391 := by
    simpa [prefixWord, tailWord_4012391, baseEnd_4012391] using wordTrace_append hprefix tailTrace_4012391
  have hstable : (prefixWord ++ tailWord_4012391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012391).length < 2 ^ (prefixWord ++ tailWord_4012391).sum := by decide
  have hdescent : baseEnd_4012391 < baseStart_4012391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012466 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_4012466 : Nat := 118140960795 + 4012466 * 2 ^ 59
def prefixEnd_4012466 : Nat := 4983230072969 + 3 ^ 40 * 4012466 * 2
def baseEnd_4012466 : Nat := 1373549111882268961348007

theorem tailTrace_4012466 : CollatzResearch.WordTrace tailWord_4012466 prefixEnd_4012466 1373549111882268961348007 := by
  unfold tailWord_4012466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36586664470382107870102313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97564438587685620986939501 36586664470382107870102313)
  ·
    refine ⟨27439998352786580902576735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36586664470382107870102313 27439998352786580902576735)
    ·
      refine ⟨41159997529179871353865103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27439998352786580902576735 41159997529179871353865103)
      ·
        refine ⟨61739996293769807030797655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41159997529179871353865103 61739996293769807030797655)
        ·
          refine ⟨92609994440654710546196483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61739996293769807030797655 92609994440654710546196483)
          ·
            refine ⟨138914991660982065819294725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92609994440654710546196483 138914991660982065819294725)
            ·
              refine ⟨26046560936434137341117761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138914991660982065819294725 26046560936434137341117761)
              ·
                refine ⟨19534920702325603005838321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26046560936434137341117761 19534920702325603005838321)
                ·
                  refine ⟨14651190526744202254378741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19534920702325603005838321 14651190526744202254378741)
                  ·
                    refine ⟨1373549111882268961348007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14651190526744202254378741 1373549111882268961348007)
                    ·
                      rfl

theorem cell22_4012466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_4012466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012466 prefixEnd_4012466 := by exact prefixLift 4012466
  have htrace : WordTrace (prefixWord ++ tailWord_4012466) baseStart_4012466 baseEnd_4012466 := by
    simpa [prefixWord, tailWord_4012466, baseEnd_4012466] using wordTrace_append hprefix tailTrace_4012466
  have hstable : (prefixWord ++ tailWord_4012466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012466).length < 2 ^ (prefixWord ++ tailWord_4012466).sum := by decide
  have hdescent : baseEnd_4012466 < baseStart_4012466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012515 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 1, 4]
def baseStart_4012515 : Nat := 118140960795 + 4012515 * 2 ^ 59
def prefixEnd_4012515 : Nat := 4983230072969 + 3 ^ 40 * 4012515 * 2
def baseEnd_4012515 : Nat := 1373565885583649166872857

theorem tailTrace_4012515 : CollatzResearch.WordTrace tailWord_4012515 prefixEnd_4012515 1373565885583649166872857 := by
  unfold tailWord_4012515
  simp only [CollatzResearch.WordTrace]
  refine ⟨146348445058350912848942999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97565630038900608565961999 146348445058350912848942999)
  ·
    refine ⟨219522667587526369273414499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146348445058350912848942999 219522667587526369273414499)
    ·
      refine ⟨329284001381289553910121749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219522667587526369273414499 329284001381289553910121749)
      ·
        refine ⟨15435187564747947839536957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 329284001381289553910121749 15435187564747947839536957)
        ·
          refine ⟨5788195336780480439826359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15435187564747947839536957 5788195336780480439826359)
          ·
            refine ⟨8682293005170720659739539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788195336780480439826359 8682293005170720659739539)
            ·
              refine ⟨13023439507756080989609309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682293005170720659739539 13023439507756080989609309)
              ·
                refine ⟨4883789815408530371103491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13023439507756080989609309 4883789815408530371103491)
                ·
                  refine ⟨7325684723112795556655237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883789815408530371103491 7325684723112795556655237)
                  ·
                    refine ⟨1373565885583649166872857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7325684723112795556655237 1373565885583649166872857)
                    ·
                      rfl

theorem cell22_4012515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4].length) (baseStart_4012515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012515 prefixEnd_4012515 := by exact prefixLift 4012515
  have htrace : WordTrace (prefixWord ++ tailWord_4012515) baseStart_4012515 baseEnd_4012515 := by
    simpa [prefixWord, tailWord_4012515, baseEnd_4012515] using wordTrace_append hprefix tailTrace_4012515
  have hstable : (prefixWord ++ tailWord_4012515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012515).length < 2 ^ (prefixWord ++ tailWord_4012515).sum := by decide
  have hdescent : baseEnd_4012515 < baseStart_4012515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012528 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_4012528 : Nat := 118140960795 + 4012528 * 2 ^ 59
def prefixEnd_4012528 : Nat := 4983230072969 + 3 ^ 40 * 4012528 * 2
def baseEnd_4012528 : Nat := 1373570335749321466297817

theorem tailTrace_4012528 : CollatzResearch.WordTrace tailWord_4012528 prefixEnd_4012528 1373570335749321466297817 := by
  unfold tailWord_4012528
  simp only [CollatzResearch.WordTrace]
  refine ⟨73174459603651908034583119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97565946138202544046110825 73174459603651908034583119)
  ·
    refine ⟨109761689405477862051874679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73174459603651908034583119 109761689405477862051874679)
    ·
      refine ⟨164642534108216793077812019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109761689405477862051874679 164642534108216793077812019)
      ·
        refine ⟨246963801162325189616718029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164642534108216793077812019 246963801162325189616718029)
        ·
          refine ⟨92611425435871946106269261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246963801162325189616718029 92611425435871946106269261)
          ·
            refine ⟨34729284538451979789850973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92611425435871946106269261 34729284538451979789850973)
            ·
              refine ⟨13023481701919492421194115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34729284538451979789850973 13023481701919492421194115)
              ·
                refine ⟨19535222552879238631791173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023481701919492421194115 19535222552879238631791173)
                ·
                  refine ⟨3662854228664857243460845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19535222552879238631791173 3662854228664857243460845)
                  ·
                    refine ⟨1373570335749321466297817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3662854228664857243460845 1373570335749321466297817)
                    ·
                      rfl

theorem cell22_4012528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_4012528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012528 prefixEnd_4012528 := by exact prefixLift 4012528
  have htrace : WordTrace (prefixWord ++ tailWord_4012528) baseStart_4012528 baseEnd_4012528 := by
    simpa [prefixWord, tailWord_4012528, baseEnd_4012528] using wordTrace_append hprefix tailTrace_4012528
  have hstable : (prefixWord ++ tailWord_4012528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012528).length < 2 ^ (prefixWord ++ tailWord_4012528).sum := by decide
  have hdescent : baseEnd_4012528 < baseStart_4012528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012530 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_4012530 : Nat := 118140960795 + 4012530 * 2 ^ 59
def prefixEnd_4012530 : Nat := 4983230072969 + 3 ^ 40 * 4012530 * 2
def baseEnd_4012530 : Nat := 457857006796731375915937

theorem tailTrace_4012530 : CollatzResearch.WordTrace tailWord_4012530 prefixEnd_4012530 457857006796731375915937 := by
  unfold tailWord_4012530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36587248038324142602684761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97565994768864380273826029 36587248038324142602684761)
  ·
    refine ⟨27440436028743106952013571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36587248038324142602684761 27440436028743106952013571)
    ·
      refine ⟨41160654043114660428020357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440436028743106952013571 41160654043114660428020357)
      ·
        refine ⟨7717622633083998830253817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41160654043114660428020357 7717622633083998830253817)
        ·
          refine ⟨5788216974812999122690363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7717622633083998830253817 5788216974812999122690363)
          ·
            refine ⟨8682325462219498684035545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788216974812999122690363 8682325462219498684035545)
            ·
              refine ⟨6511744096664624013026659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8682325462219498684035545 6511744096664624013026659)
              ·
                refine ⟨9767616144996936019539989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511744096664624013026659 9767616144996936019539989)
                ·
                  refine ⟨457857006796731375915937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9767616144996936019539989 457857006796731375915937)
                  ·
                    rfl

theorem cell22_4012530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_4012530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012530 prefixEnd_4012530 := by exact prefixLift 4012530
  have htrace : WordTrace (prefixWord ++ tailWord_4012530) baseStart_4012530 baseEnd_4012530 := by
    simpa [prefixWord, tailWord_4012530, baseEnd_4012530] using wordTrace_append hprefix tailTrace_4012530
  have hstable : (prefixWord ++ tailWord_4012530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012530).length < 2 ^ (prefixWord ++ tailWord_4012530).sum := by decide
  have hdescent : baseEnd_4012530 < baseStart_4012530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012541 : List Nat := [1, 4, 1, 1, 1, 3, 2, 9]
def baseStart_4012541 : Nat := 118140960795 + 4012541 * 2 ^ 59
def prefixEnd_4012541 : Nat := 4983230072969 + 3 ^ 40 * 4012541 * 2
def baseEnd_4012541 : Nat := 152619420657221529524753

theorem tailTrace_4012541 : CollatzResearch.WordTrace tailWord_4012541 prefixEnd_4012541 152619420657221529524753 := by
  unfold tailWord_4012541
  simp only [CollatzResearch.WordTrace]
  refine ⟨146349393356256719289389477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97566262237504479526259651 146349393356256719289389477)
  ·
    refine ⟨27440511254298134866760527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146349393356256719289389477 27440511254298134866760527)
    ·
      refine ⟨41160766881447202300140791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440511254298134866760527 41160766881447202300140791)
      ·
        refine ⟨61741150322170803450211187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41160766881447202300140791 61741150322170803450211187)
        ·
          refine ⟨92611725483256205175316781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61741150322170803450211187 92611725483256205175316781)
          ·
            refine ⟨34729397056221076940743793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92611725483256205175316781 34729397056221076940743793)
            ·
              refine ⟨26047047792165807705557845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34729397056221076940743793 26047047792165807705557845)
              ·
                refine ⟨152619420657221529524753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26047047792165807705557845 152619420657221529524753)
                ·
                  rfl

theorem cell22_4012541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 9].length) (baseStart_4012541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012541 prefixEnd_4012541 := by exact prefixLift 4012541
  have htrace : WordTrace (prefixWord ++ tailWord_4012541) baseStart_4012541 baseEnd_4012541 := by
    simpa [prefixWord, tailWord_4012541, baseEnd_4012541] using wordTrace_append hprefix tailTrace_4012541
  have hstable : (prefixWord ++ tailWord_4012541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012541).length < 2 ^ (prefixWord ++ tailWord_4012541).sum := by decide
  have hdescent : baseEnd_4012541 < baseStart_4012541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012545 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4012545 : Nat := 118140960795 + 4012545 * 2 ^ 59
def prefixEnd_4012545 : Nat := 4983230072969 + 3 ^ 40 * 4012545 * 2
def baseEnd_4012545 : Nat := 1373576155196739088622765

theorem tailTrace_4012545 : CollatzResearch.WordTrace tailWord_4012545 prefixEnd_4012545 1373576155196739088622765 := by
  unfold tailWord_4012545
  simp only [CollatzResearch.WordTrace]
  refine ⟨146349539248242227972535089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97566359498828151981690059 146349539248242227972535089)
  ·
    refine ⟨109762154436181670979401317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146349539248242227972535089 109762154436181670979401317)
    ·
      refine ⟨20580403956784063308637747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109762154436181670979401317 20580403956784063308637747)
      ·
        refine ⟨30870605935176094962956621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580403956784063308637747 30870605935176094962956621)
        ·
          refine ⟨11576477225691035611108733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30870605935176094962956621 11576477225691035611108733)
          ·
            refine ⟨4341178959634138354165775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11576477225691035611108733 4341178959634138354165775)
            ·
              refine ⟨6511768439451207531248663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341178959634138354165775 6511768439451207531248663)
              ·
                refine ⟨9767652659176811296872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511768439451207531248663 9767652659176811296872995)
                ·
                  refine ⟨14651478988765216945309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767652659176811296872995 14651478988765216945309493)
                  ·
                    refine ⟨1373576155196739088622765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14651478988765216945309493 1373576155196739088622765)
                    ·
                      rfl

theorem cell22_4012545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4012545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012545 prefixEnd_4012545 := by exact prefixLift 4012545
  have htrace : WordTrace (prefixWord ++ tailWord_4012545) baseStart_4012545 baseEnd_4012545 := by
    simpa [prefixWord, tailWord_4012545, baseEnd_4012545] using wordTrace_append hprefix tailTrace_4012545
  have hstable : (prefixWord ++ tailWord_4012545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012545).length < 2 ^ (prefixWord ++ tailWord_4012545).sum := by decide
  have hdescent : baseEnd_4012545 < baseStart_4012545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012558 : List Nat := [4, 1, 1, 2, 3, 2, 1, 8]
def baseStart_4012558 : Nat := 118140960795 + 4012558 * 2 ^ 59
def prefixEnd_4012558 : Nat := 4983230072969 + 3 ^ 40 * 4012558 * 2
def baseEnd_4012558 : Nat := 152620067262490154227525

theorem tailTrace_4012558 : CollatzResearch.WordTrace tailWord_4012558 prefixEnd_4012558 152620067262490154227525 := by
  unfold tailWord_4012558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293751674649391399094791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97566675598130087461838885 18293751674649391399094791)
  ·
    refine ⟨27440627511974087098642187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293751674649391399094791 27440627511974087098642187)
    ·
      refine ⟨41160941267961130647963281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440627511974087098642187 41160941267961130647963281)
      ·
        refine ⟨30870705950970847985972461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41160941267961130647963281 30870705950970847985972461)
        ·
          refine ⟨11576514731614067994739673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30870705950970847985972461 11576514731614067994739673)
          ·
            refine ⟨8682386048710550996054755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11576514731614067994739673 8682386048710550996054755)
            ·
              refine ⟨13023579073065826494082133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682386048710550996054755 13023579073065826494082133)
              ·
                refine ⟨152620067262490154227525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13023579073065826494082133 152620067262490154227525)
                ·
                  rfl

theorem cell22_4012558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_4012558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012558 prefixEnd_4012558 := by exact prefixLift 4012558
  have htrace : WordTrace (prefixWord ++ tailWord_4012558) baseStart_4012558 baseEnd_4012558 := by
    simpa [prefixWord, tailWord_4012558, baseEnd_4012558] using wordTrace_append hprefix tailTrace_4012558
  have hstable : (prefixWord ++ tailWord_4012558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012558).length < 2 ^ (prefixWord ++ tailWord_4012558).sum := by decide
  have hdescent : baseEnd_4012558 < baseStart_4012558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012564 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4012564 : Nat := 118140960795 + 4012564 * 2 ^ 59
def prefixEnd_4012564 : Nat := 4983230072969 + 3 ^ 40 * 4012564 * 2
def baseEnd_4012564 : Nat := 457860886428343124132569

theorem tailTrace_4012564 : CollatzResearch.WordTrace tailWord_4012564 prefixEnd_4012564 457860886428343124132569 := by
  unfold tailWord_4012564
  simp only [CollatzResearch.WordTrace]
  refine ⟨73175116117586697108738373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97566821490115596144984497 73175116117586697108738373)
  ·
    refine ⟨13720334272047505707888445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73175116117586697108738373 13720334272047505707888445)
    ·
      refine ⟨5145125352017814640458167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13720334272047505707888445 5145125352017814640458167)
      ·
        refine ⟨7717688028026721960687251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145125352017814640458167 7717688028026721960687251)
        ·
          refine ⟨11576532042040082941030877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717688028026721960687251 11576532042040082941030877)
          ·
            refine ⟨4341199515765031102886579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11576532042040082941030877 4341199515765031102886579)
            ·
              refine ⟨6511799273647546654329869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341199515765031102886579 6511799273647546654329869)
              ·
                refine ⟨2441924727617829995373701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6511799273647546654329869 2441924727617829995373701)
                ·
                  refine ⟨457860886428343124132569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441924727617829995373701 457860886428343124132569)
                  ·
                    rfl

theorem cell22_4012564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4012564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012564 prefixEnd_4012564 := by exact prefixLift 4012564
  have htrace : WordTrace (prefixWord ++ tailWord_4012564) baseStart_4012564 baseEnd_4012564 := by
    simpa [prefixWord, tailWord_4012564, baseEnd_4012564] using wordTrace_append hprefix tailTrace_4012564
  have hstable : (prefixWord ++ tailWord_4012564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012564).length < 2 ^ (prefixWord ++ tailWord_4012564).sum := by decide
  have hdescent : baseEnd_4012564 < baseStart_4012564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012663 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_4012663 : Nat := 118140960795 + 4012663 * 2 ^ 59
def prefixEnd_4012663 : Nat := 4983230072969 + 3 ^ 40 * 4012663 * 2
def baseEnd_4012663 : Nat := 1373616549008226114172403

theorem tailTrace_4012663 : CollatzResearch.WordTrace tailWord_4012663 prefixEnd_4012663 1373616549008226114172403 := by
  unfold tailWord_4012663
  simp only [CollatzResearch.WordTrace]
  refine ⟨146353843061814734125330643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97569228707876489416887095 146353843061814734125330643)
  ·
    refine ⟨219530764592722101187995965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146353843061814734125330643 219530764592722101187995965)
    ·
      refine ⟨82324036722270787945498487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219530764592722101187995965 82324036722270787945498487)
      ·
        refine ⟨123486055083406181918247731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82324036722270787945498487 123486055083406181918247731)
        ·
          refine ⟨185229082625109272877371597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123486055083406181918247731 185229082625109272877371597)
          ·
            refine ⟨69460905984415977329014349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185229082625109272877371597 69460905984415977329014349)
            ·
              refine ⟨26047839744155991498380381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69460905984415977329014349 26047839744155991498380381)
              ·
                refine ⟨9767939904058496811892643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26047839744155991498380381 9767939904058496811892643)
                ·
                  refine ⟨14651909856087745217838965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767939904058496811892643 14651909856087745217838965)
                  ·
                    refine ⟨1373616549008226114172403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14651909856087745217838965 1373616549008226114172403)
                    ·
                      rfl

theorem cell22_4012663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_4012663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012663 prefixEnd_4012663 := by exact prefixLift 4012663
  have htrace : WordTrace (prefixWord ++ tailWord_4012663) baseStart_4012663 baseEnd_4012663 := by
    simpa [prefixWord, tailWord_4012663, baseEnd_4012663] using wordTrace_append hprefix tailTrace_4012663
  have hstable : (prefixWord ++ tailWord_4012663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012663).length < 2 ^ (prefixWord ++ tailWord_4012663).sum := by decide
  have hdescent : baseEnd_4012663 < baseStart_4012663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012727 : List Nat := [1, 1, 3, 1, 6, 2, 2, 6]
def baseStart_4012727 : Nat := 118140960795 + 4012727 * 2 ^ 59
def prefixEnd_4012727 : Nat := 4983230072969 + 3 ^ 40 * 4012727 * 2
def baseEnd_4012727 : Nat := 152626495279572364508023

theorem tailTrace_4012727 : CollatzResearch.WordTrace tailWord_4012727 prefixEnd_4012727 152626495279572364508023 := by
  unfold tailWord_4012727
  simp only [CollatzResearch.WordTrace]
  refine ⟨146356177333582873055660435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97570784889055248703773623 146356177333582873055660435)
  ·
    refine ⟨219534266000374309583490653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146356177333582873055660435 219534266000374309583490653)
    ·
      refine ⟨82325349750140366093808995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219534266000374309583490653 82325349750140366093808995)
      ·
        refine ⟨123488024625210549140713493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82325349750140366093808995 123488024625210549140713493)
        ·
          refine ⟨5788501154306744490970945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123488024625210549140713493 5788501154306744490970945)
          ·
            refine ⟨4341375865730058368228209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5788501154306744490970945 4341375865730058368228209)
            ·
              refine ⟨3256031899297543776171157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4341375865730058368228209 3256031899297543776171157)
              ·
                refine ⟨152626495279572364508023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3256031899297543776171157 152626495279572364508023)
                ·
                  rfl

theorem cell22_4012727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 6].length) (baseStart_4012727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012727 prefixEnd_4012727 := by exact prefixLift 4012727
  have htrace : WordTrace (prefixWord ++ tailWord_4012727) baseStart_4012727 baseEnd_4012727 := by
    simpa [prefixWord, tailWord_4012727, baseEnd_4012727] using wordTrace_append hprefix tailTrace_4012727
  have hstable : (prefixWord ++ tailWord_4012727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012727).length < 2 ^ (prefixWord ++ tailWord_4012727).sum := by decide
  have hdescent : baseEnd_4012727 < baseStart_4012727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012768 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_4012768 : Nat := 118140960795 + 4012768 * 2 ^ 59
def prefixEnd_4012768 : Nat := 4983230072969 + 3 ^ 40 * 4012768 * 2
def baseEnd_4012768 : Nat := 1373652492654040840297081

theorem tailTrace_4012768 : CollatzResearch.WordTrace tailWord_4012768 prefixEnd_4012768 1373652492654040840297081 := by
  unfold tailWord_4012768
  simp only [CollatzResearch.WordTrace]
  refine ⟨73178836363217168528951479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97571781817622891371935305 73178836363217168528951479)
  ·
    refine ⟨109768254544825752793427219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73178836363217168528951479 109768254544825752793427219)
    ·
      refine ⟨164652381817238629190140829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109768254544825752793427219 164652381817238629190140829)
      ·
        refine ⟨61744643181464485946302811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164652381817238629190140829 61744643181464485946302811)
        ·
          refine ⟨92616964772196728919454217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61744643181464485946302811 92616964772196728919454217)
          ·
            refine ⟨69462723579147546689590663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92616964772196728919454217 69462723579147546689590663)
            ·
              refine ⟨104194085368721320034385995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69462723579147546689590663 104194085368721320034385995)
              ·
                refine ⟨156291128053081980051578993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104194085368721320034385995 156291128053081980051578993)
                ·
                  refine ⟨117218346039811485038684245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156291128053081980051578993 117218346039811485038684245)
                  ·
                    refine ⟨1373652492654040840297081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117218346039811485038684245 1373652492654040840297081)
                    ·
                      rfl

theorem cell22_4012768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_4012768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012768 prefixEnd_4012768 := by exact prefixLift 4012768
  have htrace : WordTrace (prefixWord ++ tailWord_4012768) baseStart_4012768 baseEnd_4012768 := by
    simpa [prefixWord, tailWord_4012768, baseEnd_4012768] using wordTrace_append hprefix tailTrace_4012768
  have hstable : (prefixWord ++ tailWord_4012768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012768).length < 2 ^ (prefixWord ++ tailWord_4012768).sum := by decide
  have hdescent : baseEnd_4012768 < baseStart_4012768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012772 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_4012772 : Nat := 118140960795 + 4012772 * 2 ^ 59
def prefixEnd_4012772 : Nat := 4983230072969 + 3 ^ 40 * 4012772 * 2
def baseEnd_4012772 : Nat := 457884620645262054399023

theorem tailTrace_4012772 : CollatzResearch.WordTrace tailWord_4012772 prefixEnd_4012772 457884620645262054399023 := by
  unfold tailWord_4012772
  simp only [CollatzResearch.WordTrace]
  refine ⟨73178909309209922870524285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97571879078946563827365713 73178909309209922870524285)
  ·
    refine ⟨27442090990953721076446607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73178909309209922870524285 27442090990953721076446607)
    ·
      refine ⟨41163136486430581614669911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27442090990953721076446607 41163136486430581614669911)
      ·
        refine ⟨61744704729645872422004867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41163136486430581614669911 61744704729645872422004867)
        ·
          refine ⟨92617057094468808633007301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61744704729645872422004867 92617057094468808633007301)
          ·
            refine ⟨17365698205212901618688869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92617057094468808633007301 17365698205212901618688869)
            ·
              refine ⟨3256068413477419053504163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17365698205212901618688869 3256068413477419053504163)
              ·
                refine ⟨4884102620216128580256245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256068413477419053504163 4884102620216128580256245)
                ·
                  refine ⟨457884620645262054399023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884102620216128580256245 457884620645262054399023)
                  ·
                    rfl

theorem cell22_4012772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_4012772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012772 prefixEnd_4012772 := by exact prefixLift 4012772
  have htrace : WordTrace (prefixWord ++ tailWord_4012772) baseStart_4012772 baseEnd_4012772 := by
    simpa [prefixWord, tailWord_4012772, baseEnd_4012772] using wordTrace_append hprefix tailTrace_4012772
  have hstable : (prefixWord ++ tailWord_4012772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012772).length < 2 ^ (prefixWord ++ tailWord_4012772).sum := by decide
  have hdescent : baseEnd_4012772 < baseStart_4012772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012785 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_4012785 : Nat := 118140960795 + 4012785 * 2 ^ 59
def prefixEnd_4012785 : Nat := 4983230072969 + 3 ^ 40 * 4012785 * 2
def baseEnd_4012785 : Nat := 1373658312101458462622029

theorem tailTrace_4012785 : CollatzResearch.WordTrace tailWord_4012785 prefixEnd_4012785 1373658312101458462622029 := by
  unfold tailWord_4012785
  simp only [CollatzResearch.WordTrace]
  refine ⟨146358292767372748961271809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97572195178248499307514539 146358292767372748961271809)
  ·
    refine ⟨109768719575529561720953857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146358292767372748961271809 109768719575529561720953857)
    ·
      refine ⟨82326539681647171290715393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109768719575529561720953857 82326539681647171290715393)
      ·
        refine ⟨61744904761235378468036545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82326539681647171290715393 61744904761235378468036545)
        ·
          refine ⟨46308678570926533851027409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61744904761235378468036545 46308678570926533851027409)
          ·
            refine ⟨34731508928194900388270557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46308678570926533851027409 34731508928194900388270557)
            ·
              refine ⟨13024315848073087645601459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34731508928194900388270557 13024315848073087645601459)
              ·
                refine ⟨19536473772109631468402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024315848073087645601459 19536473772109631468402189)
                ·
                  refine ⟨7326177664541111800650821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19536473772109631468402189 7326177664541111800650821)
                  ·
                    refine ⟨1373658312101458462622029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326177664541111800650821 1373658312101458462622029)
                    ·
                      rfl

theorem cell22_4012785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_4012785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012785 prefixEnd_4012785 := by exact prefixLift 4012785
  have htrace : WordTrace (prefixWord ++ tailWord_4012785) baseStart_4012785 baseEnd_4012785 := by
    simpa [prefixWord, tailWord_4012785, baseEnd_4012785] using wordTrace_append hprefix tailTrace_4012785
  have hstable : (prefixWord ++ tailWord_4012785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012785).length < 2 ^ (prefixWord ++ tailWord_4012785).sum := by decide
  have hdescent : baseEnd_4012785 < baseStart_4012785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012832 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_4012832 : Nat := 118140960795 + 4012832 * 2 ^ 59
def prefixEnd_4012832 : Nat := 4983230072969 + 3 ^ 40 * 4012832 * 2
def baseEnd_4012832 : Nat := 1373674401161966006696885

theorem tailTrace_4012832 : CollatzResearch.WordTrace tailWord_4012832 prefixEnd_4012832 1373674401161966006696885 := by
  unfold tailWord_4012832
  simp only [CollatzResearch.WordTrace]
  refine ⟨73180003499101237994116375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97573337998801650658821833 73180003499101237994116375)
  ·
    refine ⟨109770005248651856991174563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73180003499101237994116375 109770005248651856991174563)
    ·
      refine ⟨164655007872977785486761845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109770005248651856991174563 164655007872977785486761845)
      ·
        refine ⟨15436406988091667389383923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164655007872977785486761845 15436406988091667389383923)
        ·
          refine ⟨23154610482137501084075885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15436406988091667389383923 23154610482137501084075885)
          ·
            refine ⟨8682978930801562906528457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23154610482137501084075885 8682978930801562906528457)
            ·
              refine ⟨6512234198101172179896343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8682978930801562906528457 6512234198101172179896343)
              ·
                refine ⟨9768351297151758269844515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512234198101172179896343 9768351297151758269844515)
                ·
                  refine ⟨14652526945727637404766773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9768351297151758269844515 14652526945727637404766773)
                  ·
                    refine ⟨1373674401161966006696885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14652526945727637404766773 1373674401161966006696885)
                    ·
                      rfl

theorem cell22_4012832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_4012832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012832 prefixEnd_4012832 := by exact prefixLift 4012832
  have htrace : WordTrace (prefixWord ++ tailWord_4012832) baseStart_4012832 baseEnd_4012832 := by
    simpa [prefixWord, tailWord_4012832, baseEnd_4012832] using wordTrace_append hprefix tailTrace_4012832
  have hstable : (prefixWord ++ tailWord_4012832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012832).length < 2 ^ (prefixWord ++ tailWord_4012832).sum := by decide
  have hdescent : baseEnd_4012832 < baseStart_4012832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012862 : List Nat := [4, 2, 1, 2, 3, 1, 9]
def baseStart_4012862 : Nat := 118140960795 + 4012862 * 2 ^ 59
def prefixEnd_4012862 : Nat := 4983230072969 + 3 ^ 40 * 4012862 * 2
def baseEnd_4012862 : Nat := 50877210028705775127659

theorem tailTrace_4012862 : CollatzResearch.WordTrace tailWord_4012862 prefixEnd_4012862 50877210028705775127659 := by
  unfold tailWord_4012862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18295137648511723888978105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97574067458729194074549893 18295137648511723888978105)
  ·
    refine ⟨13721353236383792916733579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18295137648511723888978105 13721353236383792916733579)
    ·
      refine ⟨20582029854575689375100369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13721353236383792916733579 20582029854575689375100369)
      ·
        refine ⟨15436522390931767031325277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20582029854575689375100369 15436522390931767031325277)
        ·
          refine ⟨5788695896599412636746979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15436522390931767031325277 5788695896599412636746979)
          ·
            refine ⟨8683043844899118955120469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788695896599412636746979 8683043844899118955120469)
            ·
              refine ⟨50877210028705775127659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8683043844899118955120469 50877210028705775127659)
              ·
                rfl

theorem cell22_4012862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 9].length) (baseStart_4012862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012862 prefixEnd_4012862 := by exact prefixLift 4012862
  have htrace : WordTrace (prefixWord ++ tailWord_4012862) baseStart_4012862 baseEnd_4012862 := by
    simpa [prefixWord, tailWord_4012862, baseEnd_4012862] using wordTrace_append hprefix tailTrace_4012862
  have hstable : (prefixWord ++ tailWord_4012862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012862).length < 2 ^ (prefixWord ++ tailWord_4012862).sum := by decide
  have hdescent : baseEnd_4012862 < baseStart_4012862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012954 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_4012954 : Nat := 118140960795 + 4012954 * 2 ^ 59
def prefixEnd_4012954 : Nat := 4983230072969 + 3 ^ 40 * 4012954 * 2
def baseEnd_4012954 : Nat := 1373716164255198355146511

theorem tailTrace_4012954 : CollatzResearch.WordTrace tailWord_4012954 prefixEnd_4012954 1373716164255198355146511 := by
  unfold tailWord_4012954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36591114175940122706043479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97576304469173660549449277 36591114175940122706043479)
  ·
    refine ⟨54886671263910184059065219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36591114175940122706043479 54886671263910184059065219)
    ·
      refine ⟨82330006895865276088597829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54886671263910184059065219 82330006895865276088597829)
      ·
        refine ⟨15436876292974739266612093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82330006895865276088597829 15436876292974739266612093)
        ·
          refine ⟨5788828609865527224979535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15436876292974739266612093 5788828609865527224979535)
          ·
            refine ⟨8683242914798290837469303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788828609865527224979535 8683242914798290837469303)
            ·
              refine ⟨13024864372197436256203955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683242914798290837469303 13024864372197436256203955)
              ·
                refine ⟨19537296558296154384305933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024864372197436256203955 19537296558296154384305933)
                ·
                  refine ⟨7326486209361057894114725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19537296558296154384305933 7326486209361057894114725)
                  ·
                    refine ⟨1373716164255198355146511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7326486209361057894114725 1373716164255198355146511)
                    ·
                      rfl

theorem cell22_4012954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_4012954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012954 prefixEnd_4012954 := by exact prefixLift 4012954
  have htrace : WordTrace (prefixWord ++ tailWord_4012954) baseStart_4012954 baseEnd_4012954 := by
    simpa [prefixWord, tailWord_4012954, baseEnd_4012954] using wordTrace_append hprefix tailTrace_4012954
  have hstable : (prefixWord ++ tailWord_4012954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012954).length < 2 ^ (prefixWord ++ tailWord_4012954).sum := by decide
  have hdescent : baseEnd_4012954 < baseStart_4012954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012984 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_4012984 : Nat := 118140960795 + 4012984 * 2 ^ 59
def prefixEnd_4012984 : Nat := 4983230072969 + 3 ^ 40 * 4012984 * 2
def baseEnd_4012984 : Nat := 1373726433868288276896419

theorem tailTrace_4012984 : CollatzResearch.WordTrace tailWord_4012984 prefixEnd_4012984 1373726433868288276896419 := by
  unfold tailWord_4012984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73182775446825902973883003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97577033929101203965177337 73182775446825902973883003)
  ·
    refine ⟨109774163170238854460824505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73182775446825902973883003 109774163170238854460824505)
    ·
      refine ⟨82330622377679140845618379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109774163170238854460824505 82330622377679140845618379)
      ·
        refine ⟨123495933566518711268427569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82330622377679140845618379 123495933566518711268427569)
        ·
          refine ⟨92621950174889033451320677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123495933566518711268427569 92621950174889033451320677)
          ·
            refine ⟨17366615657791693772122627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92621950174889033451320677 17366615657791693772122627)
            ·
              refine ⟨26049923486687540658183941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366615657791693772122627 26049923486687540658183941)
              ·
                refine ⟨4884360653753913873409489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26049923486687540658183941 4884360653753913873409489)
                ·
                  refine ⟨3663270490315435405057117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884360653753913873409489 3663270490315435405057117)
                  ·
                    refine ⟨1373726433868288276896419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663270490315435405057117 1373726433868288276896419)
                    ·
                      rfl

theorem cell22_4012984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_4012984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4012984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4012984 prefixEnd_4012984 := by exact prefixLift 4012984
  have htrace : WordTrace (prefixWord ++ tailWord_4012984) baseStart_4012984 baseEnd_4012984 := by
    simpa [prefixWord, tailWord_4012984, baseEnd_4012984] using wordTrace_append hprefix tailTrace_4012984
  have hstable : (prefixWord ++ tailWord_4012984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012984).length < 2 ^ (prefixWord ++ tailWord_4012984).sum := by decide
  have hdescent : baseEnd_4012984 < baseStart_4012984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013046 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_4013046 : Nat := 118140960795 + 4013046 * 2 ^ 59
def prefixEnd_4013046 : Nat := 4983230072969 + 3 ^ 40 * 4013046 * 2
def baseEnd_4013046 : Nat := 1373747657735340781846229

theorem tailTrace_4013046 : CollatzResearch.WordTrace tailWord_4013046 prefixEnd_4013046 1373747657735340781846229 := by
  unfold tailWord_4013046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147988263714199408532687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97578541479618127024348661 9147988263714199408532687)
  ·
    refine ⟨13721982395571299112799031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9147988263714199408532687 13721982395571299112799031)
    ·
      refine ⟨20582973593356948669198547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13721982395571299112799031 20582973593356948669198547)
      ·
        refine ⟨30874460390035423003797821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20582973593356948669198547 30874460390035423003797821)
        ·
          refine ⟨11577922646263283626424183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30874460390035423003797821 11577922646263283626424183)
          ·
            refine ⟨17366883969394925439636275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577922646263283626424183 17366883969394925439636275)
            ·
              refine ⟨26050325954092388159454413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366883969394925439636275 26050325954092388159454413)
              ·
                refine ⟨9768872232784645559795405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26050325954092388159454413 9768872232784645559795405)
                ·
                  refine ⟨3663327087294242084923277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9768872232784645559795405 3663327087294242084923277)
                  ·
                    refine ⟨1373747657735340781846229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663327087294242084923277 1373747657735340781846229)
                    ·
                      rfl

theorem cell22_4013046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_4013046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013046 prefixEnd_4013046 := by exact prefixLift 4013046
  have htrace : WordTrace (prefixWord ++ tailWord_4013046) baseStart_4013046 baseEnd_4013046 := by
    simpa [prefixWord, tailWord_4013046, baseEnd_4013046] using wordTrace_append hprefix tailTrace_4013046
  have hstable : (prefixWord ++ tailWord_4013046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013046).length < 2 ^ (prefixWord ++ tailWord_4013046).sum := by decide
  have hdescent : baseEnd_4013046 < baseStart_4013046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013149 : List Nat := [1, 4, 4, 1, 12]
def baseStart_4013149 : Nat := 118140960795 + 4013149 * 2 ^ 59
def prefixEnd_4013149 : Nat := 4983230072969 + 3 ^ 40 * 4013149 * 2
def baseEnd_4013149 : Nat := 5653427640906513771691

theorem tailTrace_4013149 : CollatzResearch.WordTrace tailWord_4013149 prefixEnd_4013149 5653427640906513771691 := by
  unfold tailWord_4013149
  simp only [CollatzResearch.WordTrace]
  refine ⟨146371568938054039127522501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97581045958702692751681667 146371568938054039127522501)
  ·
    refine ⟨27444669175885132336410469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146371568938054039127522501 27444669175885132336410469)
    ·
      refine ⟨5145875470478462313076963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27444669175885132336410469 5145875470478462313076963)
      ·
        refine ⟨7718813205717693469615445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145875470478462313076963 7718813205717693469615445)
        ·
          refine ⟨5653427640906513771691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7718813205717693469615445 5653427640906513771691)
          ·
            rfl

theorem cell22_4013149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 12].length) (baseStart_4013149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013149 prefixEnd_4013149 := by exact prefixLift 4013149
  have htrace : WordTrace (prefixWord ++ tailWord_4013149) baseStart_4013149 baseEnd_4013149 := by
    simpa [prefixWord, tailWord_4013149, baseEnd_4013149] using wordTrace_append hprefix tailTrace_4013149
  have hstable : (prefixWord ++ tailWord_4013149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013149).length < 2 ^ (prefixWord ++ tailWord_4013149).sum := by decide
  have hdescent : baseEnd_4013149 < baseStart_4013149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013166 : List Nat := [4, 1, 2, 2, 1, 4, 1, 7]
def baseStart_4013166 : Nat := 118140960795 + 4013166 * 2 ^ 59
def prefixEnd_4013166 : Nat := 4983230072969 + 3 ^ 40 * 4013166 * 2
def baseEnd_4013166 : Nat := 152643192909744496538429

theorem tailTrace_4013166 : CollatzResearch.WordTrace tailWord_4013166 prefixEnd_4013166 152643192909744496538429 := by
  unfold tailWord_4013166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296523622374056378861419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97581459319328300687260901 18296523622374056378861419)
  ·
    refine ⟨27444785433561084568292129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18296523622374056378861419 27444785433561084568292129)
    ·
      refine ⟨20583589075170813426219097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27444785433561084568292129 20583589075170813426219097)
      ·
        refine ⟨15437691806378110069664323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20583589075170813426219097 15437691806378110069664323)
        ·
          refine ⟨23156537709567165104496485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15437691806378110069664323 23156537709567165104496485)
          ·
            refine ⟨4341850820543843457093091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23156537709567165104496485 4341850820543843457093091)
            ·
              refine ⟨6512776230815765185639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341850820543843457093091 6512776230815765185639637)
              ·
                refine ⟨152643192909744496538429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6512776230815765185639637 152643192909744496538429)
                ·
                  rfl

theorem cell22_4013166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_4013166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013166 prefixEnd_4013166 := by exact prefixLift 4013166
  have htrace : WordTrace (prefixWord ++ tailWord_4013166) baseStart_4013166 baseEnd_4013166 := by
    simpa [prefixWord, tailWord_4013166, baseEnd_4013166] using wordTrace_append hprefix tailTrace_4013166
  have hstable : (prefixWord ++ tailWord_4013166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013166).length < 2 ^ (prefixWord ++ tailWord_4013166).sum := by decide
  have hdescent : baseEnd_4013166 < baseStart_4013166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013181 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_4013181 : Nat := 118140960795 + 4013181 * 2 ^ 59
def prefixEnd_4013181 : Nat := 4983230072969 + 3 ^ 40 * 4013181 * 2
def baseEnd_4013181 : Nat := 1373793870994245429720815

theorem tailTrace_4013181 : CollatzResearch.WordTrace tailWord_4013181 prefixEnd_4013181 1373793870994245429720815 := by
  unfold tailWord_4013181
  simp only [CollatzResearch.WordTrace]
  refine ⟨146372736073938108592687397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97581824049292072395124931 146372736073938108592687397)
  ·
    refine ⟨27444888013863395361128887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146372736073938108592687397 27444888013863395361128887)
    ·
      refine ⟨41167332020795093041693331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27444888013863395361128887 41167332020795093041693331)
      ·
        refine ⟨61750998031192639562539997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41167332020795093041693331 61750998031192639562539997)
        ·
          refine ⟨23156624261697239835952499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61750998031192639562539997 23156624261697239835952499)
          ·
            refine ⟨34734936392545859753928749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23156624261697239835952499 34734936392545859753928749)
            ·
              refine ⟨13025601147204697407723281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34734936392545859753928749 13025601147204697407723281)
              ·
                refine ⟨9769200860403523055792461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13025601147204697407723281 9769200860403523055792461)
                ·
                  refine ⟨3663450322651321145922173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9769200860403523055792461 3663450322651321145922173)
                  ·
                    refine ⟨1373793870994245429720815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663450322651321145922173 1373793870994245429720815)
                    ·
                      rfl

theorem cell22_4013181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_4013181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013181 prefixEnd_4013181 := by exact prefixLift 4013181
  have htrace : WordTrace (prefixWord ++ tailWord_4013181) baseStart_4013181 baseEnd_4013181 := by
    simpa [prefixWord, tailWord_4013181, baseEnd_4013181] using wordTrace_append hprefix tailTrace_4013181
  have hstable : (prefixWord ++ tailWord_4013181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013181).length < 2 ^ (prefixWord ++ tailWord_4013181).sum := by decide
  have hdescent : baseEnd_4013181 < baseStart_4013181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013194 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_4013194 : Nat := 118140960795 + 4013194 * 2 ^ 59
def prefixEnd_4013194 : Nat := 4983230072969 + 3 ^ 40 * 4013194 * 2
def baseEnd_4013194 : Nat := 457932773719972576381925

theorem tailTrace_4013194 : CollatzResearch.WordTrace tailWord_4013194 prefixEnd_4013194 457932773719972576381925 := by
  unfold tailWord_4013194
  simp only [CollatzResearch.WordTrace]
  refine ⟨36593302555722752953227659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97582140148594007875273757 36593302555722752953227659)
  ·
    refine ⟨54889953833584129429841489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36593302555722752953227659 54889953833584129429841489)
    ·
      refine ⟨41167465375188097072381117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54889953833584129429841489 41167465375188097072381117)
      ·
        refine ⟨15437799515695536402142919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41167465375188097072381117 15437799515695536402142919)
        ·
          refine ⟨23156699273543304603214379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15437799515695536402142919 23156699273543304603214379)
          ·
            refine ⟨34735048910314956904821569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23156699273543304603214379 34735048910314956904821569)
            ·
              refine ⟨26051286682736217678616177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34735048910314956904821569 26051286682736217678616177)
              ·
                refine ⟨19538465012052163258962133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26051286682736217678616177 19538465012052163258962133)
                ·
                  refine ⟨457932773719972576381925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19538465012052163258962133 457932773719972576381925)
                  ·
                    rfl

theorem cell22_4013194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_4013194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013194 prefixEnd_4013194 := by exact prefixLift 4013194
  have htrace : WordTrace (prefixWord ++ tailWord_4013194) baseStart_4013194 baseEnd_4013194 := by
    simpa [prefixWord, tailWord_4013194, baseEnd_4013194] using wordTrace_append hprefix tailTrace_4013194
  have hstable : (prefixWord ++ tailWord_4013194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013194).length < 2 ^ (prefixWord ++ tailWord_4013194).sum := by decide
  have hdescent : baseEnd_4013194 < baseStart_4013194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013239 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 6]
def baseStart_4013239 : Nat := 118140960795 + 4013239 * 2 ^ 59
def prefixEnd_4013239 : Nat := 4983230072969 + 3 ^ 40 * 4013239 * 2
def baseEnd_4013239 : Nat := 457937908526517537256879

theorem tailTrace_4013239 : CollatzResearch.WordTrace tailWord_4013239 prefixEnd_4013239 457937908526517537256879 := by
  unfold tailWord_4013239
  simp only [CollatzResearch.WordTrace]
  refine ⟨146374851507727984498298771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97583234338485322998865847 146374851507727984498298771)
  ·
    refine ⟨219562277261591976747448157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146374851507727984498298771 219562277261591976747448157)
    ·
      refine ⟨82335853973096991280293059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219562277261591976747448157 82335853973096991280293059)
      ·
        refine ⟨123503780959645486920439589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82335853973096991280293059 123503780959645486920439589)
        ·
          refine ⟨23156958929933528797582423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123503780959645486920439589 23156958929933528797582423)
          ·
            refine ⟨34735438394900293196373635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23156958929933528797582423 34735438394900293196373635)
            ·
              refine ⟨52103157592350439794560453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34735438394900293196373635 52103157592350439794560453)
              ·
                refine ⟨9769342048565707461480085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52103157592350439794560453 9769342048565707461480085)
                ·
                  refine ⟨457937908526517537256879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9769342048565707461480085 457937908526517537256879)
                  ·
                    rfl

theorem cell22_4013239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_4013239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013239 prefixEnd_4013239 := by exact prefixLift 4013239
  have htrace : WordTrace (prefixWord ++ tailWord_4013239) baseStart_4013239 baseEnd_4013239 := by
    simpa [prefixWord, tailWord_4013239, baseEnd_4013239] using wordTrace_append hprefix tailTrace_4013239
  have hstable : (prefixWord ++ tailWord_4013239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013239).length < 2 ^ (prefixWord ++ tailWord_4013239).sum := by decide
  have hdescent : baseEnd_4013239 < baseStart_4013239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013241 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_4013241 : Nat := 118140960795 + 4013241 * 2 ^ 59
def prefixEnd_4013241 : Nat := 4983230072969 + 3 ^ 40 * 4013241 * 2
def baseEnd_4013241 : Nat := 1373814410220425273220631

theorem tailTrace_4013241 : CollatzResearch.WordTrace tailWord_4013241 prefixEnd_4013241 1373814410220425273220631 := by
  unfold tailWord_4013241
  simp only [CollatzResearch.WordTrace]
  refine ⟨146374924453720738839871577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97583282969147159226581051 146374924453720738839871577)
  ·
    refine ⟨109781193340290554129903683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146374924453720738839871577 109781193340290554129903683)
    ·
      refine ⟨164671790010435831194855525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109781193340290554129903683 164671790010435831194855525)
      ·
        refine ⟨30875960626956718349035411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164671790010435831194855525 30875960626956718349035411)
        ·
          refine ⟨46313940940435077523553117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30875960626956718349035411 46313940940435077523553117)
          ·
            refine ⟨17367727852663154071332419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46313940940435077523553117 17367727852663154071332419)
            ·
              refine ⟨26051591778994731106998629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17367727852663154071332419 26051591778994731106998629)
              ·
                refine ⟨4884673458561512082562243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26051591778994731106998629 4884673458561512082562243)
                ·
                  refine ⟨7327010187842268123843365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884673458561512082562243 7327010187842268123843365)
                  ·
                    refine ⟨1373814410220425273220631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327010187842268123843365 1373814410220425273220631)
                    ·
                      rfl

theorem cell22_4013241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_4013241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013241 prefixEnd_4013241 := by exact prefixLift 4013241
  have htrace : WordTrace (prefixWord ++ tailWord_4013241) baseStart_4013241 baseEnd_4013241 := by
    simpa [prefixWord, tailWord_4013241, baseEnd_4013241] using wordTrace_append hprefix tailTrace_4013241
  have hstable : (prefixWord ++ tailWord_4013241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013241).length < 2 ^ (prefixWord ++ tailWord_4013241).sum := by decide
  have hdescent : baseEnd_4013241 < baseStart_4013241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013271 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 4, 3]
def baseStart_4013271 : Nat := 118140960795 + 4013271 * 2 ^ 59
def prefixEnd_4013271 : Nat := 4983230072969 + 3 ^ 40 * 4013271 * 2
def baseEnd_4013271 : Nat := 1373824679833515194970539

theorem tailTrace_4013271 : CollatzResearch.WordTrace tailWord_4013271 prefixEnd_4013271 1373824679833515194970539 := by
  unfold tailWord_4013271
  simp only [CollatzResearch.WordTrace]
  refine ⟨146376018643612053963463667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97584012429074702642309111 146376018643612053963463667)
  ·
    refine ⟨219564027965418080945195501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146376018643612053963463667 219564027965418080945195501)
    ·
      refine ⟨82336510487031780354448313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219564027965418080945195501 82336510487031780354448313)
      ·
        refine ⟨61752382865273835265836235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82336510487031780354448313 61752382865273835265836235)
        ·
          refine ⟨92628574297910752898754353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61752382865273835265836235 92628574297910752898754353)
          ·
            refine ⟨69471430723433064674065765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92628574297910752898754353 69471430723433064674065765)
            ·
              refine ⟨13025893260643699626387331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69471430723433064674065765 13025893260643699626387331)
              ·
                refine ⟨19538839890965549439580997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025893260643699626387331 19538839890965549439580997)
                ·
                  refine ⟨3663532479556040519921437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19538839890965549439580997 3663532479556040519921437)
                  ·
                    refine ⟨1373824679833515194970539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663532479556040519921437 1373824679833515194970539)
                    ·
                      rfl

theorem cell22_4013271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_4013271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013271 prefixEnd_4013271 := by exact prefixLift 4013271
  have htrace : WordTrace (prefixWord ++ tailWord_4013271) baseStart_4013271 baseEnd_4013271 := by
    simpa [prefixWord, tailWord_4013271, baseEnd_4013271] using wordTrace_append hprefix tailTrace_4013271
  have hstable : (prefixWord ++ tailWord_4013271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013271).length < 2 ^ (prefixWord ++ tailWord_4013271).sum := by decide
  have hdescent : baseEnd_4013271 < baseStart_4013271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013284 : List Nat := [2, 3, 1, 1, 1, 2, 3, 9]
def baseStart_4013284 : Nat := 118140960795 + 4013284 * 2 ^ 59
def prefixEnd_4013284 : Nat := 4983230072969 + 3 ^ 40 * 4013284 * 2
def baseEnd_4013284 : Nat := 152647681111020832710611

theorem tailTrace_4013284 : CollatzResearch.WordTrace tailWord_4013284 prefixEnd_4013284 152647681111020832710611 := by
  unfold tailWord_4013284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73188246396282478591843453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97584328528376638122457937 73188246396282478591843453)
  ·
    refine ⟨27445592398605929471941295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73188246396282478591843453 27445592398605929471941295)
    ·
      refine ⟨41168388597908894207911943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27445592398605929471941295 41168388597908894207911943)
      ·
        refine ⟨61752582896863341311867915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41168388597908894207911943 61752582896863341311867915)
        ·
          refine ⟨92628874345295011967801873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61752582896863341311867915 92628874345295011967801873)
          ·
            refine ⟨69471655758971258975851405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92628874345295011967801873 69471655758971258975851405)
            ·
              refine ⟨26051870909614222115944277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69471655758971258975851405 26051870909614222115944277)
              ·
                refine ⟨152647681111020832710611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26051870909614222115944277 152647681111020832710611)
                ·
                  rfl

theorem cell22_4013284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_4013284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013284 prefixEnd_4013284 := by exact prefixLift 4013284
  have htrace : WordTrace (prefixWord ++ tailWord_4013284) baseStart_4013284 baseEnd_4013284 := by
    simpa [prefixWord, tailWord_4013284, baseEnd_4013284] using wordTrace_append hprefix tailTrace_4013284
  have hstable : (prefixWord ++ tailWord_4013284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013284).length < 2 ^ (prefixWord ++ tailWord_4013284).sum := by decide
  have hdescent : baseEnd_4013284 < baseStart_4013284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013288 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_4013288 : Nat := 118140960795 + 4013288 * 2 ^ 59
def prefixEnd_4013288 : Nat := 4983230072969 + 3 ^ 40 * 4013288 * 2
def baseEnd_4013288 : Nat := 1373830499280932817295487

theorem tailTrace_4013288 : CollatzResearch.WordTrace tailWord_4013288 prefixEnd_4013288 1373830499280932817295487 := by
  unfold tailWord_4013288
  simp only [CollatzResearch.WordTrace]
  refine ⟨73188319342275232933416259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97584425789700310577888345 73188319342275232933416259)
  ·
    refine ⟨109782479013412849400124389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73188319342275232933416259 109782479013412849400124389)
    ·
      refine ⟨20584214815014909262523323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109782479013412849400124389 20584214815014909262523323)
      ·
        refine ⟨30876322222522363893784985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20584214815014909262523323 30876322222522363893784985)
        ·
          refine ⟨23157241666891772920338739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30876322222522363893784985 23157241666891772920338739)
          ·
            refine ⟨34735862500337659380508109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23157241666891772920338739 34735862500337659380508109)
            ·
              refine ⟨13025948437626622267690541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34735862500337659380508109 13025948437626622267690541)
              ·
                refine ⟨4884730664109983350383953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13025948437626622267690541 4884730664109983350383953)
                ·
                  refine ⟨3663547998082487512787965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884730664109983350383953 3663547998082487512787965)
                  ·
                    refine ⟨1373830499280932817295487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663547998082487512787965 1373830499280932817295487)
                    ·
                      rfl

theorem cell22_4013288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_4013288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013288 prefixEnd_4013288 := by exact prefixLift 4013288
  have htrace : WordTrace (prefixWord ++ tailWord_4013288) baseStart_4013288 baseEnd_4013288 := by
    simpa [prefixWord, tailWord_4013288, baseEnd_4013288] using wordTrace_append hprefix tailTrace_4013288
  have hstable : (prefixWord ++ tailWord_4013288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013288).length < 2 ^ (prefixWord ++ tailWord_4013288).sum := by decide
  have hdescent : baseEnd_4013288 < baseStart_4013288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013380 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_4013380 : Nat := 118140960795 + 4013380 * 2 ^ 59
def prefixEnd_4013380 : Nat := 4983230072969 + 3 ^ 40 * 4013380 * 2
def baseEnd_4013380 : Nat := 457953997587025081331735

theorem tailTrace_4013380 : CollatzResearch.WordTrace tailWord_4013380 prefixEnd_4013380 457953997587025081331735 := by
  unfold tailWord_4013380
  simp only [CollatzResearch.WordTrace]
  refine ⟨73189997100108582789590797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97586662800144777052787729 73189997100108582789590797)
  ·
    refine ⟨27446248912540718546096549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73189997100108582789590797 27446248912540718546096549)
    ·
      refine ⟨5146171671101384727393103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27446248912540718546096549 5146171671101384727393103)
      ·
        refine ⟨7719257506652077091089655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146171671101384727393103 7719257506652077091089655)
        ·
          refine ⟨11578886259978115636634483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719257506652077091089655 11578886259978115636634483)
          ·
            refine ⟨17368329389967173454951725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578886259978115636634483 17368329389967173454951725)
            ·
              refine ⟨6513123521237690045606897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17368329389967173454951725 6513123521237690045606897)
              ·
                refine ⟨4884842640928267534205173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513123521237690045606897 4884842640928267534205173)
                ·
                  refine ⟨457953997587025081331735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4884842640928267534205173 457953997587025081331735)
                  ·
                    rfl

theorem cell22_4013380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_4013380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013380 prefixEnd_4013380 := by exact prefixLift 4013380
  have htrace : WordTrace (prefixWord ++ tailWord_4013380) baseStart_4013380 baseEnd_4013380 := by
    simpa [prefixWord, tailWord_4013380, baseEnd_4013380] using wordTrace_append hprefix tailTrace_4013380
  have hstable : (prefixWord ++ tailWord_4013380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013380).length < 2 ^ (prefixWord ++ tailWord_4013380).sum := by decide
  have hdescent : baseEnd_4013380 < baseStart_4013380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013410 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4013410 : Nat := 118140960795 + 4013410 * 2 ^ 59
def prefixEnd_4013410 : Nat := 4983230072969 + 3 ^ 40 * 4013410 * 2
def baseEnd_4013410 : Nat := 1373872262374165165745113

theorem tailTrace_4013410 : CollatzResearch.WordTrace tailWord_4013410 prefixEnd_4013410 1373872262374165165745113 := by
  unfold tailWord_4013410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36595272097527120175693421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97587392260072320468515789 36595272097527120175693421)
  ·
    refine ⟨13723227036572670065885033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36595272097527120175693421 13723227036572670065885033)
    ·
      refine ⟨10292420277429502549413775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13723227036572670065885033 10292420277429502549413775)
      ·
        refine ⟨15438630416144253824120663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292420277429502549413775 15438630416144253824120663)
        ·
          refine ⟨23157945624216380736180995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15438630416144253824120663 23157945624216380736180995)
          ·
            refine ⟨34736918436324571104271493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23157945624216380736180995 34736918436324571104271493)
            ·
              refine ⟨6513172206810857082050905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34736918436324571104271493 6513172206810857082050905)
              ·
                refine ⟨4884879155108142811538179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513172206810857082050905 4884879155108142811538179)
                ·
                  refine ⟨7327318732662214217307269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884879155108142811538179 7327318732662214217307269)
                  ·
                    refine ⟨1373872262374165165745113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327318732662214217307269 1373872262374165165745113)
                    ·
                      rfl

theorem cell22_4013410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4013410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013410 prefixEnd_4013410 := by exact prefixLift 4013410
  have htrace : WordTrace (prefixWord ++ tailWord_4013410) baseStart_4013410 baseEnd_4013410 := by
    simpa [prefixWord, tailWord_4013410, baseEnd_4013410] using wordTrace_append hprefix tailTrace_4013410
  have hstable : (prefixWord ++ tailWord_4013410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013410).length < 2 ^ (prefixWord ++ tailWord_4013410).sum := by decide
  have hdescent : baseEnd_4013410 < baseStart_4013410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013442 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_4013442 : Nat := 118140960795 + 4013442 * 2 ^ 59
def prefixEnd_4013442 : Nat := 4983230072969 + 3 ^ 40 * 4013442 * 2
def baseEnd_4013442 : Nat := 457961072209375916315005

theorem tailTrace_4013442 : CollatzResearch.WordTrace tailWord_4013442 prefixEnd_4013442 457961072209375916315005 := by
  unfold tailWord_4013442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36595563881498137541984645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97588170350661700111959053 36595563881498137541984645)
  ·
    refine ⟨6861668227780900789122121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36595563881498137541984645 6861668227780900789122121)
    ·
      refine ⟨5146251170835675591841591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6861668227780900789122121 5146251170835675591841591)
      ·
        refine ⟨7719376756253513387762387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146251170835675591841591 7719376756253513387762387)
        ·
          refine ⟨11579065134380270081643581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719376756253513387762387 11579065134380270081643581)
          ·
            refine ⟨4342149425392601280616343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11579065134380270081643581 4342149425392601280616343)
            ·
              refine ⟨6513224138088901920924515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342149425392601280616343 6513224138088901920924515)
              ·
                refine ⟨9769836207133352881386773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513224138088901920924515 9769836207133352881386773)
                ·
                  refine ⟨457961072209375916315005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9769836207133352881386773 457961072209375916315005)
                  ·
                    rfl

theorem cell22_4013442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_4013442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013442 prefixEnd_4013442 := by exact prefixLift 4013442
  have htrace : WordTrace (prefixWord ++ tailWord_4013442) baseStart_4013442 baseEnd_4013442 := by
    simpa [prefixWord, tailWord_4013442, baseEnd_4013442] using wordTrace_append hprefix tailTrace_4013442
  have hstable : (prefixWord ++ tailWord_4013442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013442).length < 2 ^ (prefixWord ++ tailWord_4013442).sum := by decide
  have hdescent : baseEnd_4013442 < baseStart_4013442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013528 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_4013528 : Nat := 118140960795 + 4013528 * 2 ^ 59
def prefixEnd_4013528 : Nat := 4983230072969 + 3 ^ 40 * 4013528 * 2
def baseEnd_4013528 : Nat := 1373912656185652191294751

theorem tailTrace_4013528 : CollatzResearch.WordTrace tailWord_4013528 prefixEnd_4013528 1373912656185652191294751 := by
  unfold tailWord_4013528
  simp only [CollatzResearch.WordTrace]
  refine ⟨73192696101840493427784619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97590261469120657903712825 73192696101840493427784619)
  ·
    refine ⟨109789044152760740141676929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73192696101840493427784619 109789044152760740141676929)
    ·
      refine ⟨82341783114570555106257697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109789044152760740141676929 82341783114570555106257697)
      ·
        refine ⟨61756337335927916329693273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82341783114570555106257697 61756337335927916329693273)
        ·
          refine ⟨46317253001945937247269955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61756337335927916329693273 46317253001945937247269955)
          ·
            refine ⟨69475879502918905870904933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46317253001945937247269955 69475879502918905870904933)
            ·
              refine ⟨13026727406797294850794675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69475879502918905870904933 13026727406797294850794675)
              ·
                refine ⟨19540091110195942276192013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026727406797294850794675 19540091110195942276192013)
                ·
                  refine ⟨7327534166323478353572005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19540091110195942276192013 7327534166323478353572005)
                  ·
                    refine ⟨1373912656185652191294751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327534166323478353572005 1373912656185652191294751)
                    ·
                      rfl

theorem cell22_4013528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_4013528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013528 prefixEnd_4013528 := by exact prefixLift 4013528
  have htrace : WordTrace (prefixWord ++ tailWord_4013528) baseStart_4013528 baseEnd_4013528 := by
    simpa [prefixWord, tailWord_4013528, baseEnd_4013528] using wordTrace_append hprefix tailTrace_4013528
  have hstable : (prefixWord ++ tailWord_4013528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013528).length < 2 ^ (prefixWord ++ tailWord_4013528).sum := by decide
  have hdescent : baseEnd_4013528 < baseStart_4013528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013549 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 5]
def baseStart_4013549 : Nat := 118140960795 + 4013549 * 2 ^ 59
def prefixEnd_4013549 : Nat := 4983230072969 + 3 ^ 40 * 4013549 * 2
def baseEnd_4013549 : Nat := 457973281638271712173229

theorem tailTrace_4013549 : CollatzResearch.WordTrace tailWord_4013549 prefixEnd_4013549 457973281638271712173229 := by
  unfold tailWord_4013549
  simp only [CollatzResearch.WordTrace]
  refine ⟨146386158136604907442083701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97590772091069938294722467 146386158136604907442083701)
  ·
    refine ⟨13723702325306710072695347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146386158136604907442083701 13723702325306710072695347)
    ·
      refine ⟨20585553487960065109043021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13723702325306710072695347 20585553487960065109043021)
      ·
        refine ⟨7719582557985024415891133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20585553487960065109043021 7719582557985024415891133)
        ·
          refine ⟨2894843459244384155959175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7719582557985024415891133 2894843459244384155959175)
          ·
            refine ⟨4342265188866576233938763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894843459244384155959175 4342265188866576233938763)
            ·
              refine ⟨6513397783299864350908145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342265188866576233938763 6513397783299864350908145)
              ·
                refine ⟨4885048337474898263181109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513397783299864350908145 4885048337474898263181109)
                ·
                  refine ⟨457973281638271712173229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4885048337474898263181109 457973281638271712173229)
                  ·
                    rfl

theorem cell22_4013549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_4013549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013549 prefixEnd_4013549 := by exact prefixLift 4013549
  have htrace : WordTrace (prefixWord ++ tailWord_4013549) baseStart_4013549 baseEnd_4013549 := by
    simpa [prefixWord, tailWord_4013549, baseEnd_4013549] using wordTrace_append hprefix tailTrace_4013549
  have hstable : (prefixWord ++ tailWord_4013549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013549).length < 2 ^ (prefixWord ++ tailWord_4013549).sum := by decide
  have hdescent : baseEnd_4013549 < baseStart_4013549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013560 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_4013560 : Nat := 118140960795 + 4013560 * 2 ^ 59
def prefixEnd_4013560 : Nat := 4983230072969 + 3 ^ 40 * 4013560 * 2
def baseEnd_4013560 : Nat := 457974536813204924831551

theorem tailTrace_4013560 : CollatzResearch.WordTrace tailWord_4013560 prefixEnd_4013560 457974536813204924831551 := by
  unfold tailWord_4013560
  simp only [CollatzResearch.WordTrace]
  refine ⟨73193279669782528160367067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97591039559710037547156089 73193279669782528160367067)
  ·
    refine ⟨109789919504673792240550601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73193279669782528160367067 109789919504673792240550601)
    ·
      refine ⟨82342439628505344180412951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109789919504673792240550601 82342439628505344180412951)
      ·
        refine ⟨123513659442758016270619427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82342439628505344180412951 123513659442758016270619427)
        ·
          refine ⟨185270489164137024405929141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123513659442758016270619427 185270489164137024405929141)
          ·
            refine ⟨17369108359137846038055857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185270489164137024405929141 17369108359137846038055857)
            ·
              refine ⟨13026831269353384528541893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369108359137846038055857 13026831269353384528541893)
              ·
                refine ⟨2442530863003759599101605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13026831269353384528541893 2442530863003759599101605)
                ·
                  refine ⟨457974536813204924831551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442530863003759599101605 457974536813204924831551)
                  ·
                    rfl

theorem cell22_4013560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_4013560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013560 prefixEnd_4013560 := by exact prefixLift 4013560
  have htrace : WordTrace (prefixWord ++ tailWord_4013560) baseStart_4013560 baseEnd_4013560 := by
    simpa [prefixWord, tailWord_4013560, baseEnd_4013560] using wordTrace_append hprefix tailTrace_4013560
  have hstable : (prefixWord ++ tailWord_4013560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013560).length < 2 ^ (prefixWord ++ tailWord_4013560).sum := by decide
  have hdescent : baseEnd_4013560 < baseStart_4013560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013575 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 1, 5]
def baseStart_4013575 : Nat := 118140960795 + 4013575 * 2 ^ 59
def prefixEnd_4013575 : Nat := 4983230072969 + 3 ^ 40 * 4013575 * 2
def baseEnd_4013575 : Nat := 1373928745246159735369607

theorem tailTrace_4013575 : CollatzResearch.WordTrace tailWord_4013575 prefixEnd_4013575 1373928745246159735369607 := by
  unfold tailWord_4013575
  simp only [CollatzResearch.WordTrace]
  refine ⟨146387106434510713882530179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97591404289673809255020119 146387106434510713882530179)
  ·
    refine ⟨219580659651766070823795269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146387106434510713882530179 219580659651766070823795269)
    ·
      refine ⟨41171373684706138279461613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219580659651766070823795269 41171373684706138279461613)
      ·
        refine ⟨15439265131764801854798105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41171373684706138279461613 15439265131764801854798105)
        ·
          refine ⟨11579448848823601391098579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15439265131764801854798105 11579448848823601391098579)
          ·
            refine ⟨17369173273235402086647869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579448848823601391098579 17369173273235402086647869)
            ·
              refine ⟨6513439977463275782492951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17369173273235402086647869 6513439977463275782492951)
              ·
                refine ⟨9770159966194913673739427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513439977463275782492951 9770159966194913673739427)
                ·
                  refine ⟨14655239949292370510609141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770159966194913673739427 14655239949292370510609141)
                  ·
                    refine ⟨1373928745246159735369607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14655239949292370510609141 1373928745246159735369607)
                    ·
                      rfl

theorem cell22_4013575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_4013575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013575 prefixEnd_4013575 := by exact prefixLift 4013575
  have htrace : WordTrace (prefixWord ++ tailWord_4013575) baseStart_4013575 baseEnd_4013575 := by
    simpa [prefixWord, tailWord_4013575, baseEnd_4013575] using wordTrace_append hprefix tailTrace_4013575
  have hstable : (prefixWord ++ tailWord_4013575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013575).length < 2 ^ (prefixWord ++ tailWord_4013575).sum := by decide
  have hdescent : baseEnd_4013575 < baseStart_4013575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013618 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_4013618 : Nat := 118140960795 + 4013618 * 2 ^ 59
def prefixEnd_4013618 : Nat := 4983230072969 + 3 ^ 40 * 4013618 * 2
def baseEnd_4013618 : Nat := 1373943465024921956544475

theorem tailTrace_4013618 : CollatzResearch.WordTrace tailWord_4013618 prefixEnd_4013618 1373943465024921956544475 := by
  unfold tailWord_4013618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36597168693338733056586377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97592449848903288150897005 36597168693338733056586377)
  ·
    refine ⟨27447876520004049792439783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36597168693338733056586377 27447876520004049792439783)
    ·
      refine ⟨41171814780006074688659675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27447876520004049792439783 41171814780006074688659675)
      ·
        refine ⟨61757722170009112032989513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41171814780006074688659675 61757722170009112032989513)
        ·
          refine ⟨46318291627506834024742135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61757722170009112032989513 46318291627506834024742135)
          ·
            refine ⟨69477437441260251037113203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46318291627506834024742135 69477437441260251037113203)
            ·
              refine ⟨104216156161890376555669805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69477437441260251037113203 104216156161890376555669805)
              ·
                refine ⟨39081058560708891208376177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104216156161890376555669805 39081058560708891208376177)
                ·
                  refine ⟨29310793920531668406282133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39081058560708891208376177 29310793920531668406282133)
                  ·
                    refine ⟨1373943465024921956544475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29310793920531668406282133 1373943465024921956544475)
                    ·
                      rfl

theorem cell22_4013618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_4013618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013618 prefixEnd_4013618 := by exact prefixLift 4013618
  have htrace : WordTrace (prefixWord ++ tailWord_4013618) baseStart_4013618 baseEnd_4013618 := by
    simpa [prefixWord, tailWord_4013618, baseEnd_4013618] using wordTrace_append hprefix tailTrace_4013618
  have hstable : (prefixWord ++ tailWord_4013618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013618).length < 2 ^ (prefixWord ++ tailWord_4013618).sum := by decide
  have hdescent : baseEnd_4013618 < baseStart_4013618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013622 : List Nat := [5, 1, 2, 1, 3, 1, 2, 7]
def baseStart_4013622 : Nat := 118140960795 + 4013622 * 2 ^ 59
def prefixEnd_4013622 : Nat := 4983230072969 + 3 ^ 40 * 4013622 * 2
def baseEnd_4013622 : Nat := 152660537145185253271607

theorem tailTrace_4013622 : CollatzResearch.WordTrace tailWord_4013622 prefixEnd_4013622 152660537145185253271607 := by
  unfold tailWord_4013622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149301291583777556843195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97592547110226960606327413 9149301291583777556843195)
  ·
    refine ⟨13723951937375666335264793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149301291583777556843195 13723951937375666335264793)
    ·
      refine ⟨10292963953031749751448595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13723951937375666335264793 10292963953031749751448595)
      ·
        refine ⟨15439445929547624627172893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292963953031749751448595 15439445929547624627172893)
        ·
          refine ⟨5789792223580359235189835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15439445929547624627172893 5789792223580359235189835)
          ·
            refine ⟨8684688335370538852784753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789792223580359235189835 8684688335370538852784753)
            ·
              refine ⟨6513516251527904139588565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8684688335370538852784753 6513516251527904139588565)
              ·
                refine ⟨152660537145185253271607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6513516251527904139588565 152660537145185253271607)
                ·
                  rfl

theorem cell22_4013622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_4013622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013622 prefixEnd_4013622 := by exact prefixLift 4013622
  have htrace : WordTrace (prefixWord ++ tailWord_4013622) baseStart_4013622 baseEnd_4013622 := by
    simpa [prefixWord, tailWord_4013622, baseEnd_4013622] using wordTrace_append hprefix tailTrace_4013622
  have hstable : (prefixWord ++ tailWord_4013622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013622).length < 2 ^ (prefixWord ++ tailWord_4013622).sum := by decide
  have hdescent : baseEnd_4013622 < baseStart_4013622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013680 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_4013680 : Nat := 118140960795 + 4013680 * 2 ^ 59
def prefixEnd_4013680 : Nat := 4983230072969 + 3 ^ 40 * 4013680 * 2
def baseEnd_4013680 : Nat := 1373964688891974461494285

theorem tailTrace_4013680 : CollatzResearch.WordTrace tailWord_4013680 prefixEnd_4013680 1373964688891974461494285 := by
  unfold tailWord_4013680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73195468049565158407551247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97593957399420211210068329 73195468049565158407551247)
  ·
    refine ⟨109793202074347737611326871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73195468049565158407551247 109793202074347737611326871)
    ·
      refine ⟨164689803111521606416990307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109793202074347737611326871 164689803111521606416990307)
      ·
        refine ⟨247034704667282409625485461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164689803111521606416990307 247034704667282409625485461)
        ·
          refine ⟨11579751781278862951194631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247034704667282409625485461 11579751781278862951194631)
          ·
            refine ⟨17369627671918294426791947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579751781278862951194631 17369627671918294426791947)
            ·
              refine ⟨26054441507877441640187921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17369627671918294426791947 26054441507877441640187921)
              ·
                refine ⟨19540831130908081230140941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26054441507877441640187921 19540831130908081230140941)
                ·
                  refine ⟨7327811674090530461302853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19540831130908081230140941 7327811674090530461302853)
                  ·
                    refine ⟨1373964688891974461494285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327811674090530461302853 1373964688891974461494285)
                    ·
                      rfl

theorem cell22_4013680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_4013680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013680 prefixEnd_4013680 := by exact prefixLift 4013680
  have htrace : WordTrace (prefixWord ++ tailWord_4013680) baseStart_4013680 baseEnd_4013680 := by
    simpa [prefixWord, tailWord_4013680, baseEnd_4013680] using wordTrace_append hprefix tailTrace_4013680
  have hstable : (prefixWord ++ tailWord_4013680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013680).length < 2 ^ (prefixWord ++ tailWord_4013680).sum := by decide
  have hdescent : baseEnd_4013680 < baseStart_4013680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013714 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4013714 : Nat := 118140960795 + 4013714 * 2 ^ 59
def prefixEnd_4013714 : Nat := 4983230072969 + 3 ^ 40 * 4013714 * 2
def baseEnd_4013714 : Nat := 1373976327786809706144181

theorem tailTrace_4013714 : CollatzResearch.WordTrace tailWord_4013714 prefixEnd_4013714 1373976327786809706144181 := by
  unfold tailWord_4013714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598044045251785155460049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97594784120671427081226797 36598044045251785155460049)
  ·
    refine ⟨27448533033938838866595037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36598044045251785155460049 27448533033938838866595037)
    ·
      refine ⟨10293199887727064574973139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27448533033938838866595037 10293199887727064574973139)
      ·
        refine ⟨15439799831590596862459709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293199887727064574973139 15439799831590596862459709)
        ·
          refine ⟨5789924936846473823422391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15439799831590596862459709 5789924936846473823422391)
          ·
            refine ⟨8684887405269710735133587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789924936846473823422391 8684887405269710735133587)
            ·
              refine ⟨13027331107904566102700381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8684887405269710735133587 13027331107904566102700381)
              ·
                refine ⟨4885249165464212288512643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13027331107904566102700381 4885249165464212288512643)
                ·
                  refine ⟨7327873748196318432768965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885249165464212288512643 7327873748196318432768965)
                  ·
                    refine ⟨1373976327786809706144181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327873748196318432768965 1373976327786809706144181)
                    ·
                      rfl

theorem cell22_4013714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4013714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013714 prefixEnd_4013714 := by exact prefixLift 4013714
  have htrace : WordTrace (prefixWord ++ tailWord_4013714) baseStart_4013714 baseEnd_4013714 := by
    simpa [prefixWord, tailWord_4013714, baseEnd_4013714] using wordTrace_append hprefix tailTrace_4013714
  have hstable : (prefixWord ++ tailWord_4013714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013714).length < 2 ^ (prefixWord ++ tailWord_4013714).sum := by decide
  have hdescent : baseEnd_4013714 < baseStart_4013714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013725 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4013725 : Nat := 118140960795 + 4013725 * 2 ^ 59
def prefixEnd_4013725 : Nat := 4983230072969 + 3 ^ 40 * 4013725 * 2
def baseEnd_4013725 : Nat := 1373980093311609344119147

theorem tailTrace_4013725 : CollatzResearch.WordTrace tailWord_4013725 prefixEnd_4013725 1373980093311609344119147 := by
  unfold tailWord_4013725
  simp only [CollatzResearch.WordTrace]
  refine ⟨146392577383967289500490629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97595051589311526333660419 146392577383967289500490629)
  ·
    refine ⟨27448608259493866781341993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146392577383967289500490629 27448608259493866781341993)
    ·
      refine ⟨20586456194620400086006495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27448608259493866781341993 20586456194620400086006495)
      ·
        refine ⟨30879684291930600129009743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20586456194620400086006495 30879684291930600129009743)
        ·
          refine ⟨46319526437895900193514615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30879684291930600129009743 46319526437895900193514615)
          ·
            refine ⟨69479289656843850290271923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46319526437895900193514615 69479289656843850290271923)
            ·
              refine ⟨104218934485265775435407885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69479289656843850290271923 104218934485265775435407885)
              ·
                refine ⟨39082100431974665788277957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104218934485265775435407885 39082100431974665788277957)
                ·
                  refine ⟨7327893830995249835302117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39082100431974665788277957 7327893830995249835302117)
                  ·
                    refine ⟨1373980093311609344119147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7327893830995249835302117 1373980093311609344119147)
                    ·
                      rfl

theorem cell22_4013725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4013725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013725 prefixEnd_4013725 := by exact prefixLift 4013725
  have htrace : WordTrace (prefixWord ++ tailWord_4013725) baseStart_4013725 baseEnd_4013725 := by
    simpa [prefixWord, tailWord_4013725, baseEnd_4013725] using wordTrace_append hprefix tailTrace_4013725
  have hstable : (prefixWord ++ tailWord_4013725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013725).length < 2 ^ (prefixWord ++ tailWord_4013725).sum := by decide
  have hdescent : baseEnd_4013725 < baseStart_4013725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013785 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 7]
def baseStart_4013785 : Nat := 118140960795 + 4013785 * 2 ^ 59
def prefixEnd_4013785 : Nat := 4983230072969 + 3 ^ 40 * 4013785 * 2
def baseEnd_4013785 : Nat := 458000210845929729206321

theorem tailTrace_4013785 : CollatzResearch.WordTrace tailWord_4013785 prefixEnd_4013785 458000210845929729206321 := by
  unfold tailWord_4013785
  simp only [CollatzResearch.WordTrace]
  refine ⟨146394765763749919747674809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97596510509166613165116539 146394765763749919747674809)
  ·
    refine ⟨109796074322812439810756107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146394765763749919747674809 109796074322812439810756107)
    ·
      refine ⟨164694111484218659716134161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109796074322812439810756107 164694111484218659716134161)
      ·
        refine ⟨123520583613163994787100621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164694111484218659716134161 123520583613163994787100621)
        ·
          refine ⟨46320218854936498045162733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123520583613163994787100621 46320218854936498045162733)
          ·
            refine ⟨17370082070601186766936025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46320218854936498045162733 17370082070601186766936025)
            ·
              refine ⟨13027561552950890075202019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17370082070601186766936025 13027561552950890075202019)
              ·
                refine ⟨19541342329426335112803029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13027561552950890075202019 19541342329426335112803029)
                ·
                  refine ⟨458000210845929729206321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19541342329426335112803029 458000210845929729206321)
                  ·
                    rfl

theorem cell22_4013785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_4013785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013785 prefixEnd_4013785 := by exact prefixLift 4013785
  have htrace : WordTrace (prefixWord ++ tailWord_4013785) baseStart_4013785 baseEnd_4013785 := by
    simpa [prefixWord, tailWord_4013785, baseEnd_4013785] using wordTrace_append hprefix tailTrace_4013785
  have hstable : (prefixWord ++ tailWord_4013785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013785).length < 2 ^ (prefixWord ++ tailWord_4013785).sum := by decide
  have hdescent : baseEnd_4013785 < baseStart_4013785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013896 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_4013896 : Nat := 118140960795 + 4013896 * 2 ^ 59
def prefixEnd_4013896 : Nat := 4983230072969 + 3 ^ 40 * 4013896 * 2
def baseEnd_4013896 : Nat := 1374038630106221898093623

theorem tailTrace_4013896 : CollatzResearch.WordTrace tailWord_4013896 prefixEnd_4013896 1374038630106221898093623 := by
  unfold tailWord_4013896
  simp only [CollatzResearch.WordTrace]
  refine ⟨73199407133173892852482771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97599209510898523803310361 73199407133173892852482771)
  ·
    refine ⟨109799110699760839278724157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73199407133173892852482771 109799110699760839278724157)
    ·
      refine ⟨41174666512410314729521559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109799110699760839278724157 41174666512410314729521559)
      ·
        refine ⟨61761999768615472094282339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41174666512410314729521559 61761999768615472094282339)
        ·
          refine ⟨92642999652923208141423509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61761999768615472094282339 92642999652923208141423509)
          ·
            refine ⟨4342640608730775381629227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92642999652923208141423509 4342640608730775381629227)
            ·
              refine ⟨6513960913096163072443841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342640608730775381629227 6513960913096163072443841)
              ·
                refine ⟨4885470684822122304332881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513960913096163072443841 4885470684822122304332881)
                ·
                  refine ⟨3664103013616591728249661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885470684822122304332881 3664103013616591728249661)
                  ·
                    refine ⟨1374038630106221898093623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664103013616591728249661 1374038630106221898093623)
                    ·
                      rfl

theorem cell22_4013896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_4013896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013896 prefixEnd_4013896 := by exact prefixLift 4013896
  have htrace : WordTrace (prefixWord ++ tailWord_4013896) baseStart_4013896 baseEnd_4013896 := by
    simpa [prefixWord, tailWord_4013896, baseEnd_4013896] using wordTrace_append hprefix tailTrace_4013896
  have hstable : (prefixWord ++ tailWord_4013896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013896).length < 2 ^ (prefixWord ++ tailWord_4013896).sum := by decide
  have hdescent : baseEnd_4013896 < baseStart_4013896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013999 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 4]
def baseStart_4013999 : Nat := 118140960795 + 4013999 * 2 ^ 59
def prefixEnd_4013999 : Nat := 4983230072969 + 3 ^ 40 * 4013999 * 2
def baseEnd_4013999 : Nat := 458024629703721320922769

theorem tailTrace_4013999 : CollatzResearch.WordTrace tailWord_4013999 prefixEnd_4013999 458024629703721320922769 := by
  unfold tailWord_4013999
  simp only [CollatzResearch.WordTrace]
  refine ⟨146402570984974634295965051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97601713989983089530643367 146402570984974634295965051)
  ·
    refine ⟨219603856477461951443947577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146402570984974634295965051 219603856477461951443947577)
    ·
      refine ⟨164702892358096463582960683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219603856477461951443947577 164702892358096463582960683)
      ·
        refine ⟨247054338537144695374441025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164702892358096463582960683 247054338537144695374441025)
        ·
          refine ⟨185290753902858521530830769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247054338537144695374441025 185290753902858521530830769)
          ·
            refine ⟨138968065427143891148123077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185290753902858521530830769 138968065427143891148123077)
            ·
              refine ⟨26056512267589479590273077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138968065427143891148123077 26056512267589479590273077)
              ·
                refine ⟨2442798025086513711588101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26056512267589479590273077 2442798025086513711588101)
                ·
                  refine ⟨458024629703721320922769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442798025086513711588101 458024629703721320922769)
                  ·
                    rfl

theorem cell22_4013999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 4].length) (baseStart_4013999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4013999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4013999 prefixEnd_4013999 := by exact prefixLift 4013999
  have htrace : WordTrace (prefixWord ++ tailWord_4013999) baseStart_4013999 baseEnd_4013999 := by
    simpa [prefixWord, tailWord_4013999, baseEnd_4013999] using wordTrace_append hprefix tailTrace_4013999
  have hstable : (prefixWord ++ tailWord_4013999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013999).length < 2 ^ (prefixWord ++ tailWord_4013999).sum := by decide
  have hdescent : baseEnd_4013999 < baseStart_4013999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014050 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_4014050 : Nat := 118140960795 + 4014050 * 2 ^ 59
def prefixEnd_4014050 : Nat := 4983230072969 + 3 ^ 40 * 4014050 * 2
def baseEnd_4014050 : Nat := 458030449151138943247717

theorem tailTrace_4014050 : CollatzResearch.WordTrace tailWord_4014050 prefixEnd_4014050 458030449151138943247717 := by
  unfold tailWord_4014050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601107776947467501517901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97602954071859913337381069 36601107776947467501517901)
  ·
    refine ⟨13725415416355300313069213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36601107776947467501517901 13725415416355300313069213)
    ·
      refine ⟨5147030781133237617400955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13725415416355300313069213 5147030781133237617400955)
      ·
        refine ⟨7720546171699856426101433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147030781133237617400955 7720546171699856426101433)
        ·
          refine ⟨5790409628774892319576075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7720546171699856426101433 5790409628774892319576075)
          ·
            refine ⟨8685614443162338479364113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790409628774892319576075 8685614443162338479364113)
            ·
              refine ⟨6514210832371753859523085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685614443162338479364113 6514210832371753859523085)
              ·
                refine ⟨2442829062139407697321157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6514210832371753859523085 2442829062139407697321157)
                ·
                  refine ⟨458030449151138943247717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442829062139407697321157 458030449151138943247717)
                  ·
                    rfl

theorem cell22_4014050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_4014050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014050 prefixEnd_4014050 := by exact prefixLift 4014050
  have htrace : WordTrace (prefixWord ++ tailWord_4014050) baseStart_4014050 baseEnd_4014050 := by
    simpa [prefixWord, tailWord_4014050, baseEnd_4014050] using wordTrace_append hprefix tailTrace_4014050
  have hstable : (prefixWord ++ tailWord_4014050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014050).length < 2 ^ (prefixWord ++ tailWord_4014050).sum := by decide
  have hdescent : baseEnd_4014050 < baseStart_4014050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014061 : List Nat := [1, 5, 1, 4, 1, 1, 9]
def baseStart_4014061 : Nat := 118140960795 + 4014061 * 2 ^ 59
def prefixEnd_4014061 : Nat := 4983230072969 + 3 ^ 40 * 4014061 * 2
def baseEnd_4014061 : Nat := 50892411591785795100671

theorem tailTrace_4014061 : CollatzResearch.WordTrace tailWord_4014061 prefixEnd_4014061 50892411591785795100671 := by
  unfold tailWord_4014061
  simp only [CollatzResearch.WordTrace]
  refine ⟨146404832310750018884722037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97603221540500012589814691 146404832310750018884722037)
  ·
    refine ⟨13725453029132814270442691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146404832310750018884722037 13725453029132814270442691)
    ·
      refine ⟨20588179543699221405664037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13725453029132814270442691 20588179543699221405664037)
      ·
        refine ⟨3860283664443604013562007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20588179543699221405664037 3860283664443604013562007)
        ·
          refine ⟨5790425496665406020343011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860283664443604013562007 5790425496665406020343011)
          ·
            refine ⟨8685638244998109030514517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790425496665406020343011 8685638244998109030514517)
            ·
              refine ⟨50892411591785795100671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8685638244998109030514517 50892411591785795100671)
              ·
                rfl

theorem cell22_4014061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 9].length) (baseStart_4014061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014061 prefixEnd_4014061 := by exact prefixLift 4014061
  have htrace : WordTrace (prefixWord ++ tailWord_4014061) baseStart_4014061 baseEnd_4014061 := by
    simpa [prefixWord, tailWord_4014061, baseEnd_4014061] using wordTrace_append hprefix tailTrace_4014061
  have hstable : (prefixWord ++ tailWord_4014061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014061).length < 2 ^ (prefixWord ++ tailWord_4014061).sum := by decide
  have hdescent : baseEnd_4014061 < baseStart_4014061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014065 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_4014065 : Nat := 118140960795 + 4014065 * 2 ^ 59
def prefixEnd_4014065 : Nat := 4983230072969 + 3 ^ 40 * 4014065 * 2
def baseEnd_4014065 : Nat := 1374096482259961790618105

theorem tailTrace_4014065 : CollatzResearch.WordTrace tailWord_4014065 prefixEnd_4014065 1374096482259961790618105 := by
  unfold tailWord_4014065
  simp only [CollatzResearch.WordTrace]
  refine ⟨146404978202735527567867649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97603318801823685045245099 146404978202735527567867649)
  ·
    refine ⟨109803733652051645675900737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146404978202735527567867649 109803733652051645675900737)
    ·
      refine ⟨82352800239038734256925553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109803733652051645675900737 82352800239038734256925553)
      ·
        refine ⟨61764600179279050692694165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82352800239038734256925553 61764600179279050692694165)
        ·
          refine ⟨2895215633403705501220039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61764600179279050692694165 2895215633403705501220039)
          ·
            refine ⟨4342823450105558251830059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895215633403705501220039 4342823450105558251830059)
            ·
              refine ⟨6514235175158337377745089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342823450105558251830059 6514235175158337377745089)
              ·
                refine ⟨4885676381368753033308817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6514235175158337377745089 4885676381368753033308817)
                ·
                  refine ⟨3664257286026564774981613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885676381368753033308817 3664257286026564774981613)
                  ·
                    refine ⟨1374096482259961790618105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664257286026564774981613 1374096482259961790618105)
                    ·
                      rfl

theorem cell22_4014065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_4014065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014065 prefixEnd_4014065 := by exact prefixLift 4014065
  have htrace : WordTrace (prefixWord ++ tailWord_4014065) baseStart_4014065 baseEnd_4014065 := by
    simpa [prefixWord, tailWord_4014065, baseEnd_4014065] using wordTrace_append hprefix tailTrace_4014065
  have hstable : (prefixWord ++ tailWord_4014065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014065).length < 2 ^ (prefixWord ++ tailWord_4014065).sum := by decide
  have hdescent : baseEnd_4014065 < baseStart_4014065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014076 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_4014076 : Nat := 118140960795 + 4014076 * 2 ^ 59
def prefixEnd_4014076 : Nat := 4983230072969 + 3 ^ 40 * 4014076 * 2
def baseEnd_4014076 : Nat := 1374100247784761428593071

theorem tailTrace_4014076 : CollatzResearch.WordTrace tailWord_4014076 prefixEnd_4014076 1374100247784761428593071 := by
  unfold tailWord_4014076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73202689702847838223259041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97603586270463784297678721 73202689702847838223259041)
  ·
    refine ⟨54902017277135878667444281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73202689702847838223259041 54902017277135878667444281)
    ·
      refine ⟨41176512957851909000583211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54902017277135878667444281 41176512957851909000583211)
      ·
        refine ⟨61764769436777863500874817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41176512957851909000583211 61764769436777863500874817)
        ·
          refine ⟨46323577077583397625656113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61764769436777863500874817 46323577077583397625656113)
          ·
            refine ⟨34742682808187548219242085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46323577077583397625656113 34742682808187548219242085)
            ·
              refine ⟨6514253026535165291107891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34742682808187548219242085 6514253026535165291107891)
              ·
                refine ⟨9771379539802747936661837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514253026535165291107891 9771379539802747936661837)
                ·
                  refine ⟨3664267327426030476248189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9771379539802747936661837 3664267327426030476248189)
                  ·
                    refine ⟨1374100247784761428593071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664267327426030476248189 1374100247784761428593071)
                    ·
                      rfl

theorem cell22_4014076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_4014076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014076 prefixEnd_4014076 := by exact prefixLift 4014076
  have htrace : WordTrace (prefixWord ++ tailWord_4014076) baseStart_4014076 baseEnd_4014076 := by
    simpa [prefixWord, tailWord_4014076, baseEnd_4014076] using wordTrace_append hprefix tailTrace_4014076
  have hstable : (prefixWord ++ tailWord_4014076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014076).length < 2 ^ (prefixWord ++ tailWord_4014076).sum := by decide
  have hdescent : baseEnd_4014076 < baseStart_4014076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014149 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_4014149 : Nat := 118140960795 + 4014149 * 2 ^ 59
def prefixEnd_4014149 : Nat := 4983230072969 + 3 ^ 40 * 4014149 * 2
def baseEnd_4014149 : Nat := 1374125237176613571517847

theorem tailTrace_4014149 : CollatzResearch.WordTrace tailWord_4014149 prefixEnd_4014149 1374125237176613571517847 := by
  unfold tailWord_4014149
  simp only [CollatzResearch.WordTrace]
  refine ⟨146408041934431209913925501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97605361289620806609283667 146408041934431209913925501)
  ·
    refine ⟨54903015725411703717722063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146408041934431209913925501 54903015725411703717722063)
    ·
      refine ⟨82354523588117555576583095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54903015725411703717722063 82354523588117555576583095)
      ·
        refine ⟨123531785382176333364874643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82354523588117555576583095 123531785382176333364874643)
        ·
          refine ⟨185297678073264500047311965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123531785382176333364874643 185297678073264500047311965)
          ·
            refine ⟨69486629277474187517741987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185297678073264500047311965 69486629277474187517741987)
            ·
              refine ⟨104229943916211281276612981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69486629277474187517741987 104229943916211281276612981)
              ·
                refine ⟨9771557242144807619682467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104229943916211281276612981 9771557242144807619682467)
                ·
                  refine ⟨14657335863217211429523701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771557242144807619682467 14657335863217211429523701)
                  ·
                    refine ⟨1374125237176613571517847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14657335863217211429523701 1374125237176613571517847)
                    ·
                      rfl

theorem cell22_4014149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_4014149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014149 prefixEnd_4014149 := by exact prefixLift 4014149
  have htrace : WordTrace (prefixWord ++ tailWord_4014149) baseStart_4014149 baseEnd_4014149 := by
    simpa [prefixWord, tailWord_4014149, baseEnd_4014149] using wordTrace_append hprefix tailTrace_4014149
  have hstable : (prefixWord ++ tailWord_4014149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014149).length < 2 ^ (prefixWord ++ tailWord_4014149).sum := by decide
  have hdescent : baseEnd_4014149 < baseStart_4014149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014181 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_4014181 : Nat := 118140960795 + 4014181 * 2 ^ 59
def prefixEnd_4014181 : Nat := 4983230072969 + 3 ^ 40 * 4014181 * 2
def baseEnd_4014181 : Nat := 1374136191430576154717749

theorem tailTrace_4014181 : CollatzResearch.WordTrace tailWord_4014181 prefixEnd_4014181 1374136191430576154717749 := by
  unfold tailWord_4014181
  simp only [CollatzResearch.WordTrace]
  refine ⟨146409209070315279379090397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97606139380210186252726931 146409209070315279379090397)
  ·
    refine ⟨54903453401368229767158899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146409209070315279379090397 54903453401368229767158899)
    ·
      refine ⟨82355180102052344650738349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54903453401368229767158899 82355180102052344650738349)
      ·
        refine ⟨30883192538269629244026881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82355180102052344650738349 30883192538269629244026881)
        ·
          refine ⟨23162394403702221933020161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30883192538269629244026881 23162394403702221933020161)
          ·
            refine ⟨17371795802776666449765121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23162394403702221933020161 17371795802776666449765121)
            ·
              refine ⟨13028846852082499837323841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17371795802776666449765121 13028846852082499837323841)
              ·
                refine ⟨9771635139061874877992881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028846852082499837323841 9771635139061874877992881)
                ·
                  refine ⟨7328726354296406158494661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9771635139061874877992881 7328726354296406158494661)
                  ·
                    refine ⟨1374136191430576154717749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7328726354296406158494661 1374136191430576154717749)
                    ·
                      rfl

theorem cell22_4014181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_4014181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014181 prefixEnd_4014181 := by exact prefixLift 4014181
  have htrace : WordTrace (prefixWord ++ tailWord_4014181) baseStart_4014181 baseEnd_4014181 := by
    simpa [prefixWord, tailWord_4014181, baseEnd_4014181] using wordTrace_append hprefix tailTrace_4014181
  have hstable : (prefixWord ++ tailWord_4014181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014181).length < 2 ^ (prefixWord ++ tailWord_4014181).sum := by decide
  have hdescent : baseEnd_4014181 < baseStart_4014181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014183 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4014183 : Nat := 118140960795 + 4014183 * 2 ^ 59
def prefixEnd_4014183 : Nat := 4983230072969 + 3 ^ 40 * 4014183 * 2
def baseEnd_4014183 : Nat := 1374136876071448816167743

theorem tailTrace_4014183 : CollatzResearch.WordTrace tailWord_4014183 prefixEnd_4014183 1374136876071448816167743 := by
  unfold tailWord_4014183
  simp only [CollatzResearch.WordTrace]
  refine ⟨146409282016308033720663203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97606188010872022480442135 146409282016308033720663203)
  ·
    refine ⟨219613923024462050580994805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146409282016308033720663203 219613923024462050580994805)
    ·
      refine ⟨20588805283543317241968263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219613923024462050580994805 20588805283543317241968263)
      ·
        refine ⟨30883207925314975862952395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20588805283543317241968263 30883207925314975862952395)
        ·
          refine ⟨46324811887972463794428593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30883207925314975862952395 46324811887972463794428593)
          ·
            refine ⟨34743608915979347845821445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46324811887972463794428593 34743608915979347845821445)
            ·
              refine ⟨6514426671746127721091521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34743608915979347845821445 6514426671746127721091521)
              ·
                refine ⟨4885820003809595790818641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6514426671746127721091521 4885820003809595790818641)
                ·
                  refine ⟨3664365002857196843113981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885820003809595790818641 3664365002857196843113981)
                  ·
                    refine ⟨1374136876071448816167743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664365002857196843113981 1374136876071448816167743)
                    ·
                      rfl

theorem cell22_4014183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4014183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014183 prefixEnd_4014183 := by exact prefixLift 4014183
  have htrace : WordTrace (prefixWord ++ tailWord_4014183) baseStart_4014183 baseEnd_4014183 := by
    simpa [prefixWord, tailWord_4014183, baseEnd_4014183] using wordTrace_append hprefix tailTrace_4014183
  have hstable : (prefixWord ++ tailWord_4014183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014183).length < 2 ^ (prefixWord ++ tailWord_4014183).sum := by decide
  have hdescent : baseEnd_4014183 < baseStart_4014183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014211 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 5, 3]
def baseStart_4014211 : Nat := 118140960795 + 4014211 * 2 ^ 59
def prefixEnd_4014211 : Nat := 4983230072969 + 3 ^ 40 * 4014211 * 2
def baseEnd_4014211 : Nat := 1374146461043666076467657

theorem tailTrace_4014211 : CollatzResearch.WordTrace tailWord_4014211 prefixEnd_4014211 1374146461043666076467657 := by
  unfold tailWord_4014211
  simp only [CollatzResearch.WordTrace]
  refine ⟨146410303260206594502682487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97606868840137729668454991 146410303260206594502682487)
  ·
    refine ⟨219615454890309891754023731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146410303260206594502682487 219615454890309891754023731)
    ·
      refine ⟨329423182335464837631035597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219615454890309891754023731 329423182335464837631035597)
      ·
        refine ⟨123533693375799314111638349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329423182335464837631035597 123533693375799314111638349)
        ·
          refine ⟨46325135015924742791864381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123533693375799314111638349 46325135015924742791864381)
          ·
            refine ⟨17371925630971778546949143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46325135015924742791864381 17371925630971778546949143)
            ·
              refine ⟨26057888446457667820423715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371925630971778546949143 26057888446457667820423715)
              ·
                refine ⟨39086832669686501730635573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26057888446457667820423715 39086832669686501730635573)
                ·
                  refine ⟨3664390562783109537247085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39086832669686501730635573 3664390562783109537247085)
                  ·
                    refine ⟨1374146461043666076467657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664390562783109537247085 1374146461043666076467657)
                    ·
                      rfl

theorem cell22_4014211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3].length) (baseStart_4014211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014211 prefixEnd_4014211 := by exact prefixLift 4014211
  have htrace : WordTrace (prefixWord ++ tailWord_4014211) baseStart_4014211 baseEnd_4014211 := by
    simpa [prefixWord, tailWord_4014211, baseEnd_4014211] using wordTrace_append hprefix tailTrace_4014211
  have hstable : (prefixWord ++ tailWord_4014211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014211).length < 2 ^ (prefixWord ++ tailWord_4014211).sum := by decide
  have hdescent : baseEnd_4014211 < baseStart_4014211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014224 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_4014224 : Nat := 118140960795 + 4014224 * 2 ^ 59
def prefixEnd_4014224 : Nat := 4983230072969 + 3 ^ 40 * 4014224 * 2
def baseEnd_4014224 : Nat := 458050303736446125297539

theorem tailTrace_4014224 : CollatzResearch.WordTrace tailWord_4014224 prefixEnd_4014224 458050303736446125297539 := by
  unfold tailWord_4014224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73205388704579748861452863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97607184939439665148603817 73205388704579748861452863)
  ·
    refine ⟨109808083056869623292179295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73205388704579748861452863 109808083056869623292179295)
    ·
      refine ⟨164712124585304434938268943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109808083056869623292179295 164712124585304434938268943)
      ·
        refine ⟨247068186877956652407403415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164712124585304434938268943 247068186877956652407403415)
        ·
          refine ⟨370602280316934978611105123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247068186877956652407403415 370602280316934978611105123)
          ·
            refine ⟨555903420475402467916657685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370602280316934978611105123 555903420475402467916657685)
            ·
              refine ⟨26057972834784490683593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 555903420475402467916657685 26057972834784490683593329)
              ·
                refine ⟨19543479626088368012694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26057972834784490683593329 19543479626088368012694997)
                ·
                  refine ⟨458050303736446125297539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19543479626088368012694997 458050303736446125297539)
                  ·
                    rfl

theorem cell22_4014224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_4014224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014224 prefixEnd_4014224 := by exact prefixLift 4014224
  have htrace : WordTrace (prefixWord ++ tailWord_4014224) baseStart_4014224 baseEnd_4014224 := by
    simpa [prefixWord, tailWord_4014224, baseEnd_4014224] using wordTrace_append hprefix tailTrace_4014224
  have hstable : (prefixWord ++ tailWord_4014224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014224).length < 2 ^ (prefixWord ++ tailWord_4014224).sum := by decide
  have hdescent : baseEnd_4014224 < baseStart_4014224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014241 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 7]
def baseStart_4014241 : Nat := 118140960795 + 4014241 * 2 ^ 59
def prefixEnd_4014241 : Nat := 4983230072969 + 3 ^ 40 * 4014241 * 2
def baseEnd_4014241 : Nat := 458052243552251999405855

theorem tailTrace_4014241 : CollatzResearch.WordTrace tailWord_4014241 prefixEnd_4014241 458052243552251999405855 := by
  unfold tailWord_4014241
  simp only [CollatzResearch.WordTrace]
  refine ⟨146411397450097909626274577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97607598300065273084183051 146411397450097909626274577)
  ·
    refine ⟨109808548087573432219705933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146411397450097909626274577 109808548087573432219705933)
    ·
      refine ⟨41178205532840037082389725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109808548087573432219705933 41178205532840037082389725)
      ·
        refine ⟨15441827074815013905896147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41178205532840037082389725 15441827074815013905896147)
        ·
          refine ⟨23162740612222520858844221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15441827074815013905896147 23162740612222520858844221)
          ·
            refine ⟨8686027729583445322066583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23162740612222520858844221 8686027729583445322066583)
            ·
              refine ⟨13029041594375167983099875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686027729583445322066583 13029041594375167983099875)
              ·
                refine ⟨19543562391562751974649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13029041594375167983099875 19543562391562751974649813)
                ·
                  refine ⟨458052243552251999405855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19543562391562751974649813 458052243552251999405855)
                  ·
                    rfl

theorem cell22_4014241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_4014241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014241 prefixEnd_4014241 := by exact prefixLift 4014241
  have htrace : WordTrace (prefixWord ++ tailWord_4014241) baseStart_4014241 baseEnd_4014241 := by
    simpa [prefixWord, tailWord_4014241, baseEnd_4014241] using wordTrace_append hprefix tailTrace_4014241
  have hstable : (prefixWord ++ tailWord_4014241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014241).length < 2 ^ (prefixWord ++ tailWord_4014241).sum := by decide
  have hdescent : baseEnd_4014241 < baseStart_4014241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014258 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_4014258 : Nat := 118140960795 + 4014258 * 2 ^ 59
def prefixEnd_4014258 : Nat := 4983230072969 + 3 ^ 40 * 4014258 * 2
def baseEnd_4014258 : Nat := 458054183368057873514171

theorem tailTrace_4014258 : CollatzResearch.WordTrace tailWord_4014258 prefixEnd_4014258 458054183368057873514171 := by
  unfold tailWord_4014258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603004372759080382410857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97608011660690881019762285 36603004372759080382410857)
  ·
    refine ⟨27452253279569310286808143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36603004372759080382410857 27452253279569310286808143)
    ·
      refine ⟨41178379919353965430212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27452253279569310286808143 41178379919353965430212215)
      ·
        refine ⟨61767569879030948145318323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41178379919353965430212215 61767569879030948145318323)
        ·
          refine ⟨92651354818546422217977485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61767569879030948145318323 92651354818546422217977485)
          ·
            refine ⟨34744258056954908331741557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92651354818546422217977485 34744258056954908331741557)
            ·
              refine ⟨3257274192839522656100771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34744258056954908331741557 3257274192839522656100771)
              ·
                refine ⟨4885911289259283984151157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257274192839522656100771 4885911289259283984151157)
                ·
                  refine ⟨458054183368057873514171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4885911289259283984151157 458054183368057873514171)
                  ·
                    rfl

theorem cell22_4014258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_4014258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014258 prefixEnd_4014258 := by exact prefixLift 4014258
  have htrace : WordTrace (prefixWord ++ tailWord_4014258) baseStart_4014258 baseEnd_4014258 := by
    simpa [prefixWord, tailWord_4014258, baseEnd_4014258] using wordTrace_append hprefix tailTrace_4014258
  have hstable : (prefixWord ++ tailWord_4014258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014258).length < 2 ^ (prefixWord ++ tailWord_4014258).sum := by decide
  have hdescent : baseEnd_4014258 < baseStart_4014258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014316 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_4014316 : Nat := 118140960795 + 4014316 * 2 ^ 59
def prefixEnd_4014316 : Nat := 4983230072969 + 3 ^ 40 * 4014316 * 2
def baseEnd_4014316 : Nat := 1374182404689480802592335

theorem tailTrace_4014316 : CollatzResearch.WordTrace tailWord_4014316 prefixEnd_4014316 1374182404689480802592335 := by
  unfold tailWord_4014316
  simp only [CollatzResearch.WordTrace]
  refine ⟨73207066462413098717627401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97609421949884131623503201 73207066462413098717627401)
  ·
    refine ⟨54905299846809824038220551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73207066462413098717627401 54905299846809824038220551)
    ·
      refine ⟨82357949770214736057330827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54905299846809824038220551 82357949770214736057330827)
      ·
        refine ⟨123536924655322104085996241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82357949770214736057330827 123536924655322104085996241)
        ·
          refine ⟨92652693491491578064497181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123536924655322104085996241 92652693491491578064497181)
          ·
            refine ⟨34744760059309341774186443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92652693491491578064497181 34744760059309341774186443)
            ·
              refine ⟨52117140088964012661279665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34744760059309341774186443 52117140088964012661279665)
              ·
                refine ⟨39087855066723009495959749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52117140088964012661279665 39087855066723009495959749)
                ·
                  refine ⟨7328972825010564280492453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39087855066723009495959749 7328972825010564280492453)
                  ·
                    refine ⟨1374182404689480802592335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7328972825010564280492453 1374182404689480802592335)
                    ·
                      rfl

theorem cell22_4014316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_4014316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014316 prefixEnd_4014316 := by exact prefixLift 4014316
  have htrace : WordTrace (prefixWord ++ tailWord_4014316) baseStart_4014316 baseEnd_4014316 := by
    simpa [prefixWord, tailWord_4014316, baseEnd_4014316] using wordTrace_append hprefix tailTrace_4014316
  have hstable : (prefixWord ++ tailWord_4014316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014316).length < 2 ^ (prefixWord ++ tailWord_4014316).sum := by decide
  have hdescent : baseEnd_4014316 < baseStart_4014316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014365 : List Nat := [1, 4, 2, 3, 2, 2, 1, 7]
def baseStart_4014365 : Nat := 118140960795 + 4014365 * 2 ^ 59
def prefixEnd_4014365 : Nat := 4983230072969 + 3 ^ 40 * 4014365 * 2
def baseEnd_4014365 : Nat := 152688797598984556457465

theorem tailTrace_4014365 : CollatzResearch.WordTrace tailWord_4014365 prefixEnd_4014365 152688797598984556457465 := by
  unfold tailWord_4014365
  simp only [CollatzResearch.WordTrace]
  refine ⟨146415920101648678803788549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97610613401099119202525699 146415920101648678803788549)
  ·
    refine ⟨27452985019059127275710353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146415920101648678803788549 27452985019059127275710353)
    ·
      refine ⟨20589738764294345456782765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27452985019059127275710353 20589738764294345456782765)
      ·
        refine ⟨7721152036610379546293537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20589738764294345456782765 7721152036610379546293537)
        ·
          refine ⟨5790864027457784659720153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7721152036610379546293537 5790864027457784659720153)
          ·
            refine ⟨4343148020593338494790115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5790864027457784659720153 4343148020593338494790115)
            ·
              refine ⟨6514722030890007742185173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343148020593338494790115 6514722030890007742185173)
              ·
                refine ⟨152688797598984556457465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6514722030890007742185173 152688797598984556457465)
                ·
                  rfl

theorem cell22_4014365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 7].length) (baseStart_4014365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014365 prefixEnd_4014365 := by exact prefixLift 4014365
  have htrace : WordTrace (prefixWord ++ tailWord_4014365) baseStart_4014365 baseEnd_4014365 := by
    simpa [prefixWord, tailWord_4014365, baseEnd_4014365] using wordTrace_append hprefix tailTrace_4014365
  have hstable : (prefixWord ++ tailWord_4014365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014365).length < 2 ^ (prefixWord ++ tailWord_4014365).sum := by decide
  have hdescent : baseEnd_4014365 < baseStart_4014365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014382 : List Nat := [4, 1, 3, 3, 1, 1, 3, 6]
def baseStart_4014382 : Nat := 118140960795 + 4014382 * 2 ^ 59
def prefixEnd_4014382 : Nat := 4983230072969 + 3 ^ 40 * 4014382 * 2
def baseEnd_4014382 : Nat := 152689444204253181160237

theorem tailTrace_4014382 : CollatzResearch.WordTrace tailWord_4014382 prefixEnd_4014382 152689444204253181160237 := by
  unfold tailWord_4014382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302067517823386338394675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97611026761724727138104933 18302067517823386338394675)
  ·
    refine ⟨27453101276735079507592013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18302067517823386338394675 27453101276735079507592013)
    ·
      refine ⟨10294912978775654815347005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27453101276735079507592013 10294912978775654815347005)
      ·
        refine ⟨3860592367040870555755127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10294912978775654815347005 3860592367040870555755127)
        ·
          refine ⟨5790888550561305833632691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860592367040870555755127 5790888550561305833632691)
          ·
            refine ⟨8686332825841958750449037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790888550561305833632691 8686332825841958750449037)
            ·
              refine ⟨3257374809690734531418389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8686332825841958750449037 3257374809690734531418389)
              ·
                refine ⟨152689444204253181160237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3257374809690734531418389 152689444204253181160237)
                ·
                  rfl

theorem cell22_4014382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_4014382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014382 prefixEnd_4014382 := by exact prefixLift 4014382
  have htrace : WordTrace (prefixWord ++ tailWord_4014382) baseStart_4014382 baseEnd_4014382 := by
    simpa [prefixWord, tailWord_4014382, baseEnd_4014382] using wordTrace_append hprefix tailTrace_4014382
  have hstable : (prefixWord ++ tailWord_4014382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014382).length < 2 ^ (prefixWord ++ tailWord_4014382).sum := by decide
  have hdescent : baseEnd_4014382 < baseStart_4014382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014440 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4014440 : Nat := 118140960795 + 4014440 * 2 ^ 59
def prefixEnd_4014440 : Nat := 4983230072969 + 3 ^ 40 * 4014440 * 2
def baseEnd_4014440 : Nat := 1374224852423585812491955

theorem tailTrace_4014440 : CollatzResearch.WordTrace tailWord_4014440 prefixEnd_4014440 1374224852423585812491955 := by
  unfold tailWord_4014440
  simp only [CollatzResearch.WordTrace]
  refine ⟨73209327788188483306384387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97612437050917977741845849 73209327788188483306384387)
  ·
    refine ⟨109813991682282724959576581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73209327788188483306384387 109813991682282724959576581)
    ·
      refine ⟨20590123440428010929920609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109813991682282724959576581 20590123440428010929920609)
      ·
        refine ⟨15442592580321008197440457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20590123440428010929920609 15442592580321008197440457)
        ·
          refine ⟨11581944435240756148080343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15442592580321008197440457 11581944435240756148080343)
          ·
            refine ⟨17372916652861134222120515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581944435240756148080343 17372916652861134222120515)
            ·
              refine ⟨26059374979291701333180773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17372916652861134222120515 26059374979291701333180773)
              ·
                refine ⟨4886132808617193999971395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26059374979291701333180773 4886132808617193999971395)
                ·
                  refine ⟨7329199212925790999957093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886132808617193999971395 7329199212925790999957093)
                  ·
                    refine ⟨1374224852423585812491955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7329199212925790999957093 1374224852423585812491955)
                    ·
                      rfl

theorem cell22_4014440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4014440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014440 prefixEnd_4014440 := by exact prefixLift 4014440
  have htrace : WordTrace (prefixWord ++ tailWord_4014440) baseStart_4014440 baseEnd_4014440 := by
    simpa [prefixWord, tailWord_4014440, baseEnd_4014440] using wordTrace_append hprefix tailTrace_4014440
  have hstable : (prefixWord ++ tailWord_4014440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014440).length < 2 ^ (prefixWord ++ tailWord_4014440).sum := by decide
  have hdescent : baseEnd_4014440 < baseStart_4014440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014472 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_4014472 : Nat := 118140960795 + 4014472 * 2 ^ 59
def prefixEnd_4014472 : Nat := 4983230072969 + 3 ^ 40 * 4014472 * 2
def baseEnd_4014472 : Nat := 458078602225849465230619

theorem tailTrace_4014472 : CollatzResearch.WordTrace tailWord_4014472 prefixEnd_4014472 458078602225849465230619 := by
  unfold tailWord_4014472
  simp only [CollatzResearch.WordTrace]
  refine ⟨73209911356130518038966835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97613215141507357385289113 73209911356130518038966835)
  ·
    refine ⟨109814867034195777058450253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73209911356130518038966835 109814867034195777058450253)
    ·
      refine ⟨41180575137823416396918845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109814867034195777058450253 41180575137823416396918845)
      ·
        refine ⟨15442715676683781148844567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41180575137823416396918845 15442715676683781148844567)
        ·
          refine ⟨23164073515025671723266851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15442715676683781148844567 23164073515025671723266851)
          ·
            refine ⟨34746110272538507584900277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23164073515025671723266851 34746110272538507584900277)
            ·
              refine ⟨3257447838050485086084401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34746110272538507584900277 3257447838050485086084401)
              ·
                refine ⟨2443085878537863814563301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257447838050485086084401 2443085878537863814563301)
                ·
                  refine ⟨458078602225849465230619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443085878537863814563301 458078602225849465230619)
                  ·
                    rfl

theorem cell22_4014472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_4014472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014472 prefixEnd_4014472 := by exact prefixLift 4014472
  have htrace : WordTrace (prefixWord ++ tailWord_4014472) baseStart_4014472 baseEnd_4014472 := by
    simpa [prefixWord, tailWord_4014472, baseEnd_4014472] using wordTrace_append hprefix tailTrace_4014472
  have hstable : (prefixWord ++ tailWord_4014472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014472).length < 2 ^ (prefixWord ++ tailWord_4014472).sum := by decide
  have hdescent : baseEnd_4014472 < baseStart_4014472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014487 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 2, 3]
def baseStart_4014487 : Nat := 118140960795 + 4014487 * 2 ^ 59
def prefixEnd_4014487 : Nat := 4983230072969 + 3 ^ 40 * 4014487 * 2
def baseEnd_4014487 : Nat := 1374240941484093356566811

theorem tailTrace_4014487 : CollatzResearch.WordTrace tailWord_4014487 prefixEnd_4014487 1374240941484093356566811 := by
  unfold tailWord_4014487
  simp only [CollatzResearch.WordTrace]
  refine ⟨146420369807206693639729715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97613579871471129093153143 146420369807206693639729715)
  ·
    refine ⟨219630554710810040459594573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146420369807206693639729715 219630554710810040459594573)
    ·
      refine ⟨82361458016553765172347965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219630554710810040459594573 82361458016553765172347965)
      ·
        refine ⟨30885546756207661939630487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82361458016553765172347965 30885546756207661939630487)
        ·
          refine ⟨46328320134311492909445731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30885546756207661939630487 46328320134311492909445731)
          ·
            refine ⟨69492480201467239364168597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46328320134311492909445731 69492480201467239364168597)
            ·
              refine ⟨3257460009443776845195403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69492480201467239364168597 3257460009443776845195403)
              ·
                refine ⟨4886190014165665267793105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257460009443776845195403 4886190014165665267793105)
                ·
                  refine ⟨3664642510624248950844829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4886190014165665267793105 3664642510624248950844829)
                  ·
                    refine ⟨1374240941484093356566811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664642510624248950844829 1374240941484093356566811)
                    ·
                      rfl

theorem cell22_4014487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_4014487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014487 prefixEnd_4014487 := by exact prefixLift 4014487
  have htrace : WordTrace (prefixWord ++ tailWord_4014487) baseStart_4014487 baseEnd_4014487 := by
    simpa [prefixWord, tailWord_4014487, baseEnd_4014487] using wordTrace_append hprefix tailTrace_4014487
  have hstable : (prefixWord ++ tailWord_4014487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014487).length < 2 ^ (prefixWord ++ tailWord_4014487).sum := by decide
  have hdescent : baseEnd_4014487 < baseStart_4014487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014620 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4014620 : Nat := 118140960795 + 4014620 * 2 ^ 59
def prefixEnd_4014620 : Nat := 4983230072969 + 3 ^ 40 * 4014620 * 2
def baseEnd_4014620 : Nat := 1374286470102125342991403

theorem tailTrace_4014620 : CollatzResearch.WordTrace tailWord_4014620 prefixEnd_4014620 1374286470102125342991403 := by
  unfold tailWord_4014620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73212610357862428677160657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97616813810483238236214209 73212610357862428677160657)
  ·
    refine ⟨54909457768396821507870493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73212610357862428677160657 54909457768396821507870493)
    ·
      refine ⟨20591046663148808065451435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54909457768396821507870493 20591046663148808065451435)
      ·
        refine ⟨30886569994723212098177153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591046663148808065451435 30886569994723212098177153)
        ·
          refine ⟨23164927496042409073632865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30886569994723212098177153 23164927496042409073632865)
          ·
            refine ⟨17373695622031806805224649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23164927496042409073632865 17373695622031806805224649)
            ·
              refine ⟨13030271716523855103918487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17373695622031806805224649 13030271716523855103918487)
              ·
                refine ⟨19545407574785782655877731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030271716523855103918487 19545407574785782655877731)
                ·
                  refine ⟨29318111362178673983816597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19545407574785782655877731 29318111362178673983816597)
                  ·
                    refine ⟨1374286470102125342991403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29318111362178673983816597 1374286470102125342991403)
                    ·
                      rfl

theorem cell22_4014620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4014620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014620 prefixEnd_4014620 := by exact prefixLift 4014620
  have htrace : WordTrace (prefixWord ++ tailWord_4014620) baseStart_4014620 baseEnd_4014620 := by
    simpa [prefixWord, tailWord_4014620, baseEnd_4014620] using wordTrace_append hprefix tailTrace_4014620
  have hstable : (prefixWord ++ tailWord_4014620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014620).length < 2 ^ (prefixWord ++ tailWord_4014620).sum := by decide
  have hdescent : baseEnd_4014620 < baseStart_4014620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014660 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4014660 : Nat := 118140960795 + 4014660 * 2 ^ 59
def prefixEnd_4014660 : Nat := 4983230072969 + 3 ^ 40 * 4014660 * 2
def baseEnd_4014660 : Nat := 1374300162919578571991281

theorem tailTrace_4014660 : CollatzResearch.WordTrace tailWord_4014660 prefixEnd_4014660 1374300162919578571991281 := by
  unfold tailWord_4014660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73213339817789972092888717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97617786423719962790518289 73213339817789972092888717)
  ·
    refine ⟨27455002431671239534833269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73213339817789972092888717 27455002431671239534833269)
    ·
      refine ⟨2573906477969178706390619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27455002431671239534833269 2573906477969178706390619)
      ·
        refine ⟨3860859716953768059585929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573906477969178706390619 3860859716953768059585929)
        ·
          refine ⟨2895644787715326044689447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860859716953768059585929 2895644787715326044689447)
          ·
            refine ⟨4343467181572989067034171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895644787715326044689447 4343467181572989067034171)
            ·
              refine ⟨6515200772359483600551257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343467181572989067034171 6515200772359483600551257)
              ·
                refine ⟨4886400579269612700413443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515200772359483600551257 4886400579269612700413443)
                ·
                  refine ⟨7329600868904419050620165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886400579269612700413443 7329600868904419050620165)
                  ·
                    refine ⟨1374300162919578571991281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7329600868904419050620165 1374300162919578571991281)
                    ·
                      rfl

theorem cell22_4014660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4014660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014660 prefixEnd_4014660 := by exact prefixLift 4014660
  have htrace : WordTrace (prefixWord ++ tailWord_4014660) baseStart_4014660 baseEnd_4014660 := by
    simpa [prefixWord, tailWord_4014660, baseEnd_4014660] using wordTrace_append hprefix tailTrace_4014660
  have hstable : (prefixWord ++ tailWord_4014660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014660).length < 2 ^ (prefixWord ++ tailWord_4014660).sum := by decide
  have hdescent : baseEnd_4014660 < baseStart_4014660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014686 : List Nat := [4, 4, 1, 2, 2, 9]
def baseStart_4014686 : Nat := 118140960795 + 4014686 * 2 ^ 59
def prefixEnd_4014686 : Nat := 4983230072969 + 3 ^ 40 * 4014686 * 2
def baseEnd_4014686 : Nat := 16966778558653372479521

theorem tailTrace_4014686 : CollatzResearch.WordTrace tailWord_4014686 prefixEnd_4014686 16966778558653372479521 := by
  unfold tailWord_4014686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303453491685718828277989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97618418622323833750815941 18303453491685718828277989)
  ·
    refine ⟨3431897529691072280302123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18303453491685718828277989 3431897529691072280302123)
    ·
      refine ⟨5147846294536608420453185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431897529691072280302123 5147846294536608420453185)
      ·
        refine ⟨3860884720902456315339889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5147846294536608420453185 3860884720902456315339889)
        ·
          refine ⟨2895663540676842236504917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860884720902456315339889 2895663540676842236504917)
          ·
            refine ⟨16966778558653372479521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2895663540676842236504917 16966778558653372479521)
            ·
              rfl

theorem cell22_4014686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 9].length) (baseStart_4014686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014686 prefixEnd_4014686 := by exact prefixLift 4014686
  have htrace : WordTrace (prefixWord ++ tailWord_4014686) baseStart_4014686 baseEnd_4014686 := by
    simpa [prefixWord, tailWord_4014686, baseEnd_4014686] using wordTrace_append hprefix tailTrace_4014686
  have hstable : (prefixWord ++ tailWord_4014686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014686).length < 2 ^ (prefixWord ++ tailWord_4014686).sum := by decide
  have hdescent : baseEnd_4014686 < baseStart_4014686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014695 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4014695 : Nat := 118140960795 + 4014695 * 2 ^ 59
def prefixEnd_4014695 : Nat := 4983230072969 + 3 ^ 40 * 4014695 * 2
def baseEnd_4014695 : Nat := 1374312144134850147366173

theorem tailTrace_4014695 : CollatzResearch.WordTrace tailWord_4014695 prefixEnd_4014695 1374312144134850147366173 := by
  unfold tailWord_4014695
  simp only [CollatzResearch.WordTrace]
  refine ⟨146427956190453145163301539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97618637460302096775534359 146427956190453145163301539)
  ·
    refine ⟨219641934285679717744952309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146427956190453145163301539 219641934285679717744952309)
    ·
      refine ⟨20591431339282473538589279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219641934285679717744952309 20591431339282473538589279)
      ·
        refine ⟨30887147008923710307883919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591431339282473538589279 30887147008923710307883919)
        ·
          refine ⟨46330720513385565461825879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887147008923710307883919 46330720513385565461825879)
          ·
            refine ⟨69496080770078348192738819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46330720513385565461825879 69496080770078348192738819)
            ·
              refine ⟨104244121155117522289108229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69496080770078348192738819 104244121155117522289108229)
              ·
                refine ⟨19545772716584535429207793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104244121155117522289108229 19545772716584535429207793)
                ·
                  refine ⟨14659329537438401571905845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19545772716584535429207793 14659329537438401571905845)
                  ·
                    refine ⟨1374312144134850147366173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14659329537438401571905845 1374312144134850147366173)
                    ·
                      rfl

theorem cell22_4014695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4014695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014695 prefixEnd_4014695 := by exact prefixLift 4014695
  have htrace : WordTrace (prefixWord ++ tailWord_4014695) baseStart_4014695 baseEnd_4014695 := by
    simpa [prefixWord, tailWord_4014695, baseEnd_4014695] using wordTrace_append hprefix tailTrace_4014695
  have hstable : (prefixWord ++ tailWord_4014695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014695).length < 2 ^ (prefixWord ++ tailWord_4014695).sum := by decide
  have hdescent : baseEnd_4014695 < baseStart_4014695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014701 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_4014701 : Nat := 118140960795 + 4014701 * 2 ^ 59
def prefixEnd_4014701 : Nat := 4983230072969 + 3 ^ 40 * 4014701 * 2
def baseEnd_4014701 : Nat := 1374314198057468131716155

theorem tailTrace_4014701 : CollatzResearch.WordTrace tailWord_4014701 prefixEnd_4014701 1374314198057468131716155 := by
  unfold tailWord_4014701
  simp only [CollatzResearch.WordTrace]
  refine ⟨146428175028431408188019957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97618783352287605458679971 146428175028431408188019957)
  ·
    refine ⟨13727641408915444517626871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146428175028431408188019957 13727641408915444517626871)
    ·
      refine ⟨20591462113373166776440307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727641408915444517626871 20591462113373166776440307)
      ·
        refine ⟨30887193170059750164660461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591462113373166776440307 30887193170059750164660461)
        ·
          refine ⟨11582697438772406311747673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30887193170059750164660461 11582697438772406311747673)
          ·
            refine ⟨8687023079079304733810755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11582697438772406311747673 8687023079079304733810755)
            ·
              refine ⟨13030534618618957100716133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687023079079304733810755 13030534618618957100716133)
              ·
                refine ⟨2443225240991054456384275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13030534618618957100716133 2443225240991054456384275)
                ·
                  refine ⟨3664837861486581684576413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443225240991054456384275 3664837861486581684576413)
                  ·
                    refine ⟨1374314198057468131716155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664837861486581684576413 1374314198057468131716155)
                    ·
                      rfl

theorem cell22_4014701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_4014701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014701 prefixEnd_4014701 := by exact prefixLift 4014701
  have htrace : WordTrace (prefixWord ++ tailWord_4014701) baseStart_4014701 baseEnd_4014701 := by
    simpa [prefixWord, tailWord_4014701, baseEnd_4014701] using wordTrace_append hprefix tailTrace_4014701
  have hstable : (prefixWord ++ tailWord_4014701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014701).length < 2 ^ (prefixWord ++ tailWord_4014701).sum := by decide
  have hdescent : baseEnd_4014701 < baseStart_4014701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014725 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 8]
def baseStart_4014725 : Nat := 118140960795 + 4014725 * 2 ^ 59
def prefixEnd_4014725 : Nat := 4983230072969 + 3 ^ 40 * 4014725 * 2
def baseEnd_4014725 : Nat := 458107471249313356372027

theorem tailTrace_4014725 : CollatzResearch.WordTrace tailWord_4014725 prefixEnd_4014725 458107471249313356372027 := by
  unfold tailWord_4014725
  simp only [CollatzResearch.WordTrace]
  refine ⟨146429050380344460286893629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97619366920229640191262419 146429050380344460286893629)
  ·
    refine ⟨54910893892629172607585111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146429050380344460286893629 54910893892629172607585111)
    ·
      refine ⟨82366340838943758911377667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54910893892629172607585111 82366340838943758911377667)
      ·
        refine ⟨123549511258415638367066501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82366340838943758911377667 123549511258415638367066501)
        ·
          refine ⟨23165533360952932193824969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123549511258415638367066501 23165533360952932193824969)
          ·
            refine ⟨17374150020714699145368727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23165533360952932193824969 17374150020714699145368727)
            ·
              refine ⟨26061225031072048718053091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17374150020714699145368727 26061225031072048718053091)
              ·
                refine ⟨39091837546608073077079637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061225031072048718053091 39091837546608073077079637)
                ·
                  refine ⟨458107471249313356372027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39091837546608073077079637 458107471249313356372027)
                  ·
                    rfl

theorem cell22_4014725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_4014725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014725 prefixEnd_4014725 := by exact prefixLift 4014725
  have htrace : WordTrace (prefixWord ++ tailWord_4014725) baseStart_4014725 baseEnd_4014725 := by
    simpa [prefixWord, tailWord_4014725, baseEnd_4014725] using wordTrace_append hprefix tailTrace_4014725
  have hstable : (prefixWord ++ tailWord_4014725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014725).length < 2 ^ (prefixWord ++ tailWord_4014725).sum := by decide
  have hdescent : baseEnd_4014725 < baseStart_4014725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014727 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4014727 : Nat := 118140960795 + 4014727 * 2 ^ 59
def prefixEnd_4014727 : Nat := 4983230072969 + 3 ^ 40 * 4014727 * 2
def baseEnd_4014727 : Nat := 1374323098388812730566075

theorem tailTrace_4014727 : CollatzResearch.WordTrace tailWord_4014727 prefixEnd_4014727 1374323098388812730566075 := by
  unfold tailWord_4014727
  simp only [CollatzResearch.WordTrace]
  refine ⟨146429123326337214628466435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97619415550891476418977623 146429123326337214628466435)
  ·
    refine ⟨219643684989505821942699653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146429123326337214628466435 219643684989505821942699653)
    ·
      refine ⟨41183190935532341614256185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219643684989505821942699653 41183190935532341614256185)
      ·
        refine ⟨30887393201649256210692139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41183190935532341614256185 30887393201649256210692139)
        ·
          refine ⟨46331089802473884316038209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887393201649256210692139 46331089802473884316038209)
          ·
            refine ⟨34748317351855413237028657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46331089802473884316038209 34748317351855413237028657)
            ·
              refine ⟨26061238013891559927771493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34748317351855413237028657 26061238013891559927771493)
              ·
                refine ⟨4886482127604667486457155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26061238013891559927771493 4886482127604667486457155)
                ·
                  refine ⟨7329723191407001229685733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886482127604667486457155 7329723191407001229685733)
                  ·
                    refine ⟨1374323098388812730566075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7329723191407001229685733 1374323098388812730566075)
                    ·
                      rfl

theorem cell22_4014727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4014727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014727 prefixEnd_4014727 := by exact prefixLift 4014727
  have htrace : WordTrace (prefixWord ++ tailWord_4014727) baseStart_4014727 baseEnd_4014727 := by
    simpa [prefixWord, tailWord_4014727, baseEnd_4014727] using wordTrace_append hprefix tailTrace_4014727
  have hstable : (prefixWord ++ tailWord_4014727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014727).length < 2 ^ (prefixWord ++ tailWord_4014727).sum := by decide
  have hdescent : baseEnd_4014727 < baseStart_4014727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014770 : List Nat := [3, 2, 1, 1, 1, 2, 1, 11]
def baseStart_4014770 : Nat := 118140960795 + 4014770 * 2 ^ 59
def prefixEnd_4014770 : Nat := 4983230072969 + 3 ^ 40 * 4014770 * 2
def baseEnd_4014770 : Nat := 152704202018619439082327

theorem tailTrace_4014770 : CollatzResearch.WordTrace tailWord_4014770 prefixEnd_4014770 152704202018619439082327 := by
  unfold tailWord_4014770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607672916295358243070441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97620461110120955314854509 36607672916295358243070441)
  ·
    refine ⟨27455754687221518682302831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36607672916295358243070441 27455754687221518682302831)
    ·
      refine ⟨41183632030832278023454247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27455754687221518682302831 41183632030832278023454247)
      ·
        refine ⟨61775448046248417035181371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41183632030832278023454247 61775448046248417035181371)
        ·
          refine ⟨92663172069372625552772057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61775448046248417035181371 92663172069372625552772057)
          ·
            refine ⟨69497379052029469164579043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92663172069372625552772057 69497379052029469164579043)
            ·
              refine ⟨104246068578044203746868565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69497379052029469164579043 104246068578044203746868565)
              ·
                refine ⟨152704202018619439082327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 104246068578044203746868565 152704202018619439082327)
                ·
                  rfl

theorem cell22_4014770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_4014770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014770 prefixEnd_4014770 := by exact prefixLift 4014770
  have htrace : WordTrace (prefixWord ++ tailWord_4014770) baseStart_4014770 baseEnd_4014770 := by
    simpa [prefixWord, tailWord_4014770, baseEnd_4014770] using wordTrace_append hprefix tailTrace_4014770
  have hstable : (prefixWord ++ tailWord_4014770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014770).length < 2 ^ (prefixWord ++ tailWord_4014770).sum := by decide
  have hdescent : baseEnd_4014770 < baseStart_4014770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014804 : List Nat := [2, 4, 1, 3, 2, 2, 8]
def baseStart_4014804 : Nat := 118140960795 + 4014804 * 2 ^ 59
def prefixEnd_4014804 : Nat := 4983230072969 + 3 ^ 40 * 4014804 * 2
def baseEnd_4014804 : Nat := 50901831743052229495957

theorem tailTrace_4014804 : CollatzResearch.WordTrace tailWord_4014804 prefixEnd_4014804 50901831743052229495957 := by
  unfold tailWord_4014804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73215965873529128389509733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97621287831372171186012977 73215965873529128389509733)
  ·
    refine ⟨13727993601286711573033075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73215965873529128389509733 13727993601286711573033075)
    ·
      refine ⟨20591990401930067359549613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727993601286711573033075 20591990401930067359549613)
      ·
        refine ⟨7721996400723775259831105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20591990401930067359549613 7721996400723775259831105)
        ·
          refine ⟨5791497300542831444873329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7721996400723775259831105 5791497300542831444873329)
          ·
            refine ⟨4343622975407123583654997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5791497300542831444873329 4343622975407123583654997)
            ·
              refine ⟨50901831743052229495957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4343622975407123583654997 50901831743052229495957)
              ·
                rfl

theorem cell22_4014804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 8].length) (baseStart_4014804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014804 prefixEnd_4014804 := by exact prefixLift 4014804
  have htrace : WordTrace (prefixWord ++ tailWord_4014804) baseStart_4014804 baseEnd_4014804 := by
    simpa [prefixWord, tailWord_4014804, baseEnd_4014804] using wordTrace_append hprefix tailTrace_4014804
  have hstable : (prefixWord ++ tailWord_4014804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014804).length < 2 ^ (prefixWord ++ tailWord_4014804).sum := by decide
  have hdescent : baseEnd_4014804 < baseStart_4014804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014832 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_4014832 : Nat := 118140960795 + 4014832 * 2 ^ 59
def prefixEnd_4014832 : Nat := 4983230072969 + 3 ^ 40 * 4014832 * 2
def baseEnd_4014832 : Nat := 458119680678209152230251

theorem tailTrace_4014832 : CollatzResearch.WordTrace tailWord_4014832 prefixEnd_4014832 458119680678209152230251 := by
  unfold tailWord_4014832
  simp only [CollatzResearch.WordTrace]
  refine ⟨73216476495478408780519375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97621968660637878374025833 73216476495478408780519375)
  ·
    refine ⟨109824714743217613170779063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73216476495478408780519375 109824714743217613170779063)
    ·
      refine ⟨164737072114826419756168595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109824714743217613170779063 164737072114826419756168595)
      ·
        refine ⟨247105608172239629634252893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164737072114826419756168595 247105608172239629634252893)
        ·
          refine ⟨92664603064589861112844835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247105608172239629634252893 92664603064589861112844835)
          ·
            refine ⟨138996904596884791669267253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92664603064589861112844835 138996904596884791669267253)
            ·
              refine ⟨13030959805957949218993805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138996904596884791669267253 13030959805957949218993805)
              ·
                refine ⟨4886609927234230957122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13030959805957949218993805 4886609927234230957122677)
                ·
                  refine ⟨458119680678209152230251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4886609927234230957122677 458119680678209152230251)
                  ·
                    rfl

theorem cell22_4014832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_4014832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014832 prefixEnd_4014832 := by exact prefixLift 4014832
  have htrace : WordTrace (prefixWord ++ tailWord_4014832) baseStart_4014832 baseEnd_4014832 := by
    simpa [prefixWord, tailWord_4014832, baseEnd_4014832] using wordTrace_append hprefix tailTrace_4014832
  have hstable : (prefixWord ++ tailWord_4014832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014832).length < 2 ^ (prefixWord ++ tailWord_4014832).sum := by decide
  have hdescent : baseEnd_4014832 < baseStart_4014832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014894 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_4014894 : Nat := 118140960795 + 4014894 * 2 ^ 59
def prefixEnd_4014894 : Nat := 4983230072969 + 3 ^ 40 * 4014894 * 2
def baseEnd_4014894 : Nat := 458126755300559987213521

theorem tailTrace_4014894 : CollatzResearch.WordTrace tailWord_4014894 prefixEnd_4014894 458126755300559987213521 := by
  unfold tailWord_4014894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304401789591525268724467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97623476211154801433197157 18304401789591525268724467)
  ·
    refine ⟨27456602684387287903086701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18304401789591525268724467 27456602684387287903086701)
    ·
      refine ⟨10296226006645232963657513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27456602684387287903086701 10296226006645232963657513)
      ·
        refine ⟨7722169504983924722743135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10296226006645232963657513 7722169504983924722743135)
        ·
          refine ⟨11583254257475887084114703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722169504983924722743135 11583254257475887084114703)
          ·
            refine ⟨17374881386213830626172055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583254257475887084114703 17374881386213830626172055)
            ·
              refine ⟨26062322079320745939258083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17374881386213830626172055 26062322079320745939258083)
              ·
                refine ⟨39093483118981118908887125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26062322079320745939258083 39093483118981118908887125)
                ·
                  refine ⟨458126755300559987213521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39093483118981118908887125 458126755300559987213521)
                  ·
                    rfl

theorem cell22_4014894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_4014894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014894 prefixEnd_4014894 := by exact prefixLift 4014894
  have htrace : WordTrace (prefixWord ++ tailWord_4014894) baseStart_4014894 baseEnd_4014894 := by
    simpa [prefixWord, tailWord_4014894, baseEnd_4014894] using wordTrace_append hprefix tailTrace_4014894
  have hstable : (prefixWord ++ tailWord_4014894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014894).length < 2 ^ (prefixWord ++ tailWord_4014894).sum := by decide
  have hdescent : baseEnd_4014894 < baseStart_4014894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014911 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 4]
def baseStart_4014911 : Nat := 118140960795 + 4014911 * 2 ^ 59
def prefixEnd_4014911 : Nat := 4983230072969 + 3 ^ 40 * 4014911 * 2
def baseEnd_4014911 : Nat := 458128695116365861321837

theorem tailTrace_4014911 : CollatzResearch.WordTrace tailWord_4014911 prefixEnd_4014911 458128695116365861321837 := by
  unfold tailWord_4014911
  simp only [CollatzResearch.WordTrace]
  refine ⟨146435834357670614053164587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97623889571780409368776391 146435834357670614053164587)
  ·
    refine ⟨219653751536505921079746881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146435834357670614053164587 219653751536505921079746881)
    ·
      refine ⟨164740313652379440809810161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219653751536505921079746881 164740313652379440809810161)
      ·
        refine ⟨123555235239284580607357621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164740313652379440809810161 123555235239284580607357621)
        ·
          refine ⟨11583303303682929431939777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123555235239284580607357621 11583303303682929431939777)
          ·
            refine ⟨8687477477762197073954833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11583303303682929431939777 8687477477762197073954833)
            ·
              refine ⟨6515608108321647805466125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8687477477762197073954833 6515608108321647805466125)
              ·
                refine ⟨2443353040620617927049797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6515608108321647805466125 2443353040620617927049797)
                ·
                  refine ⟨458128695116365861321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443353040620617927049797 458128695116365861321837)
                  ·
                    rfl

theorem cell22_4014911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 4].length) (baseStart_4014911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014911 prefixEnd_4014911 := by exact prefixLift 4014911
  have htrace : WordTrace (prefixWord ++ tailWord_4014911) baseStart_4014911 baseEnd_4014911 := by
    simpa [prefixWord, tailWord_4014911, baseEnd_4014911] using wordTrace_append hprefix tailTrace_4014911
  have hstable : (prefixWord ++ tailWord_4014911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014911).length < 2 ^ (prefixWord ++ tailWord_4014911).sum := by decide
  have hdescent : baseEnd_4014911 < baseStart_4014911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014913 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_4014913 : Nat := 118140960795 + 4014913 * 2 ^ 59
def prefixEnd_4014913 : Nat := 4983230072969 + 3 ^ 40 * 4014913 * 2
def baseEnd_4014913 : Nat := 1374386769989970245415505

theorem tailTrace_4014913 : CollatzResearch.WordTrace tailWord_4014913 prefixEnd_4014913 1374386769989970245415505 := by
  unfold tailWord_4014913
  simp only [CollatzResearch.WordTrace]
  refine ⟨146435907303663368394737393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97623938202442245596491595 146435907303663368394737393)
  ·
    refine ⟨109826930477747526296053045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146435907303663368394737393 109826930477747526296053045)
    ·
      refine ⟨10296274732288830590254973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109826930477747526296053045 10296274732288830590254973)
      ·
        refine ⟨3861103024608311471345615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10296274732288830590254973 3861103024608311471345615)
        ·
          refine ⟨5791654536912467207018423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861103024608311471345615 5791654536912467207018423)
          ·
            refine ⟨8687481805368700810527635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791654536912467207018423 8687481805368700810527635)
            ·
              refine ⟨13031222708053051215791453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687481805368700810527635 13031222708053051215791453)
              ·
                refine ⟨4886708515519894205921795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13031222708053051215791453 4886708515519894205921795)
                ·
                  refine ⟨7330062773279841308882693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886708515519894205921795 7330062773279841308882693)
                  ·
                    refine ⟨1374386769989970245415505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330062773279841308882693 1374386769989970245415505)
                    ·
                      rfl

theorem cell22_4014913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_4014913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014913 prefixEnd_4014913 := by exact prefixLift 4014913
  have htrace : WordTrace (prefixWord ++ tailWord_4014913) baseStart_4014913 baseEnd_4014913 := by
    simpa [prefixWord, tailWord_4014913, baseEnd_4014913] using wordTrace_append hprefix tailTrace_4014913
  have hstable : (prefixWord ++ tailWord_4014913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014913).length < 2 ^ (prefixWord ++ tailWord_4014913).sum := by decide
  have hdescent : baseEnd_4014913 < baseStart_4014913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014984 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_4014984 : Nat := 118140960795 + 4014984 * 2 ^ 59
def prefixEnd_4014984 : Nat := 4983230072969 + 3 ^ 40 * 4014984 * 2
def baseEnd_4014984 : Nat := 458137024913649908963429

theorem tailTrace_4014984 : CollatzResearch.WordTrace tailWord_4014984 prefixEnd_4014984 458137024913649908963429 := by
  unfold tailWord_4014984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73219248443203073760286003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97625664590937431680381337 73219248443203073760286003)
  ·
    refine ⟨109828872664804610640429005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73219248443203073760286003 109828872664804610640429005)
    ·
      refine ⟨41185827249301728990160877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109828872664804610640429005 41185827249301728990160877)
      ·
        refine ⟨15444685218488148371310329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41185827249301728990160877 15444685218488148371310329)
        ·
          refine ⟨11583513913866111278482747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15444685218488148371310329 11583513913866111278482747)
          ·
            refine ⟨17375270870799166917724121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583513913866111278482747 17375270870799166917724121)
            ·
              refine ⟨13031453153099375188293091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17375270870799166917724121 13031453153099375188293091)
              ·
                refine ⟨19547179729649062782439637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13031453153099375188293091 19547179729649062782439637)
                ·
                  refine ⟨458137024913649908963429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19547179729649062782439637 458137024913649908963429)
                  ·
                    rfl

theorem cell22_4014984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_4014984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4014984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4014984 prefixEnd_4014984 := by exact prefixLift 4014984
  have htrace : WordTrace (prefixWord ++ tailWord_4014984) baseStart_4014984 baseEnd_4014984 := by
    simpa [prefixWord, tailWord_4014984, baseEnd_4014984] using wordTrace_append hprefix tailTrace_4014984
  have hstable : (prefixWord ++ tailWord_4014984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014984).length < 2 ^ (prefixWord ++ tailWord_4014984).sum := by decide
  have hdescent : baseEnd_4014984 < baseStart_4014984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015209 : List Nat := [1, 2, 1, 1, 1, 16]
def baseStart_4015209 : Nat := 118140960795 + 4015209 * 2 ^ 59
def prefixEnd_4015209 : Nat := 4983230072969 + 3 ^ 40 * 4015209 * 2
def baseEnd_4015209 : Nat := 16968988849865730123637

theorem tailTrace_4015209 : CollatzResearch.WordTrace tailWord_4015209 prefixEnd_4015209 16968988849865730123637 := by
  unfold tailWord_4015209
  simp only [CollatzResearch.WordTrace]
  refine ⟨146446703310591010947512681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97631135540394007298341787 146446703310591010947512681)
  ·
    refine ⟨109835027482943258210634511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146446703310591010947512681 109835027482943258210634511)
    ·
      refine ⟨164752541224414887315951767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109835027482943258210634511 164752541224414887315951767)
      ·
        refine ⟨247128811836622330973927651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164752541224414887315951767 247128811836622330973927651)
        ·
          refine ⟨370693217754933496460891477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247128811836622330973927651 370693217754933496460891477)
          ·
            refine ⟨16968988849865730123637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 370693217754933496460891477 16968988849865730123637)
            ·
              rfl

theorem cell22_4015209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 16].length) (baseStart_4015209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015209 prefixEnd_4015209 := by exact prefixLift 4015209
  have htrace : WordTrace (prefixWord ++ tailWord_4015209) baseStart_4015209 baseEnd_4015209 := by
    simpa [prefixWord, tailWord_4015209, baseEnd_4015209] using wordTrace_append hprefix tailTrace_4015209
  have hstable : (prefixWord ++ tailWord_4015209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015209).length < 2 ^ (prefixWord ++ tailWord_4015209).sum := by decide
  have hdescent : baseEnd_4015209 < baseStart_4015209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015363 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_4015363 : Nat := 118140960795 + 4015363 * 2 ^ 59
def prefixEnd_4015363 : Nat := 4983230072969 + 3 ^ 40 * 4015363 * 2
def baseEnd_4015363 : Nat := 1374540814186319071664125

theorem tailTrace_4015363 : CollatzResearch.WordTrace tailWord_4015363 prefixEnd_4015363 1374540814186319071664125 := by
  unfold tailWord_4015363
  simp only [CollatzResearch.WordTrace]
  refine ⟨146452320152033095248618743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97634880101355396832412495 146452320152033095248618743)
  ·
    refine ⟨219678480228049642872928115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146452320152033095248618743 219678480228049642872928115)
    ·
      refine ⟨329517720342074464309392173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219678480228049642872928115 329517720342074464309392173)
      ·
        refine ⟨123569145128277924116022065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329517720342074464309392173 123569145128277924116022065)
        ·
          refine ⟨92676858846208443087016549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123569145128277924116022065 92676858846208443087016549)
          ·
            refine ⟨17376911033664083078815603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92676858846208443087016549 17376911033664083078815603)
            ·
              refine ⟨26065366550496124618223405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17376911033664083078815603 26065366550496124618223405)
              ·
                refine ⟨9774512456436046731833777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26065366550496124618223405 9774512456436046731833777)
                ·
                  refine ⟨7330884342327035048875333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9774512456436046731833777 7330884342327035048875333)
                  ·
                    refine ⟨1374540814186319071664125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330884342327035048875333 1374540814186319071664125)
                    ·
                      rfl

theorem cell22_4015363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_4015363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015363 prefixEnd_4015363 := by exact prefixLift 4015363
  have htrace : WordTrace (prefixWord ++ tailWord_4015363) baseStart_4015363 baseEnd_4015363 := by
    simpa [prefixWord, tailWord_4015363, baseEnd_4015363] using wordTrace_append hprefix tailTrace_4015363
  have hstable : (prefixWord ++ tailWord_4015363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015363).length < 2 ^ (prefixWord ++ tailWord_4015363).sum := by decide
  have hdescent : baseEnd_4015363 < baseStart_4015363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015376 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_4015376 : Nat := 118140960795 + 4015376 * 2 ^ 59
def prefixEnd_4015376 : Nat := 4983230072969 + 3 ^ 40 * 4015376 * 2
def baseEnd_4015376 : Nat := 1374545264351991371089085

theorem tailTrace_4015376 : CollatzResearch.WordTrace tailWord_4015376 prefixEnd_4015376 1374545264351991371089085 := by
  unfold tailWord_4015376
  simp only [CollatzResearch.WordTrace]
  refine ⟨73226397150492999234420991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97635196200657332312561321 73226397150492999234420991)
  ·
    refine ⟨109839595725739498851631487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73226397150492999234420991 109839595725739498851631487)
    ·
      refine ⟨164759393588609248277447231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109839595725739498851631487 164759393588609248277447231)
      ·
        refine ⟨247139090382913872416170847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164759393588609248277447231 247139090382913872416170847)
        ·
          refine ⟨370708635574370808624256271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247139090382913872416170847 370708635574370808624256271)
          ·
            refine ⟨556062953361556212936384407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370708635574370808624256271 556062953361556212936384407)
            ·
              refine ⟨834094430042334319404576611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556062953361556212936384407 834094430042334319404576611)
              ·
                refine ⟨1251141645063501479106864917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834094430042334319404576611 1251141645063501479106864917)
                ·
                  refine ⟨58647264612351631833134293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1251141645063501479106864917 58647264612351631833134293)
                  ·
                    refine ⟨1374545264351991371089085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58647264612351631833134293 1374545264351991371089085)
                    ·
                      rfl

theorem cell22_4015376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_4015376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015376 prefixEnd_4015376 := by exact prefixLift 4015376
  have htrace : WordTrace (prefixWord ++ tailWord_4015376) baseStart_4015376 baseEnd_4015376 := by
    simpa [prefixWord, tailWord_4015376, baseEnd_4015376] using wordTrace_append hprefix tailTrace_4015376
  have hstable : (prefixWord ++ tailWord_4015376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015376).length < 2 ^ (prefixWord ++ tailWord_4015376).sum := by decide
  have hdescent : baseEnd_4015376 < baseStart_4015376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015410 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_4015410 : Nat := 118140960795 + 4015410 * 2 ^ 59
def prefixEnd_4015410 : Nat := 4983230072969 + 3 ^ 40 * 4015410 * 2
def baseEnd_4015410 : Nat := 1374556903246826615738981

theorem tailTrace_4015410 : CollatzResearch.WordTrace tailWord_4015410 prefixEnd_4015410 1374556903246826615738981 := by
  unfold tailWord_4015410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36613508595715705568894921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97636022921908548183719789 36613508595715705568894921)
  ·
    refine ⟨27460131446786779176671191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36613508595715705568894921 27460131446786779176671191)
    ·
      refine ⟨41190197170180168765006787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27460131446786779176671191 41190197170180168765006787)
      ·
        refine ⟨61785295755270253147510181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41190197170180168765006787 61785295755270253147510181)
        ·
          refine ⟨11584742954113172465158159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61785295755270253147510181 11584742954113172465158159)
          ·
            refine ⟨17377114431169758697737239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584742954113172465158159 17377114431169758697737239)
            ·
              refine ⟨26065671646754638046605859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377114431169758697737239 26065671646754638046605859)
              ·
                refine ⟨39098507470131957069908789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26065671646754638046605859 39098507470131957069908789)
                ·
                  refine ⟨3665485075324870975303949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39098507470131957069908789 3665485075324870975303949)
                  ·
                    refine ⟨1374556903246826615738981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3665485075324870975303949 1374556903246826615738981)
                    ·
                      rfl

theorem cell22_4015410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_4015410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015410 prefixEnd_4015410 := by exact prefixLift 4015410
  have htrace : WordTrace (prefixWord ++ tailWord_4015410) baseStart_4015410 baseEnd_4015410 := by
    simpa [prefixWord, tailWord_4015410, baseEnd_4015410] using wordTrace_append hprefix tailTrace_4015410
  have hstable : (prefixWord ++ tailWord_4015410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015410).length < 2 ^ (prefixWord ++ tailWord_4015410).sum := by decide
  have hdescent : baseEnd_4015410 < baseStart_4015410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015438 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_4015438 : Nat := 118140960795 + 4015438 * 2 ^ 59
def prefixEnd_4015438 : Nat := 4983230072969 + 3 ^ 40 * 4015438 * 2
def baseEnd_4015438 : Nat := 1374566488219043876038895

theorem tailTrace_4015438 : CollatzResearch.WordTrace tailWord_4015438 prefixEnd_4015438 1374566488219043876038895 := by
  unfold tailWord_4015438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306881953345172882199871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97636703751174255371732645 18306881953345172882199871)
  ·
    refine ⟨27460322930017759323299807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18306881953345172882199871 27460322930017759323299807)
    ·
      refine ⟨41190484395026638984949711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27460322930017759323299807 41190484395026638984949711)
      ·
        refine ⟨61785726592539958477424567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41190484395026638984949711 61785726592539958477424567)
        ·
          refine ⟨92678589888809937716136851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61785726592539958477424567 92678589888809937716136851)
          ·
            refine ⟨139017884833214906574205277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92678589888809937716136851 139017884833214906574205277)
            ·
              refine ⟨52131706812455589965326979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139017884833214906574205277 52131706812455589965326979)
              ·
                refine ⟨78197560218683384947990469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52131706812455589965326979 78197560218683384947990469)
                ·
                  refine ⟨14662042541003134677748213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78197560218683384947990469 14662042541003134677748213)
                  ·
                    refine ⟨1374566488219043876038895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14662042541003134677748213 1374566488219043876038895)
                    ·
                      rfl

theorem cell22_4015438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_4015438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015438 prefixEnd_4015438 := by exact prefixLift 4015438
  have htrace : WordTrace (prefixWord ++ tailWord_4015438) baseStart_4015438 baseEnd_4015438 := by
    simpa [prefixWord, tailWord_4015438, baseEnd_4015438] using wordTrace_append hprefix tailTrace_4015438
  have hstable : (prefixWord ++ tailWord_4015438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015438).length < 2 ^ (prefixWord ++ tailWord_4015438).sum := by decide
  have hdescent : baseEnd_4015438 < baseStart_4015438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015483 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_4015483 : Nat := 118140960795 + 4015483 * 2 ^ 59
def prefixEnd_4015483 : Nat := 4983230072969 + 3 ^ 40 * 4015483 * 2
def baseEnd_4015483 : Nat := 1374581892638678758663757

theorem tailTrace_4015483 : CollatzResearch.WordTrace tailWord_4015483 prefixEnd_4015483 1374581892638678758663757 := by
  unfold tailWord_4015483
  simp only [CollatzResearch.WordTrace]
  refine ⟨146456696911598355742987103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97637797941065570495324735 146456696911598355742987103)
  ·
    refine ⟨219685045367397533614480655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146456696911598355742987103 219685045367397533614480655)
    ·
      refine ⟨329527568051096300421720983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219685045367397533614480655 329527568051096300421720983)
      ·
        refine ⟨494291352076644450632581475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329527568051096300421720983 494291352076644450632581475)
        ·
          refine ⟨741437028114966675948872213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494291352076644450632581475 741437028114966675948872213)
          ·
            refine ⟨34754860692889062935103385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 741437028114966675948872213 34754860692889062935103385)
            ·
              refine ⟨26066145519666797201327539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34754860692889062935103385 26066145519666797201327539)
              ·
                refine ⟨39099218279500195801991309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26066145519666797201327539 39099218279500195801991309)
                ·
                  refine ⟨14662206854812573425746741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39099218279500195801991309 14662206854812573425746741)
                  ·
                    refine ⟨1374581892638678758663757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14662206854812573425746741 1374581892638678758663757)
                    ·
                      rfl

theorem cell22_4015483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_4015483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015483 prefixEnd_4015483 := by exact prefixLift 4015483
  have htrace : WordTrace (prefixWord ++ tailWord_4015483) baseStart_4015483 baseEnd_4015483 := by
    simpa [prefixWord, tailWord_4015483, baseEnd_4015483] using wordTrace_append hprefix tailTrace_4015483
  have hstable : (prefixWord ++ tailWord_4015483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015483).length < 2 ^ (prefixWord ++ tailWord_4015483).sum := by decide
  have hdescent : baseEnd_4015483 < baseStart_4015483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015500 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_4015500 : Nat := 118140960795 + 4015500 * 2 ^ 59
def prefixEnd_4015500 : Nat := 4983230072969 + 3 ^ 40 * 4015500 * 2
def baseEnd_4015500 : Nat := 1374587712086096380988705

theorem tailTrace_4015500 : CollatzResearch.WordTrace tailWord_4015500 prefixEnd_4015500 1374587712086096380988705 := by
  unfold tailWord_4015500
  simp only [CollatzResearch.WordTrace]
  refine ⟨73228658476268383823177977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97638211301691178430903969 73228658476268383823177977)
  ·
    refine ⟨54921493857201287867383483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73228658476268383823177977 54921493857201287867383483)
    ·
      refine ⟨82382240785801931801075225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54921493857201287867383483 82382240785801931801075225)
      ·
        refine ⟨61786680589351448850806419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82382240785801931801075225 61786680589351448850806419)
        ·
          refine ⟨92680020884027173276209629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61786680589351448850806419 92680020884027173276209629)
          ·
            refine ⟨34755007831510189978578611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92680020884027173276209629 34755007831510189978578611)
            ·
              refine ⟨52132511747265284967867917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34755007831510189978578611 52132511747265284967867917)
              ·
                refine ⟨19549691905224481862950469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52132511747265284967867917 19549691905224481862950469)
                ·
                  refine ⟨3665567232229590349303213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19549691905224481862950469 3665567232229590349303213)
                  ·
                    refine ⟨1374587712086096380988705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3665567232229590349303213 1374587712086096380988705)
                    ·
                      rfl

theorem cell22_4015500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_4015500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015500 prefixEnd_4015500 := by exact prefixLift 4015500
  have htrace : WordTrace (prefixWord ++ tailWord_4015500) baseStart_4015500 baseEnd_4015500 := by
    simpa [prefixWord, tailWord_4015500, baseEnd_4015500] using wordTrace_append hprefix tailTrace_4015500
  have hstable : (prefixWord ++ tailWord_4015500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015500).length < 2 ^ (prefixWord ++ tailWord_4015500).sum := by decide
  have hdescent : baseEnd_4015500 < baseStart_4015500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015513 : List Nat := [1, 2, 1, 2, 1, 5, 1, 9]
def baseStart_4015513 : Nat := 118140960795 + 4015513 * 2 ^ 59
def prefixEnd_4015513 : Nat := 4983230072969 + 3 ^ 40 * 4015513 * 2
def baseEnd_4015513 : Nat := 152732462472418742268185

theorem tailTrace_4015513 : CollatzResearch.WordTrace tailWord_4015513 prefixEnd_4015513 152732462472418742268185 := by
  unfold tailWord_4015513
  simp only [CollatzResearch.WordTrace]
  refine ⟨146457791101489670866579193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97638527400993113911052795 146457791101489670866579193)
  ·
    refine ⟨109843343326117253149934395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146457791101489670866579193 109843343326117253149934395)
    ·
      refine ⟨164765014989175879724901593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109843343326117253149934395 164765014989175879724901593)
      ·
        refine ⟨123573761241881909793676195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164765014989175879724901593 123573761241881909793676195)
        ·
          refine ⟨185360641862822864690514293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123573761241881909793676195 185360641862822864690514293)
          ·
            refine ⟨17377560174639643564735715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185360641862822864690514293 17377560174639643564735715)
            ·
              refine ⟨26066340261959465347103573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377560174639643564735715 26066340261959465347103573)
              ·
                refine ⟨152732462472418742268185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26066340261959465347103573 152732462472418742268185)
                ·
                  rfl

theorem cell22_4015513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 9].length) (baseStart_4015513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015513 prefixEnd_4015513 := by exact prefixLift 4015513
  have htrace : WordTrace (prefixWord ++ tailWord_4015513) baseStart_4015513 baseEnd_4015513 := by
    simpa [prefixWord, tailWord_4015513, baseEnd_4015513] using wordTrace_append hprefix tailTrace_4015513
  have hstable : (prefixWord ++ tailWord_4015513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015513).length < 2 ^ (prefixWord ++ tailWord_4015513).sum := by decide
  have hdescent : baseEnd_4015513 < baseStart_4015513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015667 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_4015667 : Nat := 118140960795 + 4015667 * 2 ^ 59
def prefixEnd_4015667 : Nat := 4983230072969 + 3 ^ 40 * 4015667 * 2
def baseEnd_4015667 : Nat := 1374644879598963612063193

theorem tailTrace_4015667 : CollatzResearch.WordTrace tailWord_4015667 prefixEnd_4015667 1374644879598963612063193 := by
  unfold tailWord_4015667
  simp only [CollatzResearch.WordTrace]
  refine ⟨146463407942931755167685255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97642271961954503445123503 146463407942931755167685255)
  ·
    refine ⟨219695111914397632751527883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146463407942931755167685255 219695111914397632751527883)
    ·
      refine ⟨329542667871596449127291825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219695111914397632751527883 329542667871596449127291825)
      ·
        refine ⟨247157000903697336845468869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329542667871596449127291825 247157000903697336845468869)
        ·
          refine ⟨46341937669443250658525413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247157000903697336845468869 46341937669443250658525413)
          ·
            refine ⟨8689113313020609498473515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46341937669443250658525413 8689113313020609498473515)
            ·
              refine ⟨13033669969530914247710273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689113313020609498473515 13033669969530914247710273)
              ·
                refine ⟨9775252477148185685782705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13033669969530914247710273 9775252477148185685782705)
                ·
                  refine ⟨7331439357861139264337029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775252477148185685782705 7331439357861139264337029)
                  ·
                    refine ⟨1374644879598963612063193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7331439357861139264337029 1374644879598963612063193)
                    ·
                      rfl

theorem cell22_4015667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_4015667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015667 prefixEnd_4015667 := by exact prefixLift 4015667
  have htrace : WordTrace (prefixWord ++ tailWord_4015667) baseStart_4015667 baseEnd_4015667 := by
    simpa [prefixWord, tailWord_4015667, baseEnd_4015667] using wordTrace_append hprefix tailTrace_4015667
  have hstable : (prefixWord ++ tailWord_4015667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015667).length < 2 ^ (prefixWord ++ tailWord_4015667).sum := by decide
  have hdescent : baseEnd_4015667 < baseStart_4015667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015697 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_4015697 : Nat := 118140960795 + 4015697 * 2 ^ 59
def prefixEnd_4015697 : Nat := 4983230072969 + 3 ^ 40 * 4015697 * 2
def baseEnd_4015697 : Nat := 1374655149212053533813101

theorem tailTrace_4015697 : CollatzResearch.WordTrace tailWord_4015697 prefixEnd_4015697 1374655149212053533813101 := by
  unfold tailWord_4015697
  simp only [CollatzResearch.WordTrace]
  refine ⟨146464502132823070291277345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97643001421882046860851563 146464502132823070291277345)
  ·
    refine ⟨109848376599617302718458009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146464502132823070291277345 109848376599617302718458009)
    ·
      refine ⟨82386282449712977038843507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109848376599617302718458009 82386282449712977038843507)
      ·
        refine ⟨123579423674569465558265261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82386282449712977038843507 123579423674569465558265261)
        ·
          refine ⟨46342283877963549584349473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123579423674569465558265261 46342283877963549584349473)
          ·
            refine ⟨34756712908472662188262105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46342283877963549584349473 34756712908472662188262105)
            ·
              refine ⟨26067534681354496641196579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34756712908472662188262105 26067534681354496641196579)
              ·
                refine ⟨39101302022031744961794869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26067534681354496641196579 39101302022031744961794869)
                ·
                  refine ⟨3665747064565476090168269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39101302022031744961794869 3665747064565476090168269)
                  ·
                    refine ⟨1374655149212053533813101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3665747064565476090168269 1374655149212053533813101)
                    ·
                      rfl

theorem cell22_4015697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_4015697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015697 prefixEnd_4015697 := by exact prefixLift 4015697
  have htrace : WordTrace (prefixWord ++ tailWord_4015697) baseStart_4015697 baseEnd_4015697 := by
    simpa [prefixWord, tailWord_4015697, baseEnd_4015697] using wordTrace_append hprefix tailTrace_4015697
  have hstable : (prefixWord ++ tailWord_4015697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015697).length < 2 ^ (prefixWord ++ tailWord_4015697).sum := by decide
  have hdescent : baseEnd_4015697 < baseStart_4015697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015778 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_4015778 : Nat := 118140960795 + 4015778 * 2 ^ 59
def prefixEnd_4015778 : Nat := 4983230072969 + 3 ^ 40 * 4015778 * 2
def baseEnd_4015778 : Nat := 458227625722465440845951

theorem tailTrace_4015778 : CollatzResearch.WordTrace tailWord_4015778 prefixEnd_4015778 458227625722465440845951 := by
  unfold tailWord_4015778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36616864111382405281243997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97644970963686414083317325 36616864111382405281243997)
  ·
    refine ⟨13731324041768401980466499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36616864111382405281243997 13731324041768401980466499)
    ·
      refine ⟨20596986062652602970699749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13731324041768401980466499 20596986062652602970699749)
      ·
        refine ⟨3861934886747363057006203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20596986062652602970699749 3861934886747363057006203)
        ·
          refine ⟨5792902330121044585509305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861934886747363057006203 5792902330121044585509305)
          ·
            refine ⟨4344676747590783439131979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792902330121044585509305 4344676747590783439131979)
            ·
              refine ⟨6517015121386175158697969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344676747590783439131979 6517015121386175158697969)
              ·
                refine ⟨4887761341039631369023477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517015121386175158697969 4887761341039631369023477)
                ·
                  refine ⟨458227625722465440845951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4887761341039631369023477 458227625722465440845951)
                  ·
                    rfl

theorem cell22_4015778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_4015778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015778 prefixEnd_4015778 := by exact prefixLift 4015778
  have htrace : WordTrace (prefixWord ++ tailWord_4015778) baseStart_4015778 baseEnd_4015778 := by
    simpa [prefixWord, tailWord_4015778, baseEnd_4015778] using wordTrace_append hprefix tailTrace_4015778
  have hstable : (prefixWord ++ tailWord_4015778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015778).length < 2 ^ (prefixWord ++ tailWord_4015778).sum := by decide
  have hdescent : baseEnd_4015778 < baseStart_4015778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015789 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 6]
def baseStart_4015789 : Nat := 118140960795 + 4015789 * 2 ^ 59
def prefixEnd_4015789 : Nat := 4983230072969 + 3 ^ 40 * 4015789 * 2
def baseEnd_4015789 : Nat := 458228880897398653504273

theorem tailTrace_4015789 : CollatzResearch.WordTrace tailWord_4015789 prefixEnd_4015789 458228880897398653504273 := by
  unfold tailWord_4015789
  simp only [CollatzResearch.WordTrace]
  refine ⟨146467857648489770003626421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97645238432326513335750947 146467857648489770003626421)
  ·
    refine ⟨13731361654545915937839977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146467857648489770003626421 13731361654545915937839977)
    ·
      refine ⟨10298521240909436953379983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13731361654545915937839977 10298521240909436953379983)
      ·
        refine ⟨15447781861364155430069975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298521240909436953379983 15447781861364155430069975)
        ·
          refine ⟨23171672792046233145104963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447781861364155430069975 23171672792046233145104963)
          ·
            refine ⟨34757509188069349717657445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23171672792046233145104963 34757509188069349717657445)
            ·
              refine ⟨6517032972763003072060771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34757509188069349717657445 6517032972763003072060771)
              ·
                refine ⟨9775549459144504608091157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517032972763003072060771 9775549459144504608091157)
                ·
                  refine ⟨458228880897398653504273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9775549459144504608091157 458228880897398653504273)
                  ·
                    rfl

theorem cell22_4015789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_4015789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015789 prefixEnd_4015789 := by exact prefixLift 4015789
  have htrace : WordTrace (prefixWord ++ tailWord_4015789) baseStart_4015789 baseEnd_4015789 := by
    simpa [prefixWord, tailWord_4015789, baseEnd_4015789] using wordTrace_append hprefix tailTrace_4015789
  have hstable : (prefixWord ++ tailWord_4015789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015789).length < 2 ^ (prefixWord ++ tailWord_4015789).sum := by decide
  have hdescent : baseEnd_4015789 < baseStart_4015789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015802 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_4015802 : Nat := 118140960795 + 4015802 * 2 ^ 59
def prefixEnd_4015802 : Nat := 4983230072969 + 3 ^ 40 * 4015802 * 2
def baseEnd_4015802 : Nat := 1374691092857868259937779

theorem tailTrace_4015802 : CollatzResearch.WordTrace tailWord_4015802 prefixEnd_4015802 1374691092857868259937779 := by
  unfold tailWord_4015802
  simp only [CollatzResearch.WordTrace]
  refine ⟨36617082949360668305962415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97645554531628448815899773 36617082949360668305962415)
  ·
    refine ⟨54925624424041002458943623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36617082949360668305962415 54925624424041002458943623)
    ·
      refine ⟨82388436636061503688415435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54925624424041002458943623 82388436636061503688415435)
      ·
        refine ⟨123582654954092255532623153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82388436636061503688415435 123582654954092255532623153)
        ·
          refine ⟨92686991215569191649467365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123582654954092255532623153 92686991215569191649467365)
          ·
            refine ⟨17378810852919223434275131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92686991215569191649467365 17378810852919223434275131)
            ·
              refine ⟨26068216279378835151412697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17378810852919223434275131 26068216279378835151412697)
              ·
                refine ⟨19551162209534126363559523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26068216279378835151412697 19551162209534126363559523)
                ·
                  refine ⟨29326743314301189545339285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19551162209534126363559523 29326743314301189545339285)
                  ·
                    refine ⟨1374691092857868259937779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29326743314301189545339285 1374691092857868259937779)
                    ·
                      rfl

theorem cell22_4015802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_4015802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015802 prefixEnd_4015802 := by exact prefixLift 4015802
  have htrace : WordTrace (prefixWord ++ tailWord_4015802) baseStart_4015802 baseEnd_4015802 := by
    simpa [prefixWord, tailWord_4015802, baseEnd_4015802] using wordTrace_append hprefix tailTrace_4015802
  have hstable : (prefixWord ++ tailWord_4015802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015802).length < 2 ^ (prefixWord ++ tailWord_4015802).sum := by decide
  have hdescent : baseEnd_4015802 < baseStart_4015802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015804 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_4015804 : Nat := 118140960795 + 4015804 * 2 ^ 59
def prefixEnd_4015804 : Nat := 4983230072969 + 3 ^ 40 * 4015804 * 2
def baseEnd_4015804 : Nat := 1374691777498740921387773

theorem tailTrace_4015804 : CollatzResearch.WordTrace tailWord_4015804 prefixEnd_4015804 1374691777498740921387773 := by
  unfold tailWord_4015804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73234202371717713782711233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97645603162290285043614977 73234202371717713782711233)
  ·
    refine ⟨54925651778788285337033425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73234202371717713782711233 54925651778788285337033425)
    ·
      refine ⟨41194238834091214002775069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54925651778788285337033425 41194238834091214002775069)
      ·
        refine ⟨15447839562784205251040651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41194238834091214002775069 15447839562784205251040651)
        ·
          refine ⟨23171759344176307876560977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447839562784205251040651 23171759344176307876560977)
          ·
            refine ⟨17378819508132230907420733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23171759344176307876560977 17378819508132230907420733)
            ·
              refine ⟨6517057315549586590282775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17378819508132230907420733 6517057315549586590282775)
              ·
                refine ⟨9775585973324379885424163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517057315549586590282775 9775585973324379885424163)
                ·
                  refine ⟨14663378959986569828136245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9775585973324379885424163 14663378959986569828136245)
                  ·
                    refine ⟨1374691777498740921387773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14663378959986569828136245 1374691777498740921387773)
                    ·
                      rfl

theorem cell22_4015804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_4015804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015804 prefixEnd_4015804 := by exact prefixLift 4015804
  have htrace : WordTrace (prefixWord ++ tailWord_4015804) baseStart_4015804 baseEnd_4015804 := by
    simpa [prefixWord, tailWord_4015804, baseEnd_4015804] using wordTrace_append hprefix tailTrace_4015804
  have hstable : (prefixWord ++ tailWord_4015804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015804).length < 2 ^ (prefixWord ++ tailWord_4015804).sum := by decide
  have hdescent : baseEnd_4015804 < baseStart_4015804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015877 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_4015877 : Nat := 118140960795 + 4015877 * 2 ^ 59
def prefixEnd_4015877 : Nat := 4983230072969 + 3 ^ 40 * 4015877 * 2
def baseEnd_4015877 : Nat := 1374716766890593064312549

theorem tailTrace_4015877 : CollatzResearch.WordTrace tailWord_4015877 prefixEnd_4015877 1374716766890593064312549 := by
  unfold tailWord_4015877
  simp only [CollatzResearch.WordTrace]
  refine ⟨146471067272170961032829885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97647378181447307355219923 146471067272170961032829885)
  ·
    refine ⟨54926650227064110387311207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146471067272170961032829885 54926650227064110387311207)
    ·
      refine ⟨82389975340596165580966811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54926650227064110387311207 82389975340596165580966811)
      ·
        refine ⟨123584963010894248371450217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82389975340596165580966811 123584963010894248371450217)
        ·
          refine ⟨92688722258170686278587663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123584963010894248371450217 92688722258170686278587663)
          ·
            refine ⟨139033083387256029417881495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92688722258170686278587663 139033083387256029417881495)
            ·
              refine ⟨208549625080884044126822243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139033083387256029417881495 208549625080884044126822243)
              ·
                refine ⟨312824437621326066190233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208549625080884044126822243 312824437621326066190233365)
                ·
                  refine ⟨14663645513499659352667189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312824437621326066190233365 14663645513499659352667189)
                  ·
                    refine ⟨1374716766890593064312549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14663645513499659352667189 1374716766890593064312549)
                    ·
                      rfl

theorem cell22_4015877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_4015877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015877 prefixEnd_4015877 := by exact prefixLift 4015877
  have htrace : WordTrace (prefixWord ++ tailWord_4015877) baseStart_4015877 baseEnd_4015877 := by
    simpa [prefixWord, tailWord_4015877, baseEnd_4015877] using wordTrace_append hprefix tailTrace_4015877
  have hstable : (prefixWord ++ tailWord_4015877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015877).length < 2 ^ (prefixWord ++ tailWord_4015877).sum := by decide
  have hdescent : baseEnd_4015877 < baseStart_4015877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015885 : List Nat := [1, 7, 2, 1, 2, 9]
def baseStart_4015885 : Nat := 118140960795 + 4015885 * 2 ^ 59
def prefixEnd_4015885 : Nat := 4983230072969 + 3 ^ 40 * 4015885 * 2
def baseEnd_4015885 : Nat := 16971845746346712470525

theorem tailTrace_4015885 : CollatzResearch.WordTrace tailWord_4015885 prefixEnd_4015885 16971845746346712470525 := by
  unfold tailWord_4015885
  simp only [CollatzResearch.WordTrace]
  refine ⟨146471359056141978399121109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97647572704094652266080739 146471359056141978399121109)
  ·
    refine ⟨3432922477878327618729401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146471359056141978399121109 3432922477878327618729401)
    ·
      refine ⟨2574691858408745714047051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3432922477878327618729401 2574691858408745714047051)
      ·
        refine ⟨3862037787613118571070577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574691858408745714047051 3862037787613118571070577)
        ·
          refine ⟨2896528340709838928302933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862037787613118571070577 2896528340709838928302933)
          ·
            refine ⟨16971845746346712470525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2896528340709838928302933 16971845746346712470525)
            ·
              rfl

theorem cell22_4015885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 9].length) (baseStart_4015885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015885 prefixEnd_4015885 := by exact prefixLift 4015885
  have htrace : WordTrace (prefixWord ++ tailWord_4015885) baseStart_4015885 baseEnd_4015885 := by
    simpa [prefixWord, tailWord_4015885, baseEnd_4015885] using wordTrace_append hprefix tailTrace_4015885
  have hstable : (prefixWord ++ tailWord_4015885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015885).length < 2 ^ (prefixWord ++ tailWord_4015885).sum := by decide
  have hdescent : baseEnd_4015885 < baseStart_4015885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015909 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_4015909 : Nat := 118140960795 + 4015909 * 2 ^ 59
def prefixEnd_4015909 : Nat := 4983230072969 + 3 ^ 40 * 4015909 * 2
def baseEnd_4015909 : Nat := 1374727721144555647512451

theorem tailTrace_4015909 : CollatzResearch.WordTrace tailWord_4015909 prefixEnd_4015909 1374727721144555647512451 := by
  unfold tailWord_4015909
  simp only [CollatzResearch.WordTrace]
  refine ⟨146472234408055030497994781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97648156272036686998663187 146472234408055030497994781)
  ·
    refine ⟨54927087903020636436748043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146472234408055030497994781 54927087903020636436748043)
    ·
      refine ⟨82390631854530954655122065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54927087903020636436748043 82390631854530954655122065)
      ·
        refine ⟨61792973890898215991341549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82390631854530954655122065 61792973890898215991341549)
        ·
          refine ⟨23172365209086830996753081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61792973890898215991341549 23172365209086830996753081)
          ·
            refine ⟨17379273906815123247564811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23172365209086830996753081 17379273906815123247564811)
            ·
              refine ⟨26068910860222684871347217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17379273906815123247564811 26068910860222684871347217)
              ·
                refine ⟨19551683145167013653510413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26068910860222684871347217 19551683145167013653510413)
                ·
                  refine ⟨7331881179437630120066405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19551683145167013653510413 7331881179437630120066405)
                  ·
                    refine ⟨1374727721144555647512451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7331881179437630120066405 1374727721144555647512451)
                    ·
                      rfl

theorem cell22_4015909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_4015909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015909 prefixEnd_4015909 := by exact prefixLift 4015909
  have htrace : WordTrace (prefixWord ++ tailWord_4015909) baseStart_4015909 baseEnd_4015909 := by
    simpa [prefixWord, tailWord_4015909, baseEnd_4015909] using wordTrace_append hprefix tailTrace_4015909
  have hstable : (prefixWord ++ tailWord_4015909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015909).length < 2 ^ (prefixWord ++ tailWord_4015909).sum := by decide
  have hdescent : baseEnd_4015909 < baseStart_4015909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015939 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_4015939 : Nat := 118140960795 + 4015939 * 2 ^ 59
def prefixEnd_4015939 : Nat := 4983230072969 + 3 ^ 40 * 4015939 * 2
def baseEnd_4015939 : Nat := 1374737990757645569262359

theorem tailTrace_4015939 : CollatzResearch.WordTrace tailWord_4015939 prefixEnd_4015939 1374737990757645569262359 := by
  unfold tailWord_4015939
  simp only [CollatzResearch.WordTrace]
  refine ⟨146473328597946345621586871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97648885731964230414391247 146473328597946345621586871)
  ·
    refine ⟨219709992896919518432380307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146473328597946345621586871 219709992896919518432380307)
    ·
      refine ⟨329564989345379277648570461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219709992896919518432380307 329564989345379277648570461)
      ·
        refine ⟨123586871004517229118213923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329564989345379277648570461 123586871004517229118213923)
        ·
          refine ⟨185380306506775843677320885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123586871004517229118213923 185380306506775843677320885)
          ·
            refine ⟨17379403735010235344748833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185380306506775843677320885 17379403735010235344748833)
            ·
              refine ⟨13034552801257676508561625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17379403735010235344748833 13034552801257676508561625)
              ·
                refine ⟨9775914600943257381421219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034552801257676508561625 9775914600943257381421219)
                ·
                  refine ⟨14663871901414886072131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9775914600943257381421219 14663871901414886072131829)
                  ·
                    refine ⟨1374737990757645569262359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14663871901414886072131829 1374737990757645569262359)
                    ·
                      rfl

theorem cell22_4015939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_4015939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015939 prefixEnd_4015939 := by exact prefixLift 4015939
  have htrace : WordTrace (prefixWord ++ tailWord_4015939) baseStart_4015939 baseEnd_4015939 := by
    simpa [prefixWord, tailWord_4015939, baseEnd_4015939] using wordTrace_append hprefix tailTrace_4015939
  have hstable : (prefixWord ++ tailWord_4015939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015939).length < 2 ^ (prefixWord ++ tailWord_4015939).sum := by decide
  have hdescent : baseEnd_4015939 < baseStart_4015939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4015941 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 4]
def baseStart_4015941 : Nat := 118140960795 + 4015941 * 2 ^ 59
def prefixEnd_4015941 : Nat := 4983230072969 + 3 ^ 40 * 4015941 * 2
def baseEnd_4015941 : Nat := 458246225132839410237451

theorem tailTrace_4015941 : CollatzResearch.WordTrace tailWord_4015941 prefixEnd_4015941 458246225132839410237451 := by
  unfold tailWord_4015941
  simp only [CollatzResearch.WordTrace]
  refine ⟨146473401543939099963159677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97648934362626066642106451 146473401543939099963159677)
  ·
    refine ⟨54927525578977162486184879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146473401543939099963159677 54927525578977162486184879)
    ·
      refine ⟨82391288368465743729277319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54927525578977162486184879 82391288368465743729277319)
      ·
        refine ⟨123586932552698615593915979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82391288368465743729277319 123586932552698615593915979)
        ·
          refine ⟨185380398829047923390873969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123586932552698615593915979 185380398829047923390873969)
          ·
            refine ⟨139035299121785942543155477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185380398829047923390873969 139035299121785942543155477)
            ·
              refine ⟨6517279646333716056710413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139035299121785942543155477 6517279646333716056710413)
              ·
                refine ⟨2443979867375143521266405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6517279646333716056710413 2443979867375143521266405)
                ·
                  refine ⟨458246225132839410237451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443979867375143521266405 458246225132839410237451)
                  ·
                    rfl

theorem cell22_4015941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_4015941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4015941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4015941 prefixEnd_4015941 := by exact prefixLift 4015941
  have htrace : WordTrace (prefixWord ++ tailWord_4015941) baseStart_4015941 baseEnd_4015941 := by
    simpa [prefixWord, tailWord_4015941, baseEnd_4015941] using wordTrace_append hprefix tailTrace_4015941
  have hstable : (prefixWord ++ tailWord_4015941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4015941).length < 2 ^ (prefixWord ++ tailWord_4015941).sum := by decide
  have hdescent : baseEnd_4015941 < baseStart_4015941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4015941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016024 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_4016024 : Nat := 118140960795 + 4016024 * 2 ^ 59
def prefixEnd_4016024 : Nat := 4983230072969 + 3 ^ 40 * 4016024 * 2
def baseEnd_4016024 : Nat := 1374767087994733680887099

theorem tailTrace_4016024 : CollatzResearch.WordTrace tailWord_4016024 prefixEnd_4016024 1374767087994733680887099 := by
  unfold tailWord_4016024
  simp only [CollatzResearch.WordTrace]
  refine ⟨73238214401319202569215563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97650952535092270092287417 73238214401319202569215563)
  ·
    refine ⟨109857321601978803853823345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73238214401319202569215563 109857321601978803853823345)
    ·
      refine ⟨82392991201484102890367509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109857321601978803853823345 82392991201484102890367509)
      ·
        refine ⟨3862171462569567322985977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82392991201484102890367509 3862171462569567322985977)
        ·
          refine ⟨2896628596927175492239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862171462569567322985977 2896628596927175492239483)
          ·
            refine ⟨4344942895390763238359225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896628596927175492239483 4344942895390763238359225)
            ·
              refine ⟨3258707171543072428769419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4344942895390763238359225 3258707171543072428769419)
              ·
                refine ⟨4888060757314608643154129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258707171543072428769419 4888060757314608643154129)
                ·
                  refine ⟨3666045567985956482365597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888060757314608643154129 3666045567985956482365597)
                  ·
                    refine ⟨1374767087994733680887099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666045567985956482365597 1374767087994733680887099)
                    ·
                      rfl

theorem cell22_4016024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_4016024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016024 prefixEnd_4016024 := by exact prefixLift 4016024
  have htrace : WordTrace (prefixWord ++ tailWord_4016024) baseStart_4016024 baseEnd_4016024 := by
    simpa [prefixWord, tailWord_4016024, baseEnd_4016024] using wordTrace_append hprefix tailTrace_4016024
  have hstable : (prefixWord ++ tailWord_4016024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016024).length < 2 ^ (prefixWord ++ tailWord_4016024).sum := by decide
  have hdescent : baseEnd_4016024 < baseStart_4016024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016093 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 6]
def baseStart_4016093 : Nat := 118140960795 + 4016093 * 2 ^ 59
def prefixEnd_4016093 : Nat := 4983230072969 + 3 ^ 40 * 4016093 * 2
def baseEnd_4016093 : Nat := 458263569368280166970629

theorem tailTrace_4016093 : CollatzResearch.WordTrace tailWord_4016093 prefixEnd_4016093 458263569368280166970629 := by
  unfold tailWord_4016093
  simp only [CollatzResearch.WordTrace]
  refine ⟨146478945439388429922692933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97652630292925619948461955 146478945439388429922692933)
  ·
    refine ⟨27464802269885330610504925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146478945439388429922692933 27464802269885330610504925)
    ·
      refine ⟨10299300851206998978939347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27464802269885330610504925 10299300851206998978939347)
      ·
        refine ⟨15448951276810498468409021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299300851206998978939347 15448951276810498468409021)
        ·
          refine ⟨5793356728803936925653383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15448951276810498468409021 5793356728803936925653383)
          ·
            refine ⟨8690035093205905388480075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793356728803936925653383 8690035093205905388480075)
            ·
              refine ⟨13035052639808858082720113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690035093205905388480075 13035052639808858082720113)
              ·
                refine ⟨9776289479856643562040085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13035052639808858082720113 9776289479856643562040085)
                ·
                  refine ⟨458263569368280166970629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9776289479856643562040085 458263569368280166970629)
                  ·
                    rfl

theorem cell22_4016093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_4016093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016093 prefixEnd_4016093 := by exact prefixLift 4016093
  have htrace : WordTrace (prefixWord ++ tailWord_4016093) baseStart_4016093 baseEnd_4016093 := by
    simpa [prefixWord, tailWord_4016093, baseEnd_4016093] using wordTrace_append hprefix tailTrace_4016093
  have hstable : (prefixWord ++ tailWord_4016093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016093).length < 2 ^ (prefixWord ++ tailWord_4016093).sum := by decide
  have hdescent : baseEnd_4016093 < baseStart_4016093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016106 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4016106 : Nat := 118140960795 + 4016106 * 2 ^ 59
def prefixEnd_4016106 : Nat := 4983230072969 + 3 ^ 40 * 4016106 * 2
def baseEnd_4016106 : Nat := 1374795158270512800336847

theorem tailTrace_4016106 : CollatzResearch.WordTrace tailWord_4016106 prefixEnd_4016106 1374795158270512800336847 := by
  unfold tailWord_4016106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36619854897085333285729043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97652946392227555428610781 36619854897085333285729043)
  ·
    refine ⟨54929782345627999928593565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36619854897085333285729043 54929782345627999928593565)
    ·
      refine ⟨20598668379610499973222587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54929782345627999928593565 20598668379610499973222587)
      ·
        refine ⟨30898002569415749959833881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20598668379610499973222587 30898002569415749959833881)
        ·
          refine ⟨23173501927061812469875411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30898002569415749959833881 23173501927061812469875411)
          ·
            refine ⟨34760252890592718704813117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23173501927061812469875411 34760252890592718704813117)
            ·
              refine ⟨13035094833972269514304919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34760252890592718704813117 13035094833972269514304919)
              ·
                refine ⟨19552642250958404271457379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035094833972269514304919 19552642250958404271457379)
                ·
                  refine ⟨29328963376437606407186069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19552642250958404271457379 29328963376437606407186069)
                  ·
                    refine ⟨1374795158270512800336847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29328963376437606407186069 1374795158270512800336847)
                    ·
                      rfl

theorem cell22_4016106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4016106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016106 prefixEnd_4016106 := by exact prefixLift 4016106
  have htrace : WordTrace (prefixWord ++ tailWord_4016106) baseStart_4016106 baseEnd_4016106 := by
    simpa [prefixWord, tailWord_4016106, baseEnd_4016106] using wordTrace_append hprefix tailTrace_4016106
  have hstable : (prefixWord ++ tailWord_4016106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016106).length < 2 ^ (prefixWord ++ tailWord_4016106).sum := by decide
  have hdescent : baseEnd_4016106 < baseStart_4016106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016110 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_4016110 : Nat := 118140960795 + 4016110 * 2 ^ 59
def prefixEnd_4016110 : Nat := 4983230072969 + 3 ^ 40 * 4016110 * 2
def baseEnd_4016110 : Nat := 458265509184086041078945

theorem tailTrace_4016110 : CollatzResearch.WordTrace tailWord_4016110 prefixEnd_4016110 458265509184086041078945 := by
  unfold tailWord_4016110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309945685040855228257723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97653043653551227884041189 18309945685040855228257723)
  ·
    refine ⟨27464918527561282842386585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309945685040855228257723 27464918527561282842386585)
    ·
      refine ⟨20598688895670962131789939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27464918527561282842386585 20598688895670962131789939)
      ·
        refine ⟨30898033343506443197684909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20598688895670962131789939 30898033343506443197684909)
        ·
          refine ⟨11586762503814916199131841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30898033343506443197684909 11586762503814916199131841)
          ·
            refine ⟨8690071877861187149348881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11586762503814916199131841 8690071877861187149348881)
            ·
              refine ⟨6517553908395890362011661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690071877861187149348881 6517553908395890362011661)
              ·
                refine ⟨2444082715648458885754373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6517553908395890362011661 2444082715648458885754373)
                ·
                  refine ⟨458265509184086041078945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2444082715648458885754373 458265509184086041078945)
                  ·
                    rfl

theorem cell22_4016110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_4016110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016110 prefixEnd_4016110 := by exact prefixLift 4016110
  have htrace : WordTrace (prefixWord ++ tailWord_4016110) baseStart_4016110 baseEnd_4016110 := by
    simpa [prefixWord, tailWord_4016110, baseEnd_4016110] using wordTrace_append hprefix tailTrace_4016110
  have hstable : (prefixWord ++ tailWord_4016110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016110).length < 2 ^ (prefixWord ++ tailWord_4016110).sum := by decide
  have hdescent : baseEnd_4016110 < baseStart_4016110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016119 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_4016119 : Nat := 118140960795 + 4016119 * 2 ^ 59
def prefixEnd_4016119 : Nat := 4983230072969 + 3 ^ 40 * 4016119 * 2
def baseEnd_4016119 : Nat := 1374799608436185099761807

theorem tailTrace_4016119 : CollatzResearch.WordTrace tailWord_4016119 prefixEnd_4016119 1374799608436185099761807 := by
  unfold tailWord_4016119
  simp only [CollatzResearch.WordTrace]
  refine ⟨146479893737294236363139411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97653262491529490908759607 146479893737294236363139411)
  ·
    refine ⟨219719840605941354544709117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146479893737294236363139411 219719840605941354544709117)
    ·
      refine ⟨82394940227228007954265919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219719840605941354544709117 82394940227228007954265919)
      ·
        refine ⟨123592410340842011931398879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82394940227228007954265919 123592410340842011931398879)
        ·
          refine ⟨185388615511263017897098319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123592410340842011931398879 185388615511263017897098319)
          ·
            refine ⟨278082923266894526845647479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185388615511263017897098319 278082923266894526845647479)
            ·
              refine ⟨417124384900341790268471219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278082923266894526845647479 417124384900341790268471219)
              ·
                refine ⟨625686577350512685402706829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417124384900341790268471219 625686577350512685402706829)
                ·
                  refine ⟨234632466506442257026015061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625686577350512685402706829 234632466506442257026015061)
                  ·
                    refine ⟨1374799608436185099761807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234632466506442257026015061 1374799608436185099761807)
                    ·
                      rfl

theorem cell22_4016119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_4016119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016119 prefixEnd_4016119 := by exact prefixLift 4016119
  have htrace : WordTrace (prefixWord ++ tailWord_4016119) baseStart_4016119 baseEnd_4016119 := by
    simpa [prefixWord, tailWord_4016119, baseEnd_4016119] using wordTrace_append hprefix tailTrace_4016119
  have hstable : (prefixWord ++ tailWord_4016119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016119).length < 2 ^ (prefixWord ++ tailWord_4016119).sum := by decide
  have hdescent : baseEnd_4016119 < baseStart_4016119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016181 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4016181 : Nat := 118140960795 + 4016181 * 2 ^ 59
def prefixEnd_4016181 : Nat := 4983230072969 + 3 ^ 40 * 4016181 * 2
def baseEnd_4016181 : Nat := 1374820832303237604711617

theorem tailTrace_4016181 : CollatzResearch.WordTrace tailWord_4016181 prefixEnd_4016181 1374820832303237604711617 := by
  unfold tailWord_4016181
  simp only [CollatzResearch.WordTrace]
  refine ⟨146482155063069620951896397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97654770042046413967930931 146482155063069620951896397)
  ·
    refine ⟨54930808148651107856961149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146482155063069620951896397 54930808148651107856961149)
    ·
      refine ⟨20599053055744165446360431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54930808148651107856961149 20599053055744165446360431)
      ·
        refine ⟨30898579583616248169540647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20599053055744165446360431 30898579583616248169540647)
        ·
          refine ⟨46347869375424372254310971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30898579583616248169540647 46347869375424372254310971)
          ·
            refine ⟨69521804063136558381466457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46347869375424372254310971 69521804063136558381466457)
            ·
              refine ⟨52141353047352418786099843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69521804063136558381466457 52141353047352418786099843)
              ·
                refine ⟨78212029571028628179149765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52141353047352418786099843 78212029571028628179149765)
                ·
                  refine ⟨14664755544567867783590581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78212029571028628179149765 14664755544567867783590581)
                  ·
                    refine ⟨1374820832303237604711617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14664755544567867783590581 1374820832303237604711617)
                    ·
                      rfl

theorem cell22_4016181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4016181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016181 prefixEnd_4016181 := by exact prefixLift 4016181
  have htrace : WordTrace (prefixWord ++ tailWord_4016181) baseStart_4016181 baseEnd_4016181 := by
    simpa [prefixWord, tailWord_4016181, baseEnd_4016181] using wordTrace_append hprefix tailTrace_4016181
  have hstable : (prefixWord ++ tailWord_4016181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016181).length < 2 ^ (prefixWord ++ tailWord_4016181).sum := by decide
  have hdescent : baseEnd_4016181 < baseStart_4016181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016213 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4016213 : Nat := 118140960795 + 4016213 * 2 ^ 59
def prefixEnd_4016213 : Nat := 4983230072969 + 3 ^ 40 * 4016213 * 2
def baseEnd_4016213 : Nat := 1374831786557200187911519

theorem tailTrace_4016213 : CollatzResearch.WordTrace tailWord_4016213 prefixEnd_4016213 1374831786557200187911519 := by
  unfold tailWord_4016213
  simp only [CollatzResearch.WordTrace]
  refine ⟨146483322198953690417061293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97655548132635793611374195 146483322198953690417061293)
  ·
    refine ⟨54931245824607633906397985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146483322198953690417061293 54931245824607633906397985)
    ·
      refine ⟨41198434368455725429798489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54931245824607633906397985 41198434368455725429798489)
      ·
        refine ⟨30898825776341794072348867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41198434368455725429798489 30898825776341794072348867)
        ·
          refine ⟨46348238664512691108523301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30898825776341794072348867 46348238664512691108523301)
          ·
            refine ⟨8690294749596129582848119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46348238664512691108523301 8690294749596129582848119)
            ·
              refine ⟨13035442124394194374272179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690294749596129582848119 13035442124394194374272179)
              ·
                refine ⟨19553163186591291561408269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035442124394194374272179 19553163186591291561408269)
                ·
                  refine ⟨7332436194971734335528101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19553163186591291561408269 7332436194971734335528101)
                  ·
                    refine ⟨1374831786557200187911519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332436194971734335528101 1374831786557200187911519)
                    ·
                      rfl

theorem cell22_4016213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4016213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016213 prefixEnd_4016213 := by exact prefixLift 4016213
  have htrace : WordTrace (prefixWord ++ tailWord_4016213) baseStart_4016213 baseEnd_4016213 := by
    simpa [prefixWord, tailWord_4016213, baseEnd_4016213] using wordTrace_append hprefix tailTrace_4016213
  have hstable : (prefixWord ++ tailWord_4016213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016213).length < 2 ^ (prefixWord ++ tailWord_4016213).sum := by decide
  have hdescent : baseEnd_4016213 < baseStart_4016213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016260 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4016260 : Nat := 118140960795 + 4016260 * 2 ^ 59
def prefixEnd_4016260 : Nat := 4983230072969 + 3 ^ 40 * 4016260 * 2
def baseEnd_4016260 : Nat := 1374847875617707731986375

theorem tailTrace_4016260 : CollatzResearch.WordTrace tailWord_4016260 prefixEnd_4016260 1374847875617707731986375 := by
  unfold tailWord_4016260
  simp only [CollatzResearch.WordTrace]
  refine ⟨73242518214891708722011117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97656690953188944962681489 73242518214891708722011117)
  ·
    refine ⟨27465944330584390770754169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73242518214891708722011117 27465944330584390770754169)
    ·
      refine ⟨20599458247938293078065627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27465944330584390770754169 20599458247938293078065627)
      ·
        refine ⟨30899187371907439617098441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20599458247938293078065627 30899187371907439617098441)
        ·
          refine ⟨23174390528930579712823831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30899187371907439617098441 23174390528930579712823831)
          ·
            refine ⟨34761585793395869569235747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23174390528930579712823831 34761585793395869569235747)
            ·
              refine ⟨52142378690093804353853621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34761585793395869569235747 52142378690093804353853621)
              ·
                refine ⟨4888348002196294158173777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52142378690093804353853621 4888348002196294158173777)
                ·
                  refine ⟨3666261001647220618630333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888348002196294158173777 3666261001647220618630333)
                  ·
                    refine ⟨1374847875617707731986375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666261001647220618630333 1374847875617707731986375)
                    ·
                      rfl

theorem cell22_4016260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4016260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016260 prefixEnd_4016260 := by exact prefixLift 4016260
  have htrace : WordTrace (prefixWord ++ tailWord_4016260) baseStart_4016260 baseEnd_4016260 := by
    simpa [prefixWord, tailWord_4016260, baseEnd_4016260] using wordTrace_append hprefix tailTrace_4016260
  have hstable : (prefixWord ++ tailWord_4016260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016260).length < 2 ^ (prefixWord ++ tailWord_4016260).sum := by decide
  have hdescent : baseEnd_4016260 < baseStart_4016260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016429 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4016429 : Nat := 118140960795 + 4016429 * 2 ^ 59
def prefixEnd_4016429 : Nat := 4983230072969 + 3 ^ 40 * 4016429 * 2
def baseEnd_4016429 : Nat := 1374905727771447624510857

theorem tailTrace_4016429 : CollatzResearch.WordTrace tailWord_4016429 prefixEnd_4016429 1374905727771447624510857 := by
  unfold tailWord_4016429
  simp only [CollatzResearch.WordTrace]
  refine ⟨146491200366171159306924341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97660800244114106204616227 146491200366171159306924341)
  ·
    refine ⟨13733550034328546185024157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146491200366171159306924341 13733550034328546185024157)
    ·
      refine ⟨5150081262873204819384059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13733550034328546185024157 5150081262873204819384059)
      ·
        refine ⟨7725121894309807229076089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150081262873204819384059 7725121894309807229076089)
        ·
          refine ⟨5793841420732355421807067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7725121894309807229076089 5793841420732355421807067)
          ·
            refine ⟨8690762131098533132710601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793841420732355421807067 8690762131098533132710601)
            ·
              refine ⟨6518071598323899849532951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690762131098533132710601 6518071598323899849532951)
              ·
                refine ⟨9777107397485849774299427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518071598323899849532951 9777107397485849774299427)
                ·
                  refine ⟨14665661096228774661449141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777107397485849774299427 14665661096228774661449141)
                  ·
                    refine ⟨1374905727771447624510857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14665661096228774661449141 1374905727771447624510857)
                    ·
                      rfl

theorem cell22_4016429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4016429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016429 prefixEnd_4016429 := by exact prefixLift 4016429
  have htrace : WordTrace (prefixWord ++ tailWord_4016429) baseStart_4016429 baseEnd_4016429 := by
    simpa [prefixWord, tailWord_4016429, baseEnd_4016429] using wordTrace_append hprefix tailTrace_4016429
  have hstable : (prefixWord ++ tailWord_4016429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016429).length < 2 ^ (prefixWord ++ tailWord_4016429).sum := by decide
  have hdescent : baseEnd_4016429 < baseStart_4016429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016440 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_4016440 : Nat := 118140960795 + 4016440 * 2 ^ 59
def prefixEnd_4016440 : Nat := 4983230072969 + 3 ^ 40 * 4016440 * 2
def baseEnd_4016440 : Nat := 1374909493296247262485823

theorem tailTrace_4016440 : CollatzResearch.WordTrace tailWord_4016440 prefixEnd_4016440 1374909493296247262485823 := by
  unfold tailWord_4016440
  simp only [CollatzResearch.WordTrace]
  refine ⟨73245800784565654092787387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97661067712754205457049849 73245800784565654092787387)
  ·
    refine ⟨109868701176848481139181081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73245800784565654092787387 109868701176848481139181081)
    ·
      refine ⟨82401525882636360854385811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109868701176848481139181081 82401525882636360854385811)
      ·
        refine ⟨123602288823954541281578717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82401525882636360854385811 123602288823954541281578717)
        ·
          refine ⟨46350858308982952980592019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123602288823954541281578717 46350858308982952980592019)
          ·
            refine ⟨69526287463474429470888029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46350858308982952980592019 69526287463474429470888029)
            ·
              refine ⟨26072357798802911051583011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69526287463474429470888029 26072357798802911051583011)
              ·
                refine ⟨39108536698204366577374517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26072357798802911051583011 39108536698204366577374517)
                ·
                  refine ⟨3666425315456659366628861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39108536698204366577374517 3666425315456659366628861)
                  ·
                    refine ⟨1374909493296247262485823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666425315456659366628861 1374909493296247262485823)
                    ·
                      rfl

theorem cell22_4016440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_4016440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016440 prefixEnd_4016440 := by exact prefixLift 4016440
  have htrace : WordTrace (prefixWord ++ tailWord_4016440) baseStart_4016440 baseEnd_4016440 := by
    simpa [prefixWord, tailWord_4016440, baseEnd_4016440] using wordTrace_append hprefix tailTrace_4016440
  have hstable : (prefixWord ++ tailWord_4016440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016440).length < 2 ^ (prefixWord ++ tailWord_4016440).sum := by decide
  have hdescent : baseEnd_4016440 < baseStart_4016440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016485 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_4016485 : Nat := 118140960795 + 4016485 * 2 ^ 59
def prefixEnd_4016485 : Nat := 4983230072969 + 3 ^ 40 * 4016485 * 2
def baseEnd_4016485 : Nat := 1374924897715882145110685

theorem tailTrace_4016485 : CollatzResearch.WordTrace tailWord_4016485 prefixEnd_4016485 1374924897715882145110685 := by
  unfold tailWord_4016485
  simp only [CollatzResearch.WordTrace]
  refine ⟨146493242853968280870962909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97662161902645520580641939 146493242853968280870962909)
  ·
    refine ⟨54934966070238105326611091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146493242853968280870962909 54934966070238105326611091)
    ·
      refine ⟨82402449105357157989916637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54934966070238105326611091 82402449105357157989916637)
      ·
        refine ⟨30900918414508934246218739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82402449105357157989916637 30900918414508934246218739)
        ·
          refine ⟨46351377621763401369328109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30900918414508934246218739 46351377621763401369328109)
          ·
            refine ⟨17381766608161275513498041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46351377621763401369328109 17381766608161275513498041)
            ·
              refine ⟨13036324956120956635123531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17381766608161275513498041 13036324956120956635123531)
              ·
                refine ⟨19554487434181434952685297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13036324956120956635123531 19554487434181434952685297)
                ·
                  refine ⟨14665865575636076214513973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19554487434181434952685297 14665865575636076214513973)
                  ·
                    refine ⟨1374924897715882145110685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14665865575636076214513973 1374924897715882145110685)
                    ·
                      rfl

theorem cell22_4016485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_4016485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016485 prefixEnd_4016485 := by exact prefixLift 4016485
  have htrace : WordTrace (prefixWord ++ tailWord_4016485) baseStart_4016485 baseEnd_4016485 := by
    simpa [prefixWord, tailWord_4016485, baseEnd_4016485] using wordTrace_append hprefix tailTrace_4016485
  have hstable : (prefixWord ++ tailWord_4016485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016485).length < 2 ^ (prefixWord ++ tailWord_4016485).sum := by decide
  have hdescent : baseEnd_4016485 < baseStart_4016485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016562 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_4016562 : Nat := 118140960795 + 4016562 * 2 ^ 59
def prefixEnd_4016562 : Nat := 4983230072969 + 3 ^ 40 * 4016562 * 2
def baseEnd_4016562 : Nat := 1374951256389479610935449

theorem tailTrace_4016562 : CollatzResearch.WordTrace tailWord_4016562 prefixEnd_4016562 1374951256389479610935449 := by
  unfold tailWord_4016562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624012818672330755378985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97664034183126215347677293 36624012818672330755378985)
  ·
    refine ⟨27468009614004248066534239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36624012818672330755378985 27468009614004248066534239)
    ·
      refine ⟨41202014421006372099801359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27468009614004248066534239 41202014421006372099801359)
      ·
        refine ⟨61803021631509558149702039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41202014421006372099801359 61803021631509558149702039)
        ·
          refine ⟨92704532447264337224553059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61803021631509558149702039 92704532447264337224553059)
          ·
            refine ⟨139056798670896505836829589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92704532447264337224553059 139056798670896505836829589)
            ·
              refine ⟨6518287437698273711101387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139056798670896505836829589 6518287437698273711101387)
              ·
                refine ⟨9777431156547410566652081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518287437698273711101387 9777431156547410566652081)
                ·
                  refine ⟨7333073367410557924989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9777431156547410566652081 7333073367410557924989061)
                  ·
                    refine ⟨1374951256389479610935449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333073367410557924989061 1374951256389479610935449)
                    ·
                      rfl

theorem cell22_4016562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_4016562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016562 prefixEnd_4016562 := by exact prefixLift 4016562
  have htrace : WordTrace (prefixWord ++ tailWord_4016562) baseStart_4016562 baseEnd_4016562 := by
    simpa [prefixWord, tailWord_4016562, baseEnd_4016562] using wordTrace_append hprefix tailTrace_4016562
  have hstable : (prefixWord ++ tailWord_4016562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016562).length < 2 ^ (prefixWord ++ tailWord_4016562).sum := by decide
  have hdescent : baseEnd_4016562 < baseStart_4016562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016620 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_4016620 : Nat := 118140960795 + 4016620 * 2 ^ 59
def prefixEnd_4016620 : Nat := 4983230072969 + 3 ^ 40 * 4016620 * 2
def baseEnd_4016620 : Nat := 1374971110974786792985271

theorem tailTrace_4016620 : CollatzResearch.WordTrace tailWord_4016620 prefixEnd_4016620 1374971110974786792985271 := by
  unfold tailWord_4016620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73249083354239599463563657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97665444472319465951418209 73249083354239599463563657)
  ·
    refine ⟨54936812515679699597672743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73249083354239599463563657 54936812515679699597672743)
    ·
      refine ⟨82405218773519549396509115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54936812515679699597672743 82405218773519549396509115)
      ·
        refine ⟨123607828160279324094763673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82405218773519549396509115 123607828160279324094763673)
        ·
          refine ⟨92705871120209493071072755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123607828160279324094763673 92705871120209493071072755)
          ·
            refine ⟨139058806680314239606609133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92705871120209493071072755 139058806680314239606609133)
            ·
              refine ⟨52147052505117839852478425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139058806680314239606609133 52147052505117839852478425)
              ·
                refine ⟨39110289378838379889358819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52147052505117839852478425 39110289378838379889358819)
                ·
                  refine ⟨58665434068257569834038229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39110289378838379889358819 58665434068257569834038229)
                  ·
                    refine ⟨1374971110974786792985271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58665434068257569834038229 1374971110974786792985271)
                    ·
                      rfl

theorem cell22_4016620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_4016620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016620 prefixEnd_4016620 := by exact prefixLift 4016620
  have htrace : WordTrace (prefixWord ++ tailWord_4016620) baseStart_4016620 baseEnd_4016620 := by
    simpa [prefixWord, tailWord_4016620, baseEnd_4016620] using wordTrace_append hprefix tailTrace_4016620
  have hstable : (prefixWord ++ tailWord_4016620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016620).length < 2 ^ (prefixWord ++ tailWord_4016620).sum := by decide
  have hdescent : baseEnd_4016620 < baseStart_4016620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016669 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4016669 : Nat := 118140960795 + 4016669 * 2 ^ 59
def prefixEnd_4016669 : Nat := 4983230072969 + 3 ^ 40 * 4016669 * 2
def baseEnd_4016669 : Nat := 1374987884676166998510121

theorem tailTrace_4016669 : CollatzResearch.WordTrace tailWord_4016669 prefixEnd_4016669 1374987884676166998510121 := by
  unfold tailWord_4016669
  simp only [CollatzResearch.WordTrace]
  refine ⟨146499953885301680295661061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97666635923534453530440707 146499953885301680295661061)
  ·
    refine ⟨27468741353494065055436449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146499953885301680295661061 27468741353494065055436449)
    ·
      refine ⟨20601556015120548791577337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27468741353494065055436449 20601556015120548791577337)
      ·
        refine ⟨15451167011340411593683003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20601556015120548791577337 15451167011340411593683003)
        ·
          refine ⟨23176750517010617390524505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15451167011340411593683003 23176750517010617390524505)
          ·
            refine ⟨17382562887757963042893379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23176750517010617390524505 17382562887757963042893379)
            ·
              refine ⟨26073844331636944564340069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17382562887757963042893379 26073844331636944564340069)
              ·
                refine ⟨4888845812181927105813763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26073844331636944564340069 4888845812181927105813763)
                ·
                  refine ⟨7333268718272890658720645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888845812181927105813763 7333268718272890658720645)
                  ·
                    refine ⟨1374987884676166998510121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333268718272890658720645 1374987884676166998510121)
                    ·
                      rfl

theorem cell22_4016669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4016669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016669 prefixEnd_4016669 := by exact prefixLift 4016669
  have htrace : WordTrace (prefixWord ++ tailWord_4016669) baseStart_4016669 baseEnd_4016669 := by
    simpa [prefixWord, tailWord_4016669, baseEnd_4016669] using wordTrace_append hprefix tailTrace_4016669
  have hstable : (prefixWord ++ tailWord_4016669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016669).length < 2 ^ (prefixWord ++ tailWord_4016669).sum := by decide
  have hdescent : baseEnd_4016669 < baseStart_4016669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016819 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 6]
def baseStart_4016819 : Nat := 118140960795 + 4016819 * 2 ^ 59
def prefixEnd_4016819 : Nat := 4983230072969 + 3 ^ 40 * 4016819 * 2
def baseEnd_4016819 : Nat := 458346410913872202419887

theorem tailTrace_4016819 : CollatzResearch.WordTrace tailWord_4016819 prefixEnd_4016819 458346410913872202419887 := by
  unfold tailWord_4016819
  simp only [CollatzResearch.WordTrace]
  refine ⟨146505424834758255913621511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97670283223172170609081007 146505424834758255913621511)
  ·
    refine ⟨219758137252137383870432267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146505424834758255913621511 219758137252137383870432267)
    ·
      refine ⟨329637205878206075805648401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219758137252137383870432267 329637205878206075805648401)
      ·
        refine ⟨247227904408654556854236301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329637205878206075805648401 247227904408654556854236301)
        ·
          refine ⟨92710464153245458820338613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247227904408654556854236301 92710464153245458820338613)
          ·
            refine ⟨8691606014366761764406745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92710464153245458820338613 8691606014366761764406745)
            ·
              refine ⟨6518704510775071323305059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691606014366761764406745 6518704510775071323305059)
              ·
                refine ⟨9778056766162606984957589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518704510775071323305059 9778056766162606984957589)
                ·
                  refine ⟨458346410913872202419887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9778056766162606984957589 458346410913872202419887)
                  ·
                    rfl

theorem cell22_4016819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 6].length) (baseStart_4016819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016819 prefixEnd_4016819 := by exact prefixLift 4016819
  have htrace : WordTrace (prefixWord ++ tailWord_4016819) baseStart_4016819 baseEnd_4016819 := by
    simpa [prefixWord, tailWord_4016819, baseEnd_4016819] using wordTrace_append hprefix tailTrace_4016819
  have hstable : (prefixWord ++ tailWord_4016819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016819).length < 2 ^ (prefixWord ++ tailWord_4016819).sum := by decide
  have hdescent : baseEnd_4016819 < baseStart_4016819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016849 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_4016849 : Nat := 118140960795 + 4016849 * 2 ^ 59
def prefixEnd_4016849 : Nat := 4983230072969 + 3 ^ 40 * 4016849 * 2
def baseEnd_4016849 : Nat := 1375049502354706529009569

theorem tailTrace_4016849 : CollatzResearch.WordTrace tailWord_4016849 prefixEnd_4016849 1375049502354706529009569 := by
  unfold tailWord_4016849
  simp only [CollatzResearch.WordTrace]
  refine ⟨146506519024649571037213601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97671012683099714024809067 146506519024649571037213601)
  ·
    refine ⟨109879889268487178277910201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146506519024649571037213601 109879889268487178277910201)
    ·
      refine ⟨82409916951365383708432651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109879889268487178277910201 82409916951365383708432651)
      ·
        refine ⟨123614875427048075562648977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82409916951365383708432651 123614875427048075562648977)
        ·
          refine ⟨92711156570286056671986733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123614875427048075562648977 92711156570286056671986733)
          ·
            refine ⟨34766683713857271251995025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92711156570286056671986733 34766683713857271251995025)
            ·
              refine ⟨26075012785392953438996269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34766683713857271251995025 26075012785392953438996269)
              ·
                refine ⟨9778129794522357539623601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26075012785392953438996269 9778129794522357539623601)
                ·
                  refine ⟨7333597345891768154717701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9778129794522357539623601 7333597345891768154717701)
                  ·
                    refine ⟨1375049502354706529009569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333597345891768154717701 1375049502354706529009569)
                    ·
                      rfl

theorem cell22_4016849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_4016849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016849 prefixEnd_4016849 := by exact prefixLift 4016849
  have htrace : WordTrace (prefixWord ++ tailWord_4016849) baseStart_4016849 baseEnd_4016849 := by
    simpa [prefixWord, tailWord_4016849, baseEnd_4016849] using wordTrace_append hprefix tailTrace_4016849
  have hstable : (prefixWord ++ tailWord_4016849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016849).length < 2 ^ (prefixWord ++ tailWord_4016849).sum := by decide
  have hdescent : baseEnd_4016849 < baseStart_4016849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016930 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4016930 : Nat := 118140960795 + 4016930 * 2 ^ 59
def prefixEnd_4016930 : Nat := 4983230072969 + 3 ^ 40 * 4016930 * 2
def baseEnd_4016930 : Nat := 1375077230310049317734321

theorem tailTrace_4016930 : CollatzResearch.WordTrace tailWord_4016930 prefixEnd_4016930 1375077230310049317734321 := by
  unfold tailWord_4016930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36627368334339030467728061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97672982224904081247274829 36627368334339030467728061)
  ·
    refine ⟨13735263125377136425398023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36627368334339030467728061 13735263125377136425398023)
    ·
      refine ⟨20602894688065704638097035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735263125377136425398023 20602894688065704638097035)
      ·
        refine ⟨30904342032098556957145553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20602894688065704638097035 30904342032098556957145553)
        ·
          refine ⟨23178256524073917717859165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30904342032098556957145553 23178256524073917717859165)
          ·
            refine ⟨8691846196527719144197187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23178256524073917717859165 8691846196527719144197187)
            ·
              refine ⟨13037769294791578716295781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691846196527719144197187 13037769294791578716295781)
              ·
                refine ⟨2444581742773421009305459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13037769294791578716295781 2444581742773421009305459)
                ·
                  refine ⟨3666872614160131513958189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444581742773421009305459 3666872614160131513958189)
                  ·
                    refine ⟨1375077230310049317734321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666872614160131513958189 1375077230310049317734321)
                    ·
                      rfl

theorem cell22_4016930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4016930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016930 prefixEnd_4016930 := by exact prefixLift 4016930
  have htrace : WordTrace (prefixWord ++ tailWord_4016930) baseStart_4016930 baseEnd_4016930 := by
    simpa [prefixWord, tailWord_4016930, baseEnd_4016930] using wordTrace_append hprefix tailTrace_4016930
  have hstable : (prefixWord ++ tailWord_4016930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016930).length < 2 ^ (prefixWord ++ tailWord_4016930).sum := by decide
  have hdescent : baseEnd_4016930 < baseStart_4016930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016939 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_4016939 : Nat := 118140960795 + 4016939 * 2 ^ 59
def prefixEnd_4016939 : Nat := 4983230072969 + 3 ^ 40 * 4016939 * 2
def baseEnd_4016939 : Nat := 1375080311193976294259293

theorem tailTrace_4016939 : CollatzResearch.WordTrace tailWord_4016939 prefixEnd_4016939 1375080311193976294259293 := by
  unfold tailWord_4016939
  simp only [CollatzResearch.WordTrace]
  refine ⟨146509801594323516407989871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97673201062882344271993247 146509801594323516407989871)
  ·
    refine ⟨219764702391485274611984807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146509801594323516407989871 219764702391485274611984807)
    ·
      refine ⟨329647053587227911917977211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219764702391485274611984807 329647053587227911917977211)
      ·
        refine ⟨494470580380841867876965817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329647053587227911917977211 494470580380841867876965817)
        ·
          refine ⟨370852935285631400907724363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494470580380841867876965817 370852935285631400907724363)
          ·
            refine ⟨556279402928447101361586545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370852935285631400907724363 556279402928447101361586545)
            ·
              refine ⟨417209552196335326021189909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556279402928447101361586545 417209552196335326021189909)
              ·
                refine ⟨19556697759203218407243277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 417209552196335326021189909 19556697759203218407243277)
                ·
                  refine ⟨7333761659701206902716229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19556697759203218407243277 7333761659701206902716229)
                  ·
                    refine ⟨1375080311193976294259293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333761659701206902716229 1375080311193976294259293)
                    ·
                      rfl

theorem cell22_4016939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_4016939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016939 prefixEnd_4016939 := by exact prefixLift 4016939
  have htrace : WordTrace (prefixWord ++ tailWord_4016939) baseStart_4016939 baseEnd_4016939 := by
    simpa [prefixWord, tailWord_4016939, baseEnd_4016939] using wordTrace_append hprefix tailTrace_4016939
  have hstable : (prefixWord ++ tailWord_4016939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016939).length < 2 ^ (prefixWord ++ tailWord_4016939).sum := by decide
  have hdescent : baseEnd_4016939 < baseStart_4016939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016956 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_4016956 : Nat := 118140960795 + 4016956 * 2 ^ 59
def prefixEnd_4016956 : Nat := 4983230072969 + 3 ^ 40 * 4016956 * 2
def baseEnd_4016956 : Nat := 1375086130641393916584241

theorem tailTrace_4016956 : CollatzResearch.WordTrace tailWord_4016956 prefixEnd_4016956 1375086130641393916584241 := by
  unfold tailWord_4016956
  simp only [CollatzResearch.WordTrace]
  refine ⟨73255210817630964155679361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97673614423507952207572481 73255210817630964155679361)
  ·
    refine ⟨54941408113223223116759521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73255210817630964155679361 54941408113223223116759521)
    ·
      refine ⟨41206056084917417337569641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54941408113223223116759521 41206056084917417337569641)
      ·
        refine ⟨30904542063688063003177231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41206056084917417337569641 30904542063688063003177231)
        ·
          refine ⟨46356813095532094504765847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30904542063688063003177231 46356813095532094504765847)
          ·
            refine ⟨69535219643298141757148771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46356813095532094504765847 69535219643298141757148771)
            ·
              refine ⟨104302829464947212635723157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69535219643298141757148771 104302829464947212635723157)
              ·
                refine ⟨4889195131169400592299523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104302829464947212635723157 4889195131169400592299523)
                ·
                  refine ⟨7333792696754100888449285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889195131169400592299523 7333792696754100888449285)
                  ·
                    refine ⟨1375086130641393916584241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333792696754100888449285 1375086130641393916584241)
                    ·
                      rfl

theorem cell22_4016956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_4016956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016956 prefixEnd_4016956 := by exact prefixLift 4016956
  have htrace : WordTrace (prefixWord ++ tailWord_4016956) baseStart_4016956 baseEnd_4016956 := by
    simpa [prefixWord, tailWord_4016956, baseEnd_4016956] using wordTrace_append hprefix tailTrace_4016956
  have hstable : (prefixWord ++ tailWord_4016956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016956).length < 2 ^ (prefixWord ++ tailWord_4016956).sum := by decide
  have hdescent : baseEnd_4016956 < baseStart_4016956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016964 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4016964 : Nat := 118140960795 + 4016964 * 2 ^ 59
def prefixEnd_4016964 : Nat := 4983230072969 + 3 ^ 40 * 4016964 * 2
def baseEnd_4016964 : Nat := 1375088869204884562384217

theorem tailTrace_4016964 : CollatzResearch.WordTrace tailWord_4016964 prefixEnd_4016964 1375088869204884562384217 := by
  unfold tailWord_4016964
  simp only [CollatzResearch.WordTrace]
  refine ⟨73255356709616472838824973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97673808946155297118433297 73255356709616472838824973)
  ·
    refine ⟨27470758766106177314559365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73255356709616472838824973 27470758766106177314559365)
    ·
      refine ⟨5150767268644908246479881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27470758766106177314559365 5150767268644908246479881)
      ·
        refine ⟨3863075451483681184859911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5150767268644908246479881 3863075451483681184859911)
        ·
          refine ⟨5794613177225521777289867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863075451483681184859911 5794613177225521777289867)
          ·
            refine ⟨8691919765838282665934801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794613177225521777289867 8691919765838282665934801)
            ·
              refine ⟨6518939824378711999451101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691919765838282665934801 6518939824378711999451101)
              ·
                refine ⟨2444602434142016999794163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6518939824378711999451101 2444602434142016999794163)
                ·
                  refine ⟨3666903651213025499691245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444602434142016999794163 3666903651213025499691245)
                  ·
                    refine ⟨1375088869204884562384217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666903651213025499691245 1375088869204884562384217)
                    ·
                      rfl

theorem cell22_4016964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4016964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016964 prefixEnd_4016964 := by exact prefixLift 4016964
  have htrace : WordTrace (prefixWord ++ tailWord_4016964) baseStart_4016964 baseEnd_4016964 := by
    simpa [prefixWord, tailWord_4016964, baseEnd_4016964] using wordTrace_append hprefix tailTrace_4016964
  have hstable : (prefixWord ++ tailWord_4016964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016964).length < 2 ^ (prefixWord ++ tailWord_4016964).sum := by decide
  have hdescent : baseEnd_4016964 < baseStart_4016964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4016988 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_4016988 : Nat := 118140960795 + 4016988 * 2 ^ 59
def prefixEnd_4016988 : Nat := 4983230072969 + 3 ^ 40 * 4016988 * 2
def baseEnd_4016988 : Nat := 458365694965118833261381

theorem tailTrace_4016988 : CollatzResearch.WordTrace tailWord_4016988 prefixEnd_4016988 458365694965118833261381 := by
  unfold tailWord_4016988
  simp only [CollatzResearch.WordTrace]
  refine ⟨73255794385572998888261809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97674392514097331851015745 73255794385572998888261809)
  ·
    refine ⟨54941845789179749166196357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73255794385572998888261809 54941845789179749166196357)
    ·
      refine ⟨10301596085471202968661817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54941845789179749166196357 10301596085471202968661817)
      ·
        refine ⟨7726197064103402226496363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10301596085471202968661817 7726197064103402226496363)
        ·
          refine ⟨11589295596155103339744545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726197064103402226496363 11589295596155103339744545)
          ·
            refine ⟨8691971697116327504808409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11589295596155103339744545 8691971697116327504808409)
            ·
              refine ⟨6518978772837245628606307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691971697116327504808409 6518978772837245628606307)
              ·
                refine ⟨9778468159255868442909461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518978772837245628606307 9778468159255868442909461)
                ·
                  refine ⟨458365694965118833261381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9778468159255868442909461 458365694965118833261381)
                  ·
                    rfl

theorem cell22_4016988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_4016988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4016988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4016988 prefixEnd_4016988 := by exact prefixLift 4016988
  have htrace : WordTrace (prefixWord ++ tailWord_4016988) baseStart_4016988 baseEnd_4016988 := by
    simpa [prefixWord, tailWord_4016988, baseEnd_4016988] using wordTrace_append hprefix tailTrace_4016988
  have hstable : (prefixWord ++ tailWord_4016988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4016988).length < 2 ^ (prefixWord ++ tailWord_4016988).sum := by decide
  have hdescent : baseEnd_4016988 < baseStart_4016988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4016988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017108 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_4017108 : Nat := 118140960795 + 4017108 * 2 ^ 59
def prefixEnd_4017108 : Nat := 4983230072969 + 3 ^ 40 * 4017108 * 2
def baseEnd_4017108 : Nat := 1375138163347716186783775

theorem tailTrace_4017108 : CollatzResearch.WordTrace tailWord_4017108 prefixEnd_4017108 1375138163347716186783775 := by
  unfold tailWord_4017108
  simp only [CollatzResearch.WordTrace]
  refine ⟨73257982765355629135445989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97677310353807505513927985 73257982765355629135445989)
  ·
    refine ⟨13735871768504180462896123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73257982765355629135445989 13735871768504180462896123)
    ·
      refine ⟨20603807652756270694344185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735871768504180462896123 20603807652756270694344185)
      ·
        refine ⟨15452855739567203020758139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20603807652756270694344185 15452855739567203020758139)
        ·
          refine ⟨23179283609350804531137209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452855739567203020758139 23179283609350804531137209)
          ·
            refine ⟨17384462707013103398352907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23179283609350804531137209 17384462707013103398352907)
            ·
              refine ⟨26076694060519655097529361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17384462707013103398352907 26076694060519655097529361)
              ·
                refine ⟨19557520545389741323147021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26076694060519655097529361 19557520545389741323147021)
                ·
                  refine ⟨7334070204521152996180133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19557520545389741323147021 7334070204521152996180133)
                  ·
                    refine ⟨1375138163347716186783775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334070204521152996180133 1375138163347716186783775)
                    ·
                      rfl

theorem cell22_4017108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_4017108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017108 prefixEnd_4017108 := by exact prefixLift 4017108
  have htrace : WordTrace (prefixWord ++ tailWord_4017108) baseStart_4017108 baseEnd_4017108 := by
    simpa [prefixWord, tailWord_4017108, baseEnd_4017108] using wordTrace_append hprefix tailTrace_4017108
  have hstable : (prefixWord ++ tailWord_4017108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017108).length < 2 ^ (prefixWord ++ tailWord_4017108).sum := by decide
  have hdescent : baseEnd_4017108 < baseStart_4017108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017110 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4017110 : Nat := 118140960795 + 4017110 * 2 ^ 59
def prefixEnd_4017110 : Nat := 4983230072969 + 3 ^ 40 * 4017110 * 2
def baseEnd_4017110 : Nat := 1375138847988588848233769

theorem tailTrace_4017110 : CollatzResearch.WordTrace tailWord_4017110 prefixEnd_4017110 1375138847988588848233769 := by
  unfold tailWord_4017110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9157252404794000788279049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97677358984469341741643189 9157252404794000788279049)
  ·
    refine ⟨6867939303595500591209287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9157252404794000788279049 6867939303595500591209287)
    ·
      refine ⟨10301908955393250886813931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867939303595500591209287 10301908955393250886813931)
      ·
        refine ⟨15452863433089876330220897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301908955393250886813931 15452863433089876330220897)
        ·
          refine ⟨11589647574817407247665673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15452863433089876330220897 11589647574817407247665673)
          ·
            refine ⟨8692235681113055435749255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11589647574817407247665673 8692235681113055435749255)
            ·
              refine ⟨13038353521669583153623883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692235681113055435749255 13038353521669583153623883)
              ·
                refine ⟨19557530282504374730435825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038353521669583153623883 19557530282504374730435825)
                ·
                  refine ⟨14668147711878281047826869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19557530282504374730435825 14668147711878281047826869)
                  ·
                    refine ⟨1375138847988588848233769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14668147711878281047826869 1375138847988588848233769)
                    ·
                      rfl

theorem cell22_4017110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4017110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017110 prefixEnd_4017110 := by exact prefixLift 4017110
  have htrace : WordTrace (prefixWord ++ tailWord_4017110) baseStart_4017110 baseEnd_4017110 := by
    simpa [prefixWord, tailWord_4017110, baseEnd_4017110] using wordTrace_append hprefix tailTrace_4017110
  have hstable : (prefixWord ++ tailWord_4017110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017110).length < 2 ^ (prefixWord ++ tailWord_4017110).sum := by decide
  have hdescent : baseEnd_4017110 < baseStart_4017110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017142 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_4017142 : Nat := 118140960795 + 4017142 * 2 ^ 59
def prefixEnd_4017142 : Nat := 4983230072969 + 3 ^ 40 * 4017142 * 2
def baseEnd_4017142 : Nat := 1375149802242551431433671

theorem tailTrace_4017142 : CollatzResearch.WordTrace tailWord_4017142 prefixEnd_4017142 1375149802242551431433671 := by
  unfold tailWord_4017142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9157325350786755129851855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97678137075058721385086453 9157325350786755129851855)
  ·
    refine ⟨13735988026180132694777783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9157325350786755129851855 13735988026180132694777783)
    ·
      refine ⟨20603982039270199042166675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735988026180132694777783 20603982039270199042166675)
      ·
        refine ⟨30905973058905298563250013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20603982039270199042166675 30905973058905298563250013)
        ·
          refine ⟨11589739897089486961218755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30905973058905298563250013 11589739897089486961218755)
          ·
            refine ⟨17384609845634230441828133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589739897089486961218755 17384609845634230441828133)
            ·
              refine ⟨3259614346056418207842775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17384609845634230441828133 3259614346056418207842775)
              ·
                refine ⟨4889421519084627311764163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259614346056418207842775 4889421519084627311764163)
                ·
                  refine ⟨7334132278626940967646245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889421519084627311764163 7334132278626940967646245)
                  ·
                    refine ⟨1375149802242551431433671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334132278626940967646245 1375149802242551431433671)
                    ·
                      rfl

theorem cell22_4017142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_4017142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017142 prefixEnd_4017142 := by exact prefixLift 4017142
  have htrace : WordTrace (prefixWord ++ tailWord_4017142) baseStart_4017142 baseEnd_4017142 := by
    simpa [prefixWord, tailWord_4017142, baseEnd_4017142] using wordTrace_append hprefix tailTrace_4017142
  have hstable : (prefixWord ++ tailWord_4017142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017142).length < 2 ^ (prefixWord ++ tailWord_4017142).sum := by decide
  have hdescent : baseEnd_4017142 < baseStart_4017142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017185 : List Nat := [1, 2, 3, 2, 3, 3, 2, 6]
def baseStart_4017185 : Nat := 118140960795 + 4017185 * 2 ^ 59
def prefixEnd_4017185 : Nat := 4983230072969 + 3 ^ 40 * 4017185 * 2
def baseEnd_4017185 : Nat := 152796058002368183623171

theorem tailTrace_4017185 : CollatzResearch.WordTrace tailWord_4017185 prefixEnd_4017185 152796058002368183623171 := by
  unfold tailWord_4017185
  simp only [CollatzResearch.WordTrace]
  refine ⟨146518773951432300421445009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97679182634288200280963339 146518773951432300421445009)
  ·
    refine ⟨109889080463574225316083757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146518773951432300421445009 109889080463574225316083757)
    ·
      refine ⟨41208405173840334493531409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109889080463574225316083757 41208405173840334493531409)
      ·
        refine ⟨30906303880380250870148557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41208405173840334493531409 30906303880380250870148557)
        ·
          refine ⟨11589863955142594076305709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30906303880380250870148557 11589863955142594076305709)
          ·
            refine ⟨4346198983178472778614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11589863955142594076305709 4346198983178472778614641)
            ·
              refine ⟨3259649237383854583960981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4346198983178472778614641 3259649237383854583960981)
              ·
                refine ⟨152796058002368183623171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3259649237383854583960981 152796058002368183623171)
                ·
                  rfl

theorem cell22_4017185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 6].length) (baseStart_4017185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017185 prefixEnd_4017185 := by exact prefixLift 4017185
  have htrace : WordTrace (prefixWord ++ tailWord_4017185) baseStart_4017185 baseEnd_4017185 := by
    simpa [prefixWord, tailWord_4017185, baseEnd_4017185] using wordTrace_append hprefix tailTrace_4017185
  have hstable : (prefixWord ++ tailWord_4017185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017185).length < 2 ^ (prefixWord ++ tailWord_4017185).sum := by decide
  have hdescent : baseEnd_4017185 < baseStart_4017185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017196 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_4017196 : Nat := 118140960795 + 4017196 * 2 ^ 59
def prefixEnd_4017196 : Nat := 4983230072969 + 3 ^ 40 * 4017196 * 2
def baseEnd_4017196 : Nat := 458389429182037763527835

theorem tailTrace_4017196 : CollatzResearch.WordTrace tailWord_4017196 prefixEnd_4017196 458389429182037763527835 := by
  unfold tailWord_4017196
  simp only [CollatzResearch.WordTrace]
  refine ⟨73259587577196224650047721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97679450102928299533396961 73259587577196224650047721)
  ·
    refine ⟨54944690682897168487535791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73259587577196224650047721 54944690682897168487535791)
    ·
      refine ⟨82417036024345752731303687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54944690682897168487535791 82417036024345752731303687)
      ·
        refine ⟨123625554036518629096955531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82417036024345752731303687 123625554036518629096955531)
        ·
          refine ⟨185438331054777943645433297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123625554036518629096955531 185438331054777943645433297)
          ·
            refine ⟨139078748291083457734074973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185438331054777943645433297 139078748291083457734074973)
            ·
              refine ⟨52154530609156296650278115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139078748291083457734074973 52154530609156296650278115)
              ·
                refine ⟨78231795913734444975417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52154530609156296650278115 78231795913734444975417173)
                ·
                  refine ⟨458389429182037763527835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78231795913734444975417173 458389429182037763527835)
                  ·
                    rfl

theorem cell22_4017196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_4017196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017196 prefixEnd_4017196 := by exact prefixLift 4017196
  have htrace : WordTrace (prefixWord ++ tailWord_4017196) baseStart_4017196 baseEnd_4017196 := by
    simpa [prefixWord, tailWord_4017196, baseEnd_4017196] using wordTrace_append hprefix tailTrace_4017196
  have hstable : (prefixWord ++ tailWord_4017196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017196).length < 2 ^ (prefixWord ++ tailWord_4017196).sum := by decide
  have hdescent : baseEnd_4017196 < baseStart_4017196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017213 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 7]
def baseStart_4017213 : Nat := 118140960795 + 4017213 * 2 ^ 59
def prefixEnd_4017213 : Nat := 4983230072969 + 3 ^ 40 * 4017213 * 2
def baseEnd_4017213 : Nat := 458391368997843637636151

theorem tailTrace_4017213 : CollatzResearch.WordTrace tailWord_4017213 prefixEnd_4017213 458391368997843637636151 := by
  unfold tailWord_4017213
  simp only [CollatzResearch.WordTrace]
  refine ⟨146519795195330861203464293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97679863463553907468976195 146519795195330861203464293)
  ·
    refine ⟨27472461599124536475649555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146519795195330861203464293 27472461599124536475649555)
    ·
      refine ⟨41208692398686804713474333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27472461599124536475649555 41208692398686804713474333)
      ·
        refine ⟨15453259649507551767552875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41208692398686804713474333 15453259649507551767552875)
        ·
          refine ⟨23179889474261327651329313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15453259649507551767552875 23179889474261327651329313)
          ·
            refine ⟨17384917105695995738496985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23179889474261327651329313 17384917105695995738496985)
            ·
              refine ⟨13038687829271996803872739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17384917105695995738496985 13038687829271996803872739)
              ·
                refine ⟨19558031743907995205809109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038687829271996803872739 19558031743907995205809109)
                ·
                  refine ⟨458391368997843637636151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19558031743907995205809109 458391368997843637636151)
                  ·
                    rfl

theorem cell22_4017213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_4017213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017213 prefixEnd_4017213 := by exact prefixLift 4017213
  have htrace : WordTrace (prefixWord ++ tailWord_4017213) baseStart_4017213 baseEnd_4017213 := by
    simpa [prefixWord, tailWord_4017213, baseEnd_4017213] using wordTrace_append hprefix tailTrace_4017213
  have hstable : (prefixWord ++ tailWord_4017213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017213).length < 2 ^ (prefixWord ++ tailWord_4017213).sum := by decide
  have hdescent : baseEnd_4017213 < baseStart_4017213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017290 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4017290 : Nat := 118140960795 + 4017290 * 2 ^ 59
def prefixEnd_4017290 : Nat := 4983230072969 + 3 ^ 40 * 4017290 * 2
def baseEnd_4017290 : Nat := 1375200465667128378733217

theorem tailTrace_4017290 : CollatzResearch.WordTrace tailWord_4017290 prefixEnd_4017290 1375200465667128378733217 := by
  unfold tailWord_4017290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630650904012975838504331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97681735744034602236011549 36630650904012975838504331)
  ·
    refine ⟨54945976356019463757756497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36630650904012975838504331 54945976356019463757756497)
    ·
      refine ⟨41209482267014597818317373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54945976356019463757756497 41209482267014597818317373)
      ·
        refine ⟨15453555850130474181869015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41209482267014597818317373 15453555850130474181869015)
        ·
          refine ⟨23180333775195711272803523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15453555850130474181869015 23180333775195711272803523)
          ·
            refine ⟨34770500662793566909205285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23180333775195711272803523 34770500662793566909205285)
            ·
              refine ⟨6519468874273793795475991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34770500662793566909205285 6519468874273793795475991)
              ·
                refine ⟨9779203311410690693213987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519468874273793795475991 9779203311410690693213987)
                ·
                  refine ⟨14668804967116036039820981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779203311410690693213987 14668804967116036039820981)
                  ·
                    refine ⟨1375200465667128378733217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14668804967116036039820981 1375200465667128378733217)
                    ·
                      rfl

theorem cell22_4017290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4017290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017290 prefixEnd_4017290 := by exact prefixLift 4017290
  have htrace : WordTrace (prefixWord ++ tailWord_4017290) baseStart_4017290 baseEnd_4017290 := by
    simpa [prefixWord, tailWord_4017290, baseEnd_4017290] using wordTrace_append hprefix tailTrace_4017290
  have hstable : (prefixWord ++ tailWord_4017290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017290).length < 2 ^ (prefixWord ++ tailWord_4017290).sum := by decide
  have hdescent : baseEnd_4017290 < baseStart_4017290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017311 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 1, 4]
def baseStart_4017311 : Nat := 118140960795 + 4017311 * 2 ^ 59
def prefixEnd_4017311 : Nat := 4983230072969 + 3 ^ 40 * 4017311 * 2
def baseEnd_4017311 : Nat := 1375207654396291323958153

theorem tailTrace_4017311 : CollatzResearch.WordTrace tailWord_4017311 prefixEnd_4017311 1375207654396291323958153 := by
  unfold tailWord_4017311
  simp only [CollatzResearch.WordTrace]
  refine ⟨146523369548975823940531787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97682246365983882627021191 146523369548975823940531787)
  ·
    refine ⟨219785054323463735910797681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146523369548975823940531787 219785054323463735910797681)
    ·
      refine ⟨164838790742597801933098261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219785054323463735910797681 164838790742597801933098261)
      ·
        refine ⟨7726818316059271965613981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164838790742597801933098261 7726818316059271965613981)
        ·
          refine ⟨2897556868522226987105243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7726818316059271965613981 2897556868522226987105243)
          ·
            refine ⟨4346335302783340480657865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897556868522226987105243 4346335302783340480657865)
            ·
              refine ⟨3259751477087505360493399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4346335302783340480657865 3259751477087505360493399)
              ·
                refine ⟨4889627215631258040740099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259751477087505360493399 4889627215631258040740099)
                ·
                  refine ⟨7334440823446887061110149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889627215631258040740099 7334440823446887061110149)
                  ·
                    refine ⟨1375207654396291323958153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334440823446887061110149 1375207654396291323958153)
                    ·
                      rfl

theorem cell22_4017311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_4017311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017311 prefixEnd_4017311 := by exact prefixLift 4017311
  have htrace : WordTrace (prefixWord ++ tailWord_4017311) baseStart_4017311 baseEnd_4017311 := by
    simpa [prefixWord, tailWord_4017311, baseEnd_4017311] using wordTrace_append hprefix tailTrace_4017311
  have hstable : (prefixWord ++ tailWord_4017311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017311).length < 2 ^ (prefixWord ++ tailWord_4017311).sum := by decide
  have hdescent : baseEnd_4017311 < baseStart_4017311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017365 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 7]
def baseStart_4017365 : Nat := 118140960795 + 4017365 * 2 ^ 59
def prefixEnd_4017365 : Nat := 4983230072969 + 3 ^ 40 * 4017365 * 2
def baseEnd_4017365 : Nat := 458408713233284394369329

theorem tailTrace_4017365 : CollatzResearch.WordTrace tailWord_4017365 prefixEnd_4017365 458408713233284394369329 := by
  unfold tailWord_4017365
  simp only [CollatzResearch.WordTrace]
  refine ⟨146525339090780191162997549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97683559393853460775331699 146525339090780191162997549)
  ·
    refine ⟨54947002159042571686124081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146525339090780191162997549 54947002159042571686124081)
    ·
      refine ⟨41210251619281928764593061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54947002159042571686124081 41210251619281928764593061)
      ·
        refine ⟨7726922178615361643361199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41210251619281928764593061 7726922178615361643361199)
        ·
          refine ⟨11590383267923042465041799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726922178615361643361199 11590383267923042465041799)
          ·
            refine ⟨17385574901884563697562699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11590383267923042465041799 17385574901884563697562699)
            ·
              refine ⟨26078362352826845546344049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17385574901884563697562699 26078362352826845546344049)
              ·
                refine ⟨19558771764620134159758037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26078362352826845546344049 19558771764620134159758037)
                ·
                  refine ⟨458408713233284394369329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19558771764620134159758037 458408713233284394369329)
                  ·
                    rfl

theorem cell22_4017365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_4017365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017365 prefixEnd_4017365 := by exact prefixLift 4017365
  have htrace : WordTrace (prefixWord ++ tailWord_4017365) baseStart_4017365 baseEnd_4017365 := by
    simpa [prefixWord, tailWord_4017365, baseEnd_4017365] using wordTrace_append hprefix tailTrace_4017365
  have hstable : (prefixWord ++ tailWord_4017365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017365).length < 2 ^ (prefixWord ++ tailWord_4017365).sum := by decide
  have hdescent : baseEnd_4017365 < baseStart_4017365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017386 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4017386 : Nat := 118140960795 + 4017386 * 2 ^ 59
def prefixEnd_4017386 : Nat := 4983230072969 + 3 ^ 40 * 4017386 * 2
def baseEnd_4017386 : Nat := 1375233328429016128332923

theorem tailTrace_4017386 : CollatzResearch.WordTrace tailWord_4017386 prefixEnd_4017386 1375233328429016128332923 := by
  unfold tailWord_4017386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631526255926027937378003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97684070015802741166341341 36631526255926027937378003)
  ·
    refine ⟨54947289383889041906067005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36631526255926027937378003 54947289383889041906067005)
    ·
      refine ⟨20605233518958390714775127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54947289383889041906067005 20605233518958390714775127)
      ·
        refine ⟨30907850278437586072162691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20605233518958390714775127 30907850278437586072162691)
        ·
          refine ⟨46361775417656379108244037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30907850278437586072162691 46361775417656379108244037)
          ·
            refine ⟨8692832890810571082795757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46361775417656379108244037 8692832890810571082795757)
            ·
              refine ⟨3259812334053964156048409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8692832890810571082795757 3259812334053964156048409)
              ·
                refine ⟨2444859250540473117036307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3259812334053964156048409 2444859250540473117036307)
                ·
                  refine ⟨3667288875810709675554461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444859250540473117036307 3667288875810709675554461)
                  ·
                    refine ⟨1375233328429016128332923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667288875810709675554461 1375233328429016128332923)
                    ·
                      rfl

theorem cell22_4017386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4017386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017386 prefixEnd_4017386 := by exact prefixLift 4017386
  have htrace : WordTrace (prefixWord ++ tailWord_4017386) baseStart_4017386 baseEnd_4017386 := by
    simpa [prefixWord, tailWord_4017386, baseEnd_4017386] using wordTrace_append hprefix tailTrace_4017386
  have hstable : (prefixWord ++ tailWord_4017386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017386).length < 2 ^ (prefixWord ++ tailWord_4017386).sum := by decide
  have hdescent : baseEnd_4017386 < baseStart_4017386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017412 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4017412 : Nat := 118140960795 + 4017412 * 2 ^ 59
def prefixEnd_4017412 : Nat := 4983230072969 + 3 ^ 40 * 4017412 * 2
def baseEnd_4017412 : Nat := 1375242228760360727182843

theorem tailTrace_4017412 : CollatzResearch.WordTrace tailWord_4017412 prefixEnd_4017412 1375242228760360727182843 := by
  unfold tailWord_4017412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73263526660804959094979245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97684702214406612126638993 73263526660804959094979245)
  ·
    refine ⟨27473822497801859660617217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73263526660804959094979245 27473822497801859660617217)
    ·
      refine ⟨20605366873351394745462913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27473822497801859660617217 20605366873351394745462913)
      ·
        refine ⟨15454025155013546059097185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20605366873351394745462913 15454025155013546059097185)
        ·
          refine ⟨11590518866260159544322889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15454025155013546059097185 11590518866260159544322889)
          ·
            refine ⟨8692889149695119658242167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590518866260159544322889 8692889149695119658242167)
            ·
              refine ⟨13039333724542679487363251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692889149695119658242167 13039333724542679487363251)
              ·
                refine ⟨19559000586814019231044877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039333724542679487363251 19559000586814019231044877)
                ·
                  refine ⟨7334625220055257211641829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19559000586814019231044877 7334625220055257211641829)
                  ·
                    refine ⟨1375242228760360727182843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334625220055257211641829 1375242228760360727182843)
                    ·
                      rfl

theorem cell22_4017412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4017412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017412 prefixEnd_4017412 := by exact prefixLift 4017412
  have htrace : WordTrace (prefixWord ++ tailWord_4017412) baseStart_4017412 baseEnd_4017412 := by
    simpa [prefixWord, tailWord_4017412, baseEnd_4017412] using wordTrace_append hprefix tailTrace_4017412
  have hstable : (prefixWord ++ tailWord_4017412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017412).length < 2 ^ (prefixWord ++ tailWord_4017412).sum := by decide
  have hdescent : baseEnd_4017412 < baseStart_4017412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017425 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_4017425 : Nat := 118140960795 + 4017425 * 2 ^ 59
def prefixEnd_4017425 : Nat := 4983230072969 + 3 ^ 40 * 4017425 * 2
def baseEnd_4017425 : Nat := 1375246678926033026607803

theorem tailTrace_4017425 : CollatzResearch.WordTrace tailWord_4017425 prefixEnd_4017425 1375246678926033026607803 := by
  unfold tailWord_4017425
  simp only [CollatzResearch.WordTrace]
  refine ⟨146527527470562821410181729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97685018313708547606787819 146527527470562821410181729)
  ·
    refine ⟨109895645602922116057636297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146527527470562821410181729 109895645602922116057636297)
    ·
      refine ⟨82421734202191587043227223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109895645602922116057636297 82421734202191587043227223)
      ·
        refine ⟨123632601303287380564840835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82421734202191587043227223 123632601303287380564840835)
        ·
          refine ⟨185448901954931070847261253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123632601303287380564840835 185448901954931070847261253)
          ·
            refine ⟨34771669116549575783861485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185448901954931070847261253 34771669116549575783861485)
            ·
              refine ⟨13039375918706090918948057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34771669116549575783861485 13039375918706090918948057)
              ·
                refine ⟨9779531939029568189211043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13039375918706090918948057 9779531939029568189211043)
                ·
                  refine ⟨14669297908544352283816565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779531939029568189211043 14669297908544352283816565)
                  ·
                    refine ⟨1375246678926033026607803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14669297908544352283816565 1375246678926033026607803)
                    ·
                      rfl

theorem cell22_4017425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_4017425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017425 prefixEnd_4017425 := by exact prefixLift 4017425
  have htrace : WordTrace (prefixWord ++ tailWord_4017425) baseStart_4017425 baseEnd_4017425 := by
    simpa [prefixWord, tailWord_4017425, baseEnd_4017425] using wordTrace_append hprefix tailTrace_4017425
  have hstable : (prefixWord ++ tailWord_4017425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017425).length < 2 ^ (prefixWord ++ tailWord_4017425).sum := by decide
  have hdescent : baseEnd_4017425 < baseStart_4017425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017504 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_4017504 : Nat := 118140960795 + 4017504 * 2 ^ 59
def prefixEnd_4017504 : Nat := 4983230072969 + 3 ^ 40 * 4017504 * 2
def baseEnd_4017504 : Nat := 1375273722240503153882561

theorem tailTrace_4017504 : CollatzResearch.WordTrace tailWord_4017504 prefixEnd_4017504 1375273722240503153882561 := by
  unfold tailWord_4017504
  simp only [CollatzResearch.WordTrace]
  refine ⟨73265204418638308951153783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97686939224851078601538377 73265204418638308951153783)
  ·
    refine ⟨109897806627957463426730675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73265204418638308951153783 109897806627957463426730675)
    ·
      refine ⟨164846709941936195140096013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109897806627957463426730675 164846709941936195140096013)
      ·
        refine ⟨61817516228226073177536005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164846709941936195140096013 61817516228226073177536005)
        ·
          refine ⟨11590784292792388720788001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61817516228226073177536005 11590784292792388720788001)
          ·
            refine ⟨8693088219594291540591001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590784292792388720788001 8693088219594291540591001)
            ·
              refine ⟨6519816164695718655443251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8693088219594291540591001 6519816164695718655443251)
              ·
                refine ⟨9779724247043577983164877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519816164695718655443251 9779724247043577983164877)
                ·
                  refine ⟨3667396592641341743686829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9779724247043577983164877 3667396592641341743686829)
                  ·
                    refine ⟨1375273722240503153882561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667396592641341743686829 1375273722240503153882561)
                    ·
                      rfl

theorem cell22_4017504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_4017504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017504 prefixEnd_4017504 := by exact prefixLift 4017504
  have htrace : WordTrace (prefixWord ++ tailWord_4017504) baseStart_4017504 baseEnd_4017504 := by
    simpa [prefixWord, tailWord_4017504, baseEnd_4017504] using wordTrace_append hprefix tailTrace_4017504
  have hstable : (prefixWord ++ tailWord_4017504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017504).length < 2 ^ (prefixWord ++ tailWord_4017504).sum := by decide
  have hdescent : baseEnd_4017504 < baseStart_4017504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017547 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 1, 4]
def baseStart_4017547 : Nat := 118140960795 + 4017547 * 2 ^ 59
def prefixEnd_4017547 : Nat := 4983230072969 + 3 ^ 40 * 4017547 * 2
def baseEnd_4017547 : Nat := 1375288442019265375057429

theorem tailTrace_4017547 : CollatzResearch.WordTrace tailWord_4017547 prefixEnd_4017547 1375288442019265375057429 := by
  unfold tailWord_4017547
  simp only [CollatzResearch.WordTrace]
  refine ⟨146531977176120836246122895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97687984784080557497415263 146531977176120836246122895)
  ·
    refine ⟨219797965764181254369184343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146531977176120836246122895 219797965764181254369184343)
    ·
      refine ⟨329696948646271881553776515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219797965764181254369184343 329696948646271881553776515)
      ·
        refine ⟨494545422969407822330664773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329696948646271881553776515 494545422969407822330664773)
        ·
          refine ⟨92727266806763966686999645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494545422969407822330664773 92727266806763966686999645)
          ·
            refine ⟨34772725052536487507624867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92727266806763966686999645 34772725052536487507624867)
            ·
              refine ⟨52159087578804731261437301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34772725052536487507624867 52159087578804731261437301)
              ·
                refine ⟨4889914460512943555759747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52159087578804731261437301 4889914460512943555759747)
                ·
                  refine ⟨7334871690769415333639621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889914460512943555759747 7334871690769415333639621)
                  ·
                    refine ⟨1375288442019265375057429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334871690769415333639621 1375288442019265375057429)
                    ·
                      rfl

theorem cell22_4017547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4].length) (baseStart_4017547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017547 prefixEnd_4017547 := by exact prefixLift 4017547
  have htrace : WordTrace (prefixWord ++ tailWord_4017547) baseStart_4017547 baseEnd_4017547 := by
    simpa [prefixWord, tailWord_4017547, baseEnd_4017547] using wordTrace_append hprefix tailTrace_4017547
  have hstable : (prefixWord ++ tailWord_4017547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017547).length < 2 ^ (prefixWord ++ tailWord_4017547).sum := by decide
  have hdescent : baseEnd_4017547 < baseStart_4017547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017581 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4017581 : Nat := 118140960795 + 4017581 * 2 ^ 59
def prefixEnd_4017581 : Nat := 4983230072969 + 3 ^ 40 * 4017581 * 2
def baseEnd_4017581 : Nat := 1375300080914100619707325

theorem tailTrace_4017581 : CollatzResearch.WordTrace tailWord_4017581 prefixEnd_4017581 1375300080914100619707325 := by
  unfold tailWord_4017581
  simp only [CollatzResearch.WordTrace]
  refine ⟨146533217257997660052860597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97688811505331773368573731 146533217257997660052860597)
  ·
    refine ⟨13737489117937280629955681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146533217257997660052860597 13737489117937280629955681)
    ·
      refine ⟨10303116838452960472466761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13737489117937280629955681 10303116838452960472466761)
      ·
        refine ⟨7727337628839720354350071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10303116838452960472466761 7727337628839720354350071)
        ·
          refine ⟨11591006443259580531525107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727337628839720354350071 11591006443259580531525107)
          ·
            refine ⟨17386509664889370797287661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591006443259580531525107 17386509664889370797287661)
            ·
              refine ⟨6519941124333514048982873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17386509664889370797287661 6519941124333514048982873)
              ·
                refine ⟨4889955843250135536737155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6519941124333514048982873 4889955843250135536737155)
                ·
                  refine ⟨7334933764875203305105733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889955843250135536737155 7334933764875203305105733)
                  ·
                    refine ⟨1375300080914100619707325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334933764875203305105733 1375300080914100619707325)
                    ·
                      rfl

theorem cell22_4017581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4017581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017581 prefixEnd_4017581 := by exact prefixLift 4017581
  have htrace : WordTrace (prefixWord ++ tailWord_4017581) baseStart_4017581 baseEnd_4017581 := by
    simpa [prefixWord, tailWord_4017581, baseEnd_4017581] using wordTrace_append hprefix tailTrace_4017581
  have hstable : (prefixWord ++ tailWord_4017581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017581).length < 2 ^ (prefixWord ++ tailWord_4017581).sum := by decide
  have hdescent : baseEnd_4017581 < baseStart_4017581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017592 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_4017592 : Nat := 118140960795 + 4017592 * 2 ^ 59
def prefixEnd_4017592 : Nat := 4983230072969 + 3 ^ 40 * 4017592 * 2
def baseEnd_4017592 : Nat := 1375303846438900257682291

theorem tailTrace_4017592 : CollatzResearch.WordTrace tailWord_4017592 prefixEnd_4017592 1375303846438900257682291 := by
  unfold tailWord_4017592
  simp only [CollatzResearch.WordTrace]
  refine ⟨73266809230478904465755515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97689078973971872621007353 73266809230478904465755515)
  ·
    refine ⟨109900213845718356698633273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73266809230478904465755515 109900213845718356698633273)
    ·
      refine ⟨82425160384288767523974955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109900213845718356698633273 82425160384288767523974955)
      ·
        refine ⟨123637740576433151285962433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82425160384288767523974955 123637740576433151285962433)
        ·
          refine ⟨92728305432324863464471825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123637740576433151285962433 92728305432324863464471825)
          ·
            refine ⟨69546229074243647598353869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92728305432324863464471825 69546229074243647598353869)
            ·
              refine ⟨26079835902841367849382701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69546229074243647598353869 26079835902841367849382701)
              ·
                refine ⟨9779938463565512943518513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26079835902841367849382701 9779938463565512943518513)
                ·
                  refine ⟨7334953847674134707638885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9779938463565512943518513 7334953847674134707638885)
                  ·
                    refine ⟨1375303846438900257682291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334953847674134707638885 1375303846438900257682291)
                    ·
                      rfl

theorem cell22_4017592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_4017592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017592 prefixEnd_4017592 := by exact prefixLift 4017592
  have htrace : WordTrace (prefixWord ++ tailWord_4017592) baseStart_4017592 baseEnd_4017592 := by
    simpa [prefixWord, tailWord_4017592, baseEnd_4017592] using wordTrace_append hprefix tailTrace_4017592
  have hstable : (prefixWord ++ tailWord_4017592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017592).length < 2 ^ (prefixWord ++ tailWord_4017592).sum := by decide
  have hdescent : baseEnd_4017592 < baseStart_4017592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017639 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4017639 : Nat := 118140960795 + 4017639 * 2 ^ 59
def prefixEnd_4017639 : Nat := 4983230072969 + 3 ^ 40 * 4017639 * 2
def baseEnd_4017639 : Nat := 1375319935499407801757147

theorem tailTrace_4017639 : CollatzResearch.WordTrace tailWord_4017639 prefixEnd_4017639 1375319935499407801757147 := by
  unfold tailWord_4017639
  simp only [CollatzResearch.WordTrace]
  refine ⟨146535332691787535958471971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97690221794525023972314647 146535332691787535958471971)
  ·
    refine ⟨219802999037681303937707957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146535332691787535958471971 219802999037681303937707957)
    ·
      refine ⟨20606531159782622244160121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219802999037681303937707957 20606531159782622244160121)
      ·
        refine ⟨15454898369836966683120091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20606531159782622244160121 15454898369836966683120091)
        ·
          refine ⟨23182347554755450024680137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454898369836966683120091 23182347554755450024680137)
          ·
            refine ⟨17386760666066587518510103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23182347554755450024680137 17386760666066587518510103)
            ·
              refine ⟨26080140999099881277765155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386760666066587518510103 26080140999099881277765155)
              ·
                refine ⟨39120211498649821916647733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26080140999099881277765155 39120211498649821916647733)
                ·
                  refine ⟨3667519827998420804685725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39120211498649821916647733 3667519827998420804685725)
                  ·
                    refine ⟨1375319935499407801757147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667519827998420804685725 1375319935499407801757147)
                    ·
                      rfl

theorem cell22_4017639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4017639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017639 prefixEnd_4017639 := by exact prefixLift 4017639
  have htrace : WordTrace (prefixWord ++ tailWord_4017639) baseStart_4017639 baseEnd_4017639 := by
    simpa [prefixWord, tailWord_4017639, baseEnd_4017639] using wordTrace_append hprefix tailTrace_4017639
  have hstable : (prefixWord ++ tailWord_4017639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017639).length < 2 ^ (prefixWord ++ tailWord_4017639).sum := by decide
  have hdescent : baseEnd_4017639 < baseStart_4017639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017656 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 1, 3]
def baseStart_4017656 : Nat := 118140960795 + 4017656 * 2 ^ 59
def prefixEnd_4017656 : Nat := 4983230072969 + 3 ^ 40 * 4017656 * 2
def baseEnd_4017656 : Nat := 1375325754946825424082095

theorem tailTrace_4017656 : CollatzResearch.WordTrace tailWord_4017656 prefixEnd_4017656 1375325754946825424082095 := by
  unfold tailWord_4017656
  simp only [CollatzResearch.WordTrace]
  refine ⟨73267976366362973930920411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97690635155150631907893881 73267976366362973930920411)
  ·
    refine ⟨109901964549544460896380617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73267976366362973930920411 109901964549544460896380617)
    ·
      refine ⟨82426473412158345672285463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109901964549544460896380617 82426473412158345672285463)
      ·
        refine ⟨123639710118237518508428195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82426473412158345672285463 123639710118237518508428195)
        ·
          refine ⟨185459565177356277762642293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123639710118237518508428195 185459565177356277762642293)
          ·
            refine ⟨17386834235377151040247715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185459565177356277762642293 17386834235377151040247715)
            ·
              refine ⟨26080251353065726560371573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386834235377151040247715 26080251353065726560371573)
              ·
                refine ⟨2445023564349911865034835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26080251353065726560371573 2445023564349911865034835)
                ·
                  refine ⟨3667535346524867797552253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445023564349911865034835 3667535346524867797552253)
                  ·
                    refine ⟨1375325754946825424082095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667535346524867797552253 1375325754946825424082095)
                    ·
                      rfl

theorem cell22_4017656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_4017656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017656 prefixEnd_4017656 := by exact prefixLift 4017656
  have htrace : WordTrace (prefixWord ++ tailWord_4017656) baseStart_4017656 baseEnd_4017656 := by
    simpa [prefixWord, tailWord_4017656, baseEnd_4017656] using wordTrace_append hprefix tailTrace_4017656
  have hstable : (prefixWord ++ tailWord_4017656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017656).length < 2 ^ (prefixWord ++ tailWord_4017656).sum := by decide
  have hdescent : baseEnd_4017656 < baseStart_4017656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017662 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4017662 : Nat := 118140960795 + 4017662 * 2 ^ 59
def prefixEnd_4017662 : Nat := 4983230072969 + 3 ^ 40 * 4017662 * 2
def baseEnd_4017662 : Nat := 1375327808869443408432077

theorem tailTrace_4017662 : CollatzResearch.WordTrace tailWord_4017662 prefixEnd_4017662 1375327808869443408432077 := by
  unfold tailWord_4017662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317021446338026360819905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97690781047136140591039493 18317021446338026360819905)
  ·
    refine ⟨13737766084753519770614929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18317021446338026360819905 13737766084753519770614929)
    ·
      refine ⟨10303324563565139827961197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13737766084753519770614929 10303324563565139827961197)
      ·
        refine ⟨3863746711336927435485449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10303324563565139827961197 3863746711336927435485449)
        ·
          refine ⟨2897810033502695576614087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3863746711336927435485449 2897810033502695576614087)
          ·
            refine ⟨4346715050254043364921131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897810033502695576614087 4346715050254043364921131)
            ·
              refine ⟨6520072575381065047381697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4346715050254043364921131 6520072575381065047381697)
              ·
                refine ⟨4890054431535798785536273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6520072575381065047381697 4890054431535798785536273)
                ·
                  refine ⟨3667540823651849089152205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4890054431535798785536273 3667540823651849089152205)
                  ·
                    refine ⟨1375327808869443408432077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667540823651849089152205 1375327808869443408432077)
                    ·
                      rfl

theorem cell22_4017662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4017662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017662 prefixEnd_4017662 := by exact prefixLift 4017662
  have htrace : WordTrace (prefixWord ++ tailWord_4017662) baseStart_4017662 baseEnd_4017662 := by
    simpa [prefixWord, tailWord_4017662, baseEnd_4017662] using wordTrace_append hprefix tailTrace_4017662
  have hstable : (prefixWord ++ tailWord_4017662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017662).length < 2 ^ (prefixWord ++ tailWord_4017662).sum := by decide
  have hdescent : baseEnd_4017662 < baseStart_4017662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017712 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_4017712 : Nat := 118140960795 + 4017712 * 2 ^ 59
def prefixEnd_4017712 : Nat := 4983230072969 + 3 ^ 40 * 4017712 * 2
def baseEnd_4017712 : Nat := 1375344924891259944681923

theorem tailTrace_4017712 : CollatzResearch.WordTrace tailWord_4017712 prefixEnd_4017712 1375344924891259944681923 := by
  unfold tailWord_4017712
  simp only [CollatzResearch.WordTrace]
  refine ⟨73268997610261534712939695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97691996813682046283919593 73268997610261534712939695)
  ·
    refine ⟨109903496415392302069409543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73268997610261534712939695 109903496415392302069409543)
    ·
      refine ⟨164855244623088453104114315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109903496415392302069409543 164855244623088453104114315)
      ·
        refine ⟨247282866934632679656171473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164855244623088453104114315 247282866934632679656171473)
        ·
          refine ⟨185462150200974509742128605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247282866934632679656171473 185462150200974509742128605)
          ·
            refine ⟨69548306325365441153298227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185462150200974509742128605 69548306325365441153298227)
            ·
              refine ⟨104322459488048161729947341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69548306325365441153298227 104322459488048161729947341)
              ·
                refine ⟨39120922308018060648730253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104322459488048161729947341 39120922308018060648730253)
                ·
                  refine ⟨14670345865506772743273845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39120922308018060648730253 14670345865506772743273845)
                  ·
                    refine ⟨1375344924891259944681923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14670345865506772743273845 1375344924891259944681923)
                    ·
                      rfl

theorem cell22_4017712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_4017712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017712 prefixEnd_4017712 := by exact prefixLift 4017712
  have htrace : WordTrace (prefixWord ++ tailWord_4017712) baseStart_4017712 baseEnd_4017712 := by
    simpa [prefixWord, tailWord_4017712, baseEnd_4017712] using wordTrace_append hprefix tailTrace_4017712
  have hstable : (prefixWord ++ tailWord_4017712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017712).length < 2 ^ (prefixWord ++ tailWord_4017712).sum := by decide
  have hdescent : baseEnd_4017712 < baseStart_4017712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017750 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4017750 : Nat := 118140960795 + 4017750 * 2 ^ 59
def prefixEnd_4017750 : Nat := 4983230072969 + 3 ^ 40 * 4017750 * 2
def baseEnd_4017750 : Nat := 1375357933067840512231807

theorem tailTrace_4017750 : CollatzResearch.WordTrace tailWord_4017750 prefixEnd_4017750 1375357933067840512231807 := by
  unfold tailWord_4017750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9158711324649087619735169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97692920796256934610508469 9158711324649087619735169)
  ·
    refine ⟨6869033493486815714801377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9158711324649087619735169 6869033493486815714801377)
    ·
      refine ⟨5151775120115111786101033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6869033493486815714801377 5151775120115111786101033)
      ·
        refine ⟨3863831340086333839575775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5151775120115111786101033 3863831340086333839575775)
        ·
          refine ⟨5795747010129500759363663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863831340086333839575775 5795747010129500759363663)
          ·
            refine ⟨8693620515194251139045495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795747010129500759363663 8693620515194251139045495)
            ·
              refine ⟨13040430772791376708568243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693620515194251139045495 13040430772791376708568243)
              ·
                refine ⟨19560646159187065062852365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13040430772791376708568243 19560646159187065062852365)
                ·
                  refine ⟨7335242309695149398569637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19560646159187065062852365 7335242309695149398569637)
                  ·
                    refine ⟨1375357933067840512231807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7335242309695149398569637 1375357933067840512231807)
                    ·
                      rfl

theorem cell22_4017750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4017750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017750 prefixEnd_4017750 := by exact prefixLift 4017750
  have htrace : WordTrace (prefixWord ++ tailWord_4017750) baseStart_4017750 baseEnd_4017750 := by
    simpa [prefixWord, tailWord_4017750, baseEnd_4017750] using wordTrace_append hprefix tailTrace_4017750
  have hstable : (prefixWord ++ tailWord_4017750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017750).length < 2 ^ (prefixWord ++ tailWord_4017750).sum := by decide
  have hdescent : baseEnd_4017750 < baseStart_4017750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017789 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4017789 : Nat := 118140960795 + 4017789 * 2 ^ 59
def prefixEnd_4017789 : Nat := 4983230072969 + 3 ^ 40 * 4017789 * 2
def baseEnd_4017789 : Nat := 1375371283564857410506687

theorem tailTrace_4017789 : CollatzResearch.WordTrace tailWord_4017789 prefixEnd_4017789 1375371283564857410506687 := by
  unfold tailWord_4017789
  simp only [CollatzResearch.WordTrace]
  refine ⟨146540803641244111576432421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97693869094162741050954947 146540803641244111576432421)
  ·
    refine ⟨27476400682733270920581079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146540803641244111576432421 27476400682733270920581079)
    ·
      refine ⟨41214601024099906380871619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27476400682733270920581079 41214601024099906380871619)
      ·
        refine ⟨61821901536149859571307429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41214601024099906380871619 61821901536149859571307429)
        ·
          refine ⟨11591606538028098669620143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61821901536149859571307429 11591606538028098669620143)
          ·
            refine ⟨17387409807042148004430215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591606538028098669620143 17387409807042148004430215)
            ·
              refine ⟨26081114710563222006645323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387409807042148004430215 26081114710563222006645323)
              ·
                refine ⟨39121672065844833009967985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26081114710563222006645323 39121672065844833009967985)
                ·
                  refine ⟨29341254049383624757475989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39121672065844833009967985 29341254049383624757475989)
                  ·
                    refine ⟨1375371283564857410506687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29341254049383624757475989 1375371283564857410506687)
                    ·
                      rfl

theorem cell22_4017789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4017789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017789 prefixEnd_4017789 := by exact prefixLift 4017789
  have htrace : WordTrace (prefixWord ++ tailWord_4017789) baseStart_4017789 baseEnd_4017789 := by
    simpa [prefixWord, tailWord_4017789, baseEnd_4017789] using wordTrace_append hprefix tailTrace_4017789
  have hstable : (prefixWord ++ tailWord_4017789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017789).length < 2 ^ (prefixWord ++ tailWord_4017789).sum := by decide
  have hdescent : baseEnd_4017789 < baseStart_4017789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017804 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_4017804 : Nat := 118140960795 + 4017804 * 2 ^ 59
def prefixEnd_4017804 : Nat := 4983230072969 + 3 ^ 40 * 4017804 * 2
def baseEnd_4017804 : Nat := 458458806123800790460547

theorem tailTrace_4017804 : CollatzResearch.WordTrace tailWord_4017804 prefixEnd_4017804 458458806123800790460547 := by
  unfold tailWord_4017804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73270675368094884569114233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97694233824126512758818977 73270675368094884569114233)
  ·
    refine ⟨54953006526071163426835675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73270675368094884569114233 54953006526071163426835675)
    ·
      refine ⟨82429509789106745140253513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54953006526071163426835675 82429509789106745140253513)
      ·
        refine ⟨61822132341830058855190135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82429509789106745140253513 61822132341830058855190135)
        ·
          refine ⟨92733198512745088282785203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61822132341830058855190135 92733198512745088282785203)
          ·
            refine ⟨139099797769117632424177805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92733198512745088282785203 139099797769117632424177805)
            ·
              refine ⟨52162424163419112159066677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139099797769117632424177805 52162424163419112159066677)
              ·
                refine ⟨4890227265320541764912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52162424163419112159066677 4890227265320541764912501)
                ·
                  refine ⟨458458806123800790460547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4890227265320541764912501 458458806123800790460547)
                  ·
                    rfl

theorem cell22_4017804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_4017804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017804 prefixEnd_4017804 := by exact prefixLift 4017804
  have htrace : WordTrace (prefixWord ++ tailWord_4017804) baseStart_4017804 baseEnd_4017804 := by
    simpa [prefixWord, tailWord_4017804, baseEnd_4017804] using wordTrace_append hprefix tailTrace_4017804
  have hstable : (prefixWord ++ tailWord_4017804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017804).length < 2 ^ (prefixWord ++ tailWord_4017804).sum := by decide
  have hdescent : baseEnd_4017804 < baseStart_4017804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017825 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 1, 3]
def baseStart_4017825 : Nat := 118140960795 + 4017825 * 2 ^ 59
def prefixEnd_4017825 : Nat := 4983230072969 + 3 ^ 40 * 4017825 * 2
def baseEnd_4017825 : Nat := 1375383607100565316606577

theorem tailTrace_4017825 : CollatzResearch.WordTrace tailWord_4017825 prefixEnd_4017825 1375383607100565316606577 := by
  unfold tailWord_4017825
  simp only [CollatzResearch.WordTrace]
  refine ⟨146542116669113689724742929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97694744446075793149828619 146542116669113689724742929)
  ·
    refine ⟨109906587501835267293557197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146542116669113689724742929 109906587501835267293557197)
    ·
      refine ⟨41214970313188225235083949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109906587501835267293557197 41214970313188225235083949)
      ·
        refine ⟨15455613867445584463156481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41214970313188225235083949 15455613867445584463156481)
        ·
          refine ⟨11591710400584188347367361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15455613867445584463156481 11591710400584188347367361)
          ·
            refine ⟨8693782800438141260525521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11591710400584188347367361 8693782800438141260525521)
            ·
              refine ⟨6520337100328605945394141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8693782800438141260525521 6520337100328605945394141)
              ·
                refine ⟨2445126412623227229522803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6520337100328605945394141 2445126412623227229522803)
                ·
                  refine ⟨3667689618934840844284205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445126412623227229522803 3667689618934840844284205)
                  ·
                    refine ⟨1375383607100565316606577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667689618934840844284205 1375383607100565316606577)
                    ·
                      rfl

theorem cell22_4017825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_4017825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017825 prefixEnd_4017825 := by exact prefixLift 4017825
  have htrace : WordTrace (prefixWord ++ tailWord_4017825) baseStart_4017825 baseEnd_4017825 := by
    simpa [prefixWord, tailWord_4017825, baseEnd_4017825] using wordTrace_append hprefix tailTrace_4017825
  have hstable : (prefixWord ++ tailWord_4017825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017825).length < 2 ^ (prefixWord ++ tailWord_4017825).sum := by decide
  have hdescent : baseEnd_4017825 < baseStart_4017825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017838 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_4017838 : Nat := 118140960795 + 4017838 * 2 ^ 59
def prefixEnd_4017838 : Nat := 4983230072969 + 3 ^ 40 * 4017838 * 2
def baseEnd_4017838 : Nat := 458462685755412538677179

theorem tailTrace_4017838 : CollatzResearch.WordTrace tailWord_4017838 prefixEnd_4017838 458462685755412538677179 := by
  unfold tailWord_4017838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317823852258324118120771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97695060545377728629977445 18317823852258324118120771)
  ·
    refine ⟨27476735778387486177181157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18317823852258324118120771 27476735778387486177181157)
    ·
      refine ⟨5151887958447653658221467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27476735778387486177181157 5151887958447653658221467)
      ·
        refine ⟨7727831937671480487332201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151887958447653658221467 7727831937671480487332201)
        ·
          refine ⟨5795873953253610365499151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7727831937671480487332201 5795873953253610365499151)
          ·
            refine ⟨8693810929880415548248727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795873953253610365499151 8693810929880415548248727)
            ·
              refine ⟨13040716394820623322373091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693810929880415548248727 13040716394820623322373091)
              ·
                refine ⟨19561074592230934983559637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13040716394820623322373091 19561074592230934983559637)
                ·
                  refine ⟨458462685755412538677179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19561074592230934983559637 458462685755412538677179)
                  ·
                    rfl

theorem cell22_4017838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_4017838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017838 prefixEnd_4017838 := by exact prefixLift 4017838
  have htrace : WordTrace (prefixWord ++ tailWord_4017838) baseStart_4017838 baseEnd_4017838 := by
    simpa [prefixWord, tailWord_4017838, baseEnd_4017838] using wordTrace_append hprefix tailTrace_4017838
  have hstable : (prefixWord ++ tailWord_4017838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017838).length < 2 ^ (prefixWord ++ tailWord_4017838).sum := by decide
  have hdescent : baseEnd_4017838 < baseStart_4017838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017849 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 6]
def baseStart_4017849 : Nat := 118140960795 + 4017849 * 2 ^ 59
def prefixEnd_4017849 : Nat := 4983230072969 + 3 ^ 40 * 4017849 * 2
def baseEnd_4017849 : Nat := 458463940930345751335501

theorem tailTrace_4017849 : CollatzResearch.WordTrace tailWord_4017849 prefixEnd_4017849 458463940930345751335501 := by
  unfold tailWord_4017849
  simp only [CollatzResearch.WordTrace]
  refine ⟨146542992021026741823616601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97695328014017827882411067 146542992021026741823616601)
  ·
    refine ⟨109907244015770056367712451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146542992021026741823616601 109907244015770056367712451)
    ·
      refine ⟨164860866023655084551568677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109907244015770056367712451 164860866023655084551568677)
      ·
        refine ⟨30911412379435328353419127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164860866023655084551568677 30911412379435328353419127)
        ·
          refine ⟨46367118569152992530128691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30911412379435328353419127 46367118569152992530128691)
          ·
            refine ⟨69550677853729488795193037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46367118569152992530128691 69550677853729488795193037)
            ·
              refine ⟨26081504195148558298197389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69550677853729488795193037 26081504195148558298197389)
              ·
                refine ⟨9780564073180709361824021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26081504195148558298197389 9780564073180709361824021)
                ·
                  refine ⟨458463940930345751335501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9780564073180709361824021 458463940930345751335501)
                  ·
                    rfl

theorem cell22_4017849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_4017849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017849 prefixEnd_4017849 := by exact prefixLift 4017849
  have htrace : WordTrace (prefixWord ++ tailWord_4017849) baseStart_4017849 baseEnd_4017849 := by
    simpa [prefixWord, tailWord_4017849, baseEnd_4017849] using wordTrace_append hprefix tailTrace_4017849
  have hstable : (prefixWord ++ tailWord_4017849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017849).length < 2 ^ (prefixWord ++ tailWord_4017849).sum := by decide
  have hdescent : baseEnd_4017849 < baseStart_4017849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017879 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_4017879 : Nat := 118140960795 + 4017879 * 2 ^ 59
def prefixEnd_4017879 : Nat := 4983230072969 + 3 ^ 40 * 4017879 * 2
def baseEnd_4017879 : Nat := 1375402092404127175756411

theorem tailTrace_4017879 : CollatzResearch.WordTrace tailWord_4017879 prefixEnd_4017879 1375402092404127175756411 := by
  unfold tailWord_4017879
  simp only [CollatzResearch.WordTrace]
  refine ⟨146544086210918056947208691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97696057473945371298139127 146544086210918056947208691)
  ·
    refine ⟨219816129316377085420813037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146544086210918056947208691 219816129316377085420813037)
    ·
      refine ⟨82431048493641407032804889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219816129316377085420813037 82431048493641407032804889)
      ·
        refine ⟨61823286370231055274603667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82431048493641407032804889 61823286370231055274603667)
        ·
          refine ⟨92734929555346582911905501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61823286370231055274603667 92734929555346582911905501)
          ·
            refine ⟨34775598583254968591964563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92734929555346582911905501 34775598583254968591964563)
            ·
              refine ⟨52163397874882452887946845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34775598583254968591964563 52163397874882452887946845)
              ·
                refine ⟨19561274203080919832980067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52163397874882452887946845 19561274203080919832980067)
                ·
                  refine ⟨29341911304621379749470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561274203080919832980067 29341911304621379749470101)
                  ·
                    refine ⟨1375402092404127175756411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29341911304621379749470101 1375402092404127175756411)
                    ·
                      rfl

theorem cell22_4017879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_4017879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017879 prefixEnd_4017879 := by exact prefixLift 4017879
  have htrace : WordTrace (prefixWord ++ tailWord_4017879) baseStart_4017879 baseEnd_4017879 := by
    simpa [prefixWord, tailWord_4017879, baseEnd_4017879] using wordTrace_append hprefix tailTrace_4017879
  have hstable : (prefixWord ++ tailWord_4017879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017879).length < 2 ^ (prefixWord ++ tailWord_4017879).sum := by decide
  have hdescent : baseEnd_4017879 < baseStart_4017879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017881 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_4017881 : Nat := 118140960795 + 4017881 * 2 ^ 59
def prefixEnd_4017881 : Nat := 4983230072969 + 3 ^ 40 * 4017881 * 2
def baseEnd_4017881 : Nat := 1375402777044999837206405

theorem tailTrace_4017881 : CollatzResearch.WordTrace tailWord_4017881 prefixEnd_4017881 1375402777044999837206405 := by
  unfold tailWord_4017881
  simp only [CollatzResearch.WordTrace]
  refine ⟨146544159156910811288781497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97696106104607207525854331 146544159156910811288781497)
  ·
    refine ⟨109908119367683108466586123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146544159156910811288781497 109908119367683108466586123)
    ·
      refine ⟨164862179051524662699879185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109908119367683108466586123 164862179051524662699879185)
      ·
        refine ⟨123646634288643497024909389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164862179051524662699879185 123646634288643497024909389)
        ·
          refine ⟨46367487858241311384341021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123646634288643497024909389 46367487858241311384341021)
          ·
            refine ⟨17387807946840491769127883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46367487858241311384341021 17387807946840491769127883)
            ·
              refine ⟨26081711920260737653691825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387807946840491769127883 26081711920260737653691825)
              ·
                refine ⟨19561283940195553240268869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26081711920260737653691825 19561283940195553240268869)
                ·
                  refine ⟨3667740738786666232550413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19561283940195553240268869 3667740738786666232550413)
                  ·
                    refine ⟨1375402777044999837206405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3667740738786666232550413 1375402777044999837206405)
                    ·
                      rfl

theorem cell22_4017881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_4017881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017881 prefixEnd_4017881 := by exact prefixLift 4017881
  have htrace : WordTrace (prefixWord ++ tailWord_4017881) baseStart_4017881 baseEnd_4017881 := by
    simpa [prefixWord, tailWord_4017881, baseEnd_4017881] using wordTrace_append hprefix tailTrace_4017881
  have hstable : (prefixWord ++ tailWord_4017881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017881).length < 2 ^ (prefixWord ++ tailWord_4017881).sum := by decide
  have hdescent : baseEnd_4017881 < baseStart_4017881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017896 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4017896 : Nat := 118140960795 + 4017896 * 2 ^ 59
def prefixEnd_4017896 : Nat := 4983230072969 + 3 ^ 40 * 4017896 * 2
def baseEnd_4017896 : Nat := 1375407911851544798081359

theorem tailTrace_4017896 : CollatzResearch.WordTrace tailWord_4017896 prefixEnd_4017896 1375407911851544798081359 := by
  unfold tailWord_4017896
  simp only [CollatzResearch.WordTrace]
  refine ⟨73272353125928234425288771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97696470834570979233718361 73272353125928234425288771)
  ·
    refine ⟨109908529688892351637933157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73272353125928234425288771 109908529688892351637933157)
    ·
      refine ⟨20607849316667315932112467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109908529688892351637933157 20607849316667315932112467)
      ·
        refine ⟨30911773975000973898168701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20607849316667315932112467 30911773975000973898168701)
        ·
          refine ⟨11591915240625365211813263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30911773975000973898168701 11591915240625365211813263)
          ·
            refine ⟨17387872860938047817719895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591915240625365211813263 17387872860938047817719895)
            ·
              refine ⟨26081809291407071726579843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387872860938047817719895 26081809291407071726579843)
              ·
                refine ⟨39122713937110607589869765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26081809291407071726579843 39122713937110607589869765)
                ·
                  refine ⟨7335508863208238923100581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39122713937110607589869765 7335508863208238923100581)
                  ·
                    refine ⟨1375407911851544798081359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7335508863208238923100581 1375407911851544798081359)
                    ·
                      rfl

theorem cell22_4017896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4017896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017896 prefixEnd_4017896 := by exact prefixLift 4017896
  have htrace : WordTrace (prefixWord ++ tailWord_4017896) baseStart_4017896 baseEnd_4017896 := by
    simpa [prefixWord, tailWord_4017896, baseEnd_4017896] using wordTrace_append hprefix tailTrace_4017896
  have hstable : (prefixWord ++ tailWord_4017896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017896).length < 2 ^ (prefixWord ++ tailWord_4017896).sum := by decide
  have hdescent : baseEnd_4017896 < baseStart_4017896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4017939 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 7]
def baseStart_4017939 : Nat := 118140960795 + 4017939 * 2 ^ 59
def prefixEnd_4017939 : Nat := 4983230072969 + 3 ^ 40 * 4017939 * 2
def baseEnd_4017939 : Nat := 458474210543435673085409

theorem tailTrace_4017939 : CollatzResearch.WordTrace tailWord_4017939 prefixEnd_4017939 458474210543435673085409 := by
  unfold tailWord_4017939
  simp only [CollatzResearch.WordTrace]
  refine ⟨146546274590700687194392871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97697516393800458129595247 146546274590700687194392871)
  ·
    refine ⟨219819411886051030791589307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146546274590700687194392871 219819411886051030791589307)
    ·
      refine ⟨329729117829076546187383961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219819411886051030791589307 329729117829076546187383961)
      ·
        refine ⟨247296838371807409640537971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329729117829076546187383961 247296838371807409640537971)
        ·
          refine ⟨370945257557711114460806957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247296838371807409640537971 370945257557711114460806957)
          ·
            refine ⟨139104471584141667922802609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370945257557711114460806957 139104471584141667922802609)
            ·
              refine ⟨104328353688106250942101957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139104471584141667922802609 104328353688106250942101957)
              ·
                refine ⟨19561566316519922051644117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104328353688106250942101957 19561566316519922051644117)
                ·
                  refine ⟨458474210543435673085409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19561566316519922051644117 458474210543435673085409)
                  ·
                    rfl

theorem cell22_4017939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_4017939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4017939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4017939 prefixEnd_4017939 := by exact prefixLift 4017939
  have htrace : WordTrace (prefixWord ++ tailWord_4017939) baseStart_4017939 baseEnd_4017939 := by
    simpa [prefixWord, tailWord_4017939, baseEnd_4017939] using wordTrace_append hprefix tailTrace_4017939
  have hstable : (prefixWord ++ tailWord_4017939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4017939).length < 2 ^ (prefixWord ++ tailWord_4017939).sum := by decide
  have hdescent : baseEnd_4017939 < baseStart_4017939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4017939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018018 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4018018 : Nat := 118140960795 + 4018018 * 2 ^ 59
def prefixEnd_4018018 : Nat := 4983230072969 + 3 ^ 40 * 4018018 * 2
def baseEnd_4018018 : Nat := 458483224981592382176995

theorem tailTrace_4018018 : CollatzResearch.WordTrace tailWord_4018018 prefixEnd_4018018 458483224981592382176995 := by
  unfold tailWord_4018018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36637288989353620921629677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97699437304942989124345805 36637288989353620921629677)
  ·
    refine ⟨13738983371007607845611129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36637288989353620921629677 13738983371007607845611129)
    ·
      refine ⟨10304237528255705884208347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13738983371007607845611129 10304237528255705884208347)
      ·
        refine ⟨15456356292383558826312521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10304237528255705884208347 15456356292383558826312521)
        ·
          refine ⟨11592267219287669119734391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15456356292383558826312521 11592267219287669119734391)
          ·
            refine ⟨17388400828931503679601587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592267219287669119734391 17388400828931503679601587)
            ·
              refine ⟨26082601243397255519402381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17388400828931503679601587 26082601243397255519402381)
              ·
                refine ⟨9780975466273970819775893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26082601243397255519402381 9780975466273970819775893)
                ·
                  refine ⟨458483224981592382176995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9780975466273970819775893 458483224981592382176995)
                  ·
                    rfl

theorem cell22_4018018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4018018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018018 prefixEnd_4018018 := by exact prefixLift 4018018
  have htrace : WordTrace (prefixWord ++ tailWord_4018018) baseStart_4018018 baseEnd_4018018 := by
    simpa [prefixWord, tailWord_4018018, baseEnd_4018018] using wordTrace_append hprefix tailTrace_4018018
  have hstable : (prefixWord ++ tailWord_4018018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018018).length < 2 ^ (prefixWord ++ tailWord_4018018).sum := by decide
  have hdescent : baseEnd_4018018 < baseStart_4018018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018106 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_4018106 : Nat := 118140960795 + 4018106 * 2 ^ 59
def prefixEnd_4018106 : Nat := 4983230072969 + 3 ^ 40 * 4018106 * 2
def baseEnd_4018106 : Nat := 1375479799143174250330715

theorem tailTrace_4018106 : CollatzResearch.WordTrace tailWord_4018106 prefixEnd_4018106 1375479799143174250330715 := by
  unfold tailWord_4018106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638091395273918678930543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97701577054063783143814781 36638091395273918678930543)
  ·
    refine ⟨54957137092910878018395815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36638091395273918678930543 54957137092910878018395815)
    ·
      refine ⟨82435705639366317027593723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54957137092910878018395815 82435705639366317027593723)
      ·
        refine ⟨123653558459049475541390585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82435705639366317027593723 123653558459049475541390585)
        ·
          refine ⟨92740168844287106656042939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123653558459049475541390585 92740168844287106656042939)
          ·
            refine ⟨139110253266430659984064409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92740168844287106656042939 139110253266430659984064409)
            ·
              refine ⟨104332689949822994988048307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139110253266430659984064409 104332689949822994988048307)
              ·
                refine ⟨156499034924734492482072461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104332689949822994988048307 156499034924734492482072461)
                ·
                  refine ⟨58687138096775434680777173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156499034924734492482072461 58687138096775434680777173)
                  ·
                    refine ⟨1375479799143174250330715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58687138096775434680777173 1375479799143174250330715)
                    ·
                      rfl

theorem cell22_4018106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_4018106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018106 prefixEnd_4018106 := by exact prefixLift 4018106
  have htrace : WordTrace (prefixWord ++ tailWord_4018106) baseStart_4018106 baseEnd_4018106 := by
    simpa [prefixWord, tailWord_4018106, baseEnd_4018106] using wordTrace_append hprefix tailTrace_4018106
  have hstable : (prefixWord ++ tailWord_4018106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018106).length < 2 ^ (prefixWord ++ tailWord_4018106).sum := by decide
  have hdescent : baseEnd_4018106 < baseStart_4018106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018168 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_4018168 : Nat := 118140960795 + 4018168 * 2 ^ 59
def prefixEnd_4018168 : Nat := 4983230072969 + 3 ^ 40 * 4018168 * 2
def baseEnd_4018168 : Nat := 1375501023010226755280525

theorem tailTrace_4018168 : CollatzResearch.WordTrace tailWord_4018168 prefixEnd_4018168 1375501023010226755280525 := by
  unfold tailWord_4018168
  simp only [CollatzResearch.WordTrace]
  refine ⟨73277313453435529652239579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97703084604580706202986105 73277313453435529652239579)
  ·
    refine ⟨109915970180153294478359369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73277313453435529652239579 109915970180153294478359369)
    ·
      refine ⟨82436977635114970858769527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109915970180153294478359369 82436977635114970858769527)
      ·
        refine ⟨123655466452672456288154291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82436977635114970858769527 123655466452672456288154291)
        ·
          refine ⟨185483199679008684432231437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123655466452672456288154291 185483199679008684432231437)
          ·
            refine ⟨69556199879628256662086789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185483199679008684432231437 69556199879628256662086789)
            ·
              refine ⟨13041787477430298124141273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69556199879628256662086789 13041787477430298124141273)
              ·
                refine ⟨9781340608072723593105955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13041787477430298124141273 9781340608072723593105955)
                ·
                  refine ⟨14672010912109085389658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781340608072723593105955 14672010912109085389658933)
                  ·
                    refine ⟨1375501023010226755280525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14672010912109085389658933 1375501023010226755280525)
                    ·
                      rfl

theorem cell22_4018168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_4018168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018168 prefixEnd_4018168 := by exact prefixLift 4018168
  have htrace : WordTrace (prefixWord ++ tailWord_4018168) baseStart_4018168 baseEnd_4018168 := by
    simpa [prefixWord, tailWord_4018168, baseEnd_4018168] using wordTrace_append hprefix tailTrace_4018168
  have hstable : (prefixWord ++ tailWord_4018168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018168).length < 2 ^ (prefixWord ++ tailWord_4018168).sum := by decide
  have hdescent : baseEnd_4018168 < baseStart_4018168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018320 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_4018320 : Nat := 118140960795 + 4018320 * 2 ^ 59
def prefixEnd_4018320 : Nat := 4983230072969 + 3 ^ 40 * 4018320 * 2
def baseEnd_4018320 : Nat := 1375553055716549025480059

theorem tailTrace_4018320 : CollatzResearch.WordTrace tailWord_4018320 prefixEnd_4018320 1375553055716549025480059 := by
  unfold tailWord_4018320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73280085401160194632006207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97706780534880259509341609 73280085401160194632006207)
  ·
    refine ⟨109920128101740291948009311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73280085401160194632006207 109920128101740291948009311)
    ·
      refine ⟨164880192152610437922013967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109920128101740291948009311 164880192152610437922013967)
      ·
        refine ⟨247320288228915656883020951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164880192152610437922013967 247320288228915656883020951)
        ·
          refine ⟨370980432343373485324531427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247320288228915656883020951 370980432343373485324531427)
          ·
            refine ⟨556470648515060227986797141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370980432343373485324531427 556470648515060227986797141)
            ·
              refine ⟨6521140412285862046720279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 556470648515060227986797141 6521140412285862046720279)
              ·
                refine ⟨9781710618428793070080419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521140412285862046720279 9781710618428793070080419)
                ·
                  refine ⟨14672565927643189605120629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781710618428793070080419 14672565927643189605120629)
                  ·
                    refine ⟨1375553055716549025480059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14672565927643189605120629 1375553055716549025480059)
                    ·
                      rfl

theorem cell22_4018320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_4018320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018320 prefixEnd_4018320 := by exact prefixLift 4018320
  have htrace : WordTrace (prefixWord ++ tailWord_4018320) baseStart_4018320 baseEnd_4018320 := by
    simpa [prefixWord, tailWord_4018320, baseEnd_4018320] using wordTrace_append hprefix tailTrace_4018320
  have hstable : (prefixWord ++ tailWord_4018320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018320).length < 2 ^ (prefixWord ++ tailWord_4018320).sum := by decide
  have hdescent : baseEnd_4018320 < baseStart_4018320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018489 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_4018489 : Nat := 118140960795 + 4018489 * 2 ^ 59
def prefixEnd_4018489 : Nat := 4983230072969 + 3 ^ 40 * 4018489 * 2
def baseEnd_4018489 : Nat := 1375610907870288918004541

theorem tailTrace_4018489 : CollatzResearch.WordTrace tailWord_4018489 prefixEnd_4018489 1375610907870288918004541 := by
  unfold tailWord_4018489
  simp only [CollatzResearch.WordTrace]
  refine ⟨146566334738708131126914521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97710889825805420751276347 146566334738708131126914521)
  ·
    refine ⟨109924751054031098345185891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146566334738708131126914521 109924751054031098345185891)
    ·
      refine ⟨164887126581046647517778837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109924751054031098345185891 164887126581046647517778837)
      ·
        refine ⟨7729084058486561602395883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164887126581046647517778837 7729084058486561602395883)
        ·
          refine ⟨11593626087729842403593825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729084058486561602395883 11593626087729842403593825)
          ·
            refine ⟨8695219565797381802695369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11593626087729842403593825 8695219565797381802695369)
            ·
              refine ⟨6521414674348036352021527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8695219565797381802695369 6521414674348036352021527)
              ·
                refine ⟨9782122011522054528032291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521414674348036352021527 9782122011522054528032291)
                ·
                  refine ⟨14673183017283081792048437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9782122011522054528032291 14673183017283081792048437)
                  ·
                    refine ⟨1375610907870288918004541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14673183017283081792048437 1375610907870288918004541)
                    ·
                      rfl

theorem cell22_4018489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_4018489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018489 prefixEnd_4018489 := by exact prefixLift 4018489
  have htrace : WordTrace (prefixWord ++ tailWord_4018489) baseStart_4018489 baseEnd_4018489 := by
    simpa [prefixWord, tailWord_4018489, baseEnd_4018489] using wordTrace_append hprefix tailTrace_4018489
  have hstable : (prefixWord ++ tailWord_4018489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018489).length < 2 ^ (prefixWord ++ tailWord_4018489).sum := by decide
  have hdescent : baseEnd_4018489 < baseStart_4018489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018515 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_4018515 : Nat := 118140960795 + 4018515 * 2 ^ 59
def prefixEnd_4018515 : Nat := 4983230072969 + 3 ^ 40 * 4018515 * 2
def baseEnd_4018515 : Nat := 1375619808201633516854461

theorem tailTrace_4018515 : CollatzResearch.WordTrace tailWord_4018515 prefixEnd_4018515 1375619808201633516854461 := by
  unfold tailWord_4018515
  simp only [CollatzResearch.WordTrace]
  refine ⟨146567283036613937567360999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97711522024409291711573999 146567283036613937567360999)
  ·
    refine ⟨219850924554920906351041499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146567283036613937567360999 219850924554920906351041499)
    ·
      refine ⟨329776386832381359526562249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219850924554920906351041499 329776386832381359526562249)
      ·
        refine ⟨247332290124286019644921687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329776386832381359526562249 247332290124286019644921687)
        ·
          refine ⟨370998435186429029467382531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247332290124286019644921687 370998435186429029467382531)
          ·
            refine ⟨556497652779643544201073797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370998435186429029467382531 556497652779643544201073797)
            ·
              refine ⟨104343309896183164537701337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556497652779643544201073797 104343309896183164537701337)
              ·
                refine ⟨78257482422137373403276003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104343309896183164537701337 78257482422137373403276003)
                ·
                  refine ⟨117386223633206060104914005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78257482422137373403276003 117386223633206060104914005)
                  ·
                    refine ⟨1375619808201633516854461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117386223633206060104914005 1375619808201633516854461)
                    ·
                      rfl

theorem cell22_4018515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_4018515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018515 prefixEnd_4018515 := by exact prefixLift 4018515
  have htrace : WordTrace (prefixWord ++ tailWord_4018515) baseStart_4018515 baseEnd_4018515 := by
    simpa [prefixWord, tailWord_4018515, baseEnd_4018515] using wordTrace_append hprefix tailTrace_4018515
  have hstable : (prefixWord ++ tailWord_4018515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018515).length < 2 ^ (prefixWord ++ tailWord_4018515).sum := by decide
  have hdescent : baseEnd_4018515 < baseStart_4018515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018594 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4018594 : Nat := 118140960795 + 4018594 * 2 ^ 59
def prefixEnd_4018594 : Nat := 4983230072969 + 3 ^ 40 * 4018594 * 2
def baseEnd_4018594 : Nat := 1375646851516103644129219

theorem tailTrace_4018594 : CollatzResearch.WordTrace tailWord_4018594 prefixEnd_4018594 1375646851516103644129219 := by
  unfold tailWord_4018594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36642541100831933514871709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97713442935551822706324557 36642541100831933514871709)
  ·
    refine ⟨13740952912811975068076891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36642541100831933514871709 13740952912811975068076891)
    ·
      refine ⟨20611429369217962602115337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13740952912811975068076891 20611429369217962602115337)
      ·
        refine ⟨15458572026913471951586503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20611429369217962602115337 15458572026913471951586503)
        ·
          refine ⟨23187858040370207927379755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15458572026913471951586503 23187858040370207927379755)
          ·
            refine ⟨34781787060555311891069633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23187858040370207927379755 34781787060555311891069633)
            ·
              refine ⟨26086340295416483918302225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34781787060555311891069633 26086340295416483918302225)
              ·
                refine ⟨19564755221562362938726669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26086340295416483918302225 19564755221562362938726669)
                ·
                  refine ⟨7336783208085886102022501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19564755221562362938726669 7336783208085886102022501)
                  ·
                    refine ⟨1375646851516103644129219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336783208085886102022501 1375646851516103644129219)
                    ·
                      rfl

theorem cell22_4018594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4018594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018594 prefixEnd_4018594 := by exact prefixLift 4018594
  have htrace : WordTrace (prefixWord ++ tailWord_4018594) baseStart_4018594 baseEnd_4018594 := by
    simpa [prefixWord, tailWord_4018594, baseEnd_4018594] using wordTrace_append hprefix tailTrace_4018594
  have hstable : (prefixWord ++ tailWord_4018594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018594).length < 2 ^ (prefixWord ++ tailWord_4018594).sum := by decide
  have hdescent : baseEnd_4018594 < baseStart_4018594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018637 : List Nat := [1, 6, 15]
def baseStart_4018637 : Nat := 118140960795 + 4018637 * 2 ^ 59
def prefixEnd_4018637 : Nat := 4983230072969 + 3 ^ 40 * 4018637 * 2
def baseEnd_4018637 : Nat := 629017636623166833701

theorem tailTrace_4018637 : CollatzResearch.WordTrace tailWord_4018637 prefixEnd_4018637 629017636623166833701 := by
  unfold tailWord_4018637
  simp only [CollatzResearch.WordTrace]
  refine ⟨146571732742171952403302165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97714488494781301602201443 146571732742171952403302165)
  ·
    refine ⟨6870549972289310268904789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146571732742171952403302165 6870549972289310268904789)
    ·
      refine ⟨629017636623166833701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 6870549972289310268904789 629017636623166833701)
      ·
        rfl

theorem cell22_4018637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 15].length) (baseStart_4018637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018637 prefixEnd_4018637 := by exact prefixLift 4018637
  have htrace : WordTrace (prefixWord ++ tailWord_4018637) baseStart_4018637 baseEnd_4018637 := by
    simpa [prefixWord, tailWord_4018637, baseEnd_4018637] using wordTrace_append hprefix tailTrace_4018637
  have hstable : (prefixWord ++ tailWord_4018637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018637).length < 2 ^ (prefixWord ++ tailWord_4018637).sum := by decide
  have hdescent : baseEnd_4018637 < baseStart_4018637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018667 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_4018667 : Nat := 118140960795 + 4018667 * 2 ^ 59
def prefixEnd_4018667 : Nat := 4983230072969 + 3 ^ 40 * 4018667 * 2
def baseEnd_4018667 : Nat := 1375671840907955787053995

theorem tailTrace_4018667 : CollatzResearch.WordTrace tailWord_4018667 prefixEnd_4018667 1375671840907955787053995 := by
  unfold tailWord_4018667
  simp only [CollatzResearch.WordTrace]
  refine ⟨146572826932063267526894255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97715217954708845017929503 146572826932063267526894255)
  ·
    refine ⟨219859240398094901290341383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146572826932063267526894255 219859240398094901290341383)
    ·
      refine ⟨329788860597142351935512075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219859240398094901290341383 329788860597142351935512075)
      ·
        refine ⟨494683290895713527903268113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329788860597142351935512075 494683290895713527903268113)
        ·
          refine ⟨371012468171785145927451085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494683290895713527903268113 371012468171785145927451085)
          ·
            refine ⟨139129675564419429722794157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371012468171785145927451085 139129675564419429722794157)
            ·
              refine ⟨52173628336657286146047809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139129675564419429722794157 52173628336657286146047809)
              ·
                refine ⟨39130221252492964609535857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52173628336657286146047809 39130221252492964609535857)
                ·
                  refine ⟨29347665939369723457151893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39130221252492964609535857 29347665939369723457151893)
                  ·
                    refine ⟨1375671840907955787053995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29347665939369723457151893 1375671840907955787053995)
                    ·
                      rfl

theorem cell22_4018667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_4018667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018667 prefixEnd_4018667 := by exact prefixLift 4018667
  have htrace : WordTrace (prefixWord ++ tailWord_4018667) baseStart_4018667 baseEnd_4018667 := by
    simpa [prefixWord, tailWord_4018667, baseEnd_4018667] using wordTrace_append hprefix tailTrace_4018667
  have hstable : (prefixWord ++ tailWord_4018667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018667).length < 2 ^ (prefixWord ++ tailWord_4018667).sum := by decide
  have hdescent : baseEnd_4018667 < baseStart_4018667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018699 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 7]
def baseStart_4018699 : Nat := 118140960795 + 4018699 * 2 ^ 59
def prefixEnd_4018699 : Nat := 4983230072969 + 3 ^ 40 * 4018699 * 2
def baseEnd_4018699 : Nat := 458560931720639456751299

theorem tailTrace_4018699 : CollatzResearch.WordTrace tailWord_4018699 prefixEnd_4018699 458560931720639456751299 := by
  unfold tailWord_4018699
  simp only [CollatzResearch.WordTrace]
  refine ⟨146573994067947336992059151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97715996045298224661372767 146573994067947336992059151)
  ·
    refine ⟨219860991101921005488088727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146573994067947336992059151 219860991101921005488088727)
    ·
      refine ⟨329791486652881508232133091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219860991101921005488088727 329791486652881508232133091)
      ·
        refine ⟨494687229979322262348199637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329791486652881508232133091 494687229979322262348199637)
        ·
          refine ⟨11594231952640365523785929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 494687229979322262348199637 11594231952640365523785929)
          ·
            refine ⟨8695673964480274142839447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11594231952640365523785929 8695673964480274142839447)
            ·
              refine ⟨13043510946720411214259171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695673964480274142839447 13043510946720411214259171)
              ·
                refine ⟨19565266420080616821388757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13043510946720411214259171 19565266420080616821388757)
                ·
                  refine ⟨458560931720639456751299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19565266420080616821388757 458560931720639456751299)
                  ·
                    rfl

theorem cell22_4018699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_4018699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018699 prefixEnd_4018699 := by exact prefixLift 4018699
  have htrace : WordTrace (prefixWord ++ tailWord_4018699) baseStart_4018699 baseEnd_4018699 := by
    simpa [prefixWord, tailWord_4018699, baseEnd_4018699] using wordTrace_append hprefix tailTrace_4018699
  have hstable : (prefixWord ++ tailWord_4018699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018699).length < 2 ^ (prefixWord ++ tailWord_4018699).sum := by decide
  have hdescent : baseEnd_4018699 < baseStart_4018699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018714 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_4018714 : Nat := 118140960795 + 4018714 * 2 ^ 59
def prefixEnd_4018714 : Nat := 4983230072969 + 3 ^ 40 * 4018714 * 2
def baseEnd_4018714 : Nat := 1375687929968463331128851

theorem tailTrace_4018714 : CollatzResearch.WordTrace tailWord_4018714 prefixEnd_4018714 1375687929968463331128851 := by
  unfold tailWord_4018714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643635290723248638463799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97716360775261996369236797 36643635290723248638463799)
  ·
    refine ⟨54965452936084872957695699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36643635290723248638463799 54965452936084872957695699)
    ·
      refine ⟨82448179404127309436543549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54965452936084872957695699 82448179404127309436543549)
      ·
        refine ⟨30918067276547741038703831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82448179404127309436543549 30918067276547741038703831)
        ·
          refine ⟨46377100914821611558055747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30918067276547741038703831 46377100914821611558055747)
          ·
            refine ⟨69565651372232417337083621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46377100914821611558055747 69565651372232417337083621)
            ·
              refine ⟨13043559632293578250703179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69565651372232417337083621 13043559632293578250703179)
              ·
                refine ⟨19565339448440367376054769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13043559632293578250703179 19565339448440367376054769)
                ·
                  refine ⟨14674004586330275532041077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19565339448440367376054769 14674004586330275532041077)
                  ·
                    refine ⟨1375687929968463331128851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14674004586330275532041077 1375687929968463331128851)
                    ·
                      rfl

theorem cell22_4018714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_4018714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018714 prefixEnd_4018714 := by exact prefixLift 4018714
  have htrace : WordTrace (prefixWord ++ tailWord_4018714) baseStart_4018714 baseEnd_4018714 := by
    simpa [prefixWord, tailWord_4018714, baseEnd_4018714] using wordTrace_append hprefix tailTrace_4018714
  have hstable : (prefixWord ++ tailWord_4018714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018714).length < 2 ^ (prefixWord ++ tailWord_4018714).sum := by decide
  have hdescent : baseEnd_4018714 < baseStart_4018714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018746 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_4018746 : Nat := 118140960795 + 4018746 * 2 ^ 59
def prefixEnd_4018746 : Nat := 4983230072969 + 3 ^ 40 * 4018746 * 2
def baseEnd_4018746 : Nat := 1375698884222425914328753

theorem tailTrace_4018746 : CollatzResearch.WordTrace tailWord_4018746 prefixEnd_4018746 1375698884222425914328753 := by
  unfold tailWord_4018746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643927074694266004755023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97717138865851376012680061 36643927074694266004755023)
  ·
    refine ⟨54965890612041399007132535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36643927074694266004755023 54965890612041399007132535)
    ·
      refine ⟨82448835918062098510698803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54965890612041399007132535 82448835918062098510698803)
      ·
        refine ⟨123673253877093147766048205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82448835918062098510698803 123673253877093147766048205)
        ·
          refine ⟨46377470203909930412268077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123673253877093147766048205 46377470203909930412268077)
          ·
            refine ⟨17391551326466223904600529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46377470203909930412268077 17391551326466223904600529)
            ·
              refine ⟨13043663494849667928450397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17391551326466223904600529 13043663494849667928450397)
              ·
                refine ⟨4891373810568625473168899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13043663494849667928450397 4891373810568625473168899)
                ·
                  refine ⟨7337060715852938209753349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891373810568625473168899 7337060715852938209753349)
                  ·
                    refine ⟨1375698884222425914328753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337060715852938209753349 1375698884222425914328753)
                    ·
                      rfl

theorem cell22_4018746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_4018746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018746 prefixEnd_4018746 := by exact prefixLift 4018746
  have htrace : WordTrace (prefixWord ++ tailWord_4018746) baseStart_4018746 baseEnd_4018746 := by
    simpa [prefixWord, tailWord_4018746, baseEnd_4018746] using wordTrace_append hprefix tailTrace_4018746
  have hstable : (prefixWord ++ tailWord_4018746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018746).length < 2 ^ (prefixWord ++ tailWord_4018746).sum := by decide
  have hdescent : baseEnd_4018746 < baseStart_4018746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018780 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_4018780 : Nat := 118140960795 + 4018780 * 2 ^ 59
def prefixEnd_4018780 : Nat := 4983230072969 + 3 ^ 40 * 4018780 * 2
def baseEnd_4018780 : Nat := 1375710523117261158978649

theorem tailTrace_4018780 : CollatzResearch.WordTrace tailWord_4018780 prefixEnd_4018780 1375710523117261158978649 := by
  unfold tailWord_4018780
  simp only [CollatzResearch.WordTrace]
  refine ⟨73288474190326943912878897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97717965587102591883838529 73288474190326943912878897)
  ·
    refine ⟨54966355642745207934659173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73288474190326943912878897 54966355642745207934659173)
    ·
      refine ⟨10306191683014726487748595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54966355642745207934659173 10306191683014726487748595)
      ·
        refine ⟨15459287524522089731622893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306191683014726487748595 15459287524522089731622893)
        ·
          refine ⟨5797232821695783649358585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15459287524522089731622893 5797232821695783649358585)
          ·
            refine ⟨4347924616271837737018939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797232821695783649358585 4347924616271837737018939)
            ·
              refine ⟨6521886924407756605528409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347924616271837737018939 6521886924407756605528409)
              ·
                refine ⟨4891415193305817454146307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521886924407756605528409 4891415193305817454146307)
                ·
                  refine ⟨7337122789958726181219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891415193305817454146307 7337122789958726181219461)
                  ·
                    refine ⟨1375710523117261158978649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337122789958726181219461 1375710523117261158978649)
                    ·
                      rfl

theorem cell22_4018780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_4018780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018780 prefixEnd_4018780 := by exact prefixLift 4018780
  have htrace : WordTrace (prefixWord ++ tailWord_4018780) baseStart_4018780 baseEnd_4018780 := by
    simpa [prefixWord, tailWord_4018780, baseEnd_4018780] using wordTrace_append hprefix tailTrace_4018780
  have hstable : (prefixWord ++ tailWord_4018780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018780).length < 2 ^ (prefixWord ++ tailWord_4018780).sum := by decide
  have hdescent : baseEnd_4018780 < baseStart_4018780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018806 : List Nat := [5, 1, 1, 2, 3, 10]
def baseStart_4018806 : Nat := 118140960795 + 4018806 * 2 ^ 59
def prefixEnd_4018806 : Nat := 4983230072969 + 3 ^ 40 * 4018806 * 2
def baseEnd_4018806 : Nat := 16984190412945750096649

theorem tailTrace_4018806 : CollatzResearch.WordTrace tailWord_4018806 prefixEnd_4018806 16984190412945750096649 := by
  unfold tailWord_4018806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161118542409980891637767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97718597785706462844136181 9161118542409980891637767)
  ·
    refine ⟨13741677813614971337456651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9161118542409980891637767 13741677813614971337456651)
    ·
      refine ⟨20612516720422457006184977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13741677813614971337456651 20612516720422457006184977)
      ·
        refine ⟨15459387540316842754638733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20612516720422457006184977 15459387540316842754638733)
        ·
          refine ⟨5797270327618816032989525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15459387540316842754638733 5797270327618816032989525)
          ·
            refine ⟨16984190412945750096649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5797270327618816032989525 16984190412945750096649)
            ·
              rfl

theorem cell22_4018806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 10].length) (baseStart_4018806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018806 prefixEnd_4018806 := by exact prefixLift 4018806
  have htrace : WordTrace (prefixWord ++ tailWord_4018806) baseStart_4018806 baseEnd_4018806 := by
    simpa [prefixWord, tailWord_4018806, baseEnd_4018806] using wordTrace_append hprefix tailTrace_4018806
  have hstable : (prefixWord ++ tailWord_4018806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018806).length < 2 ^ (prefixWord ++ tailWord_4018806).sum := by decide
  have hdescent : baseEnd_4018806 < baseStart_4018806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018819 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_4018819 : Nat := 118140960795 + 4018819 * 2 ^ 59
def prefixEnd_4018819 : Nat := 4983230072969 + 3 ^ 40 * 4018819 * 2
def baseEnd_4018819 : Nat := 1375723873614278057253529

theorem tailTrace_4018819 : CollatzResearch.WordTrace tailWord_4018819 prefixEnd_4018819 1375723873614278057253529 := by
  unfold tailWord_4018819
  simp only [CollatzResearch.WordTrace]
  refine ⟨146578370827512597486427511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97718913885008398324285007 146578370827512597486427511)
  ·
    refine ⟨219867556241268896229641267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146578370827512597486427511 219867556241268896229641267)
    ·
      refine ⟨329801334361903344344461901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219867556241268896229641267 329801334361903344344461901)
      ·
        refine ⟨123675500385713754129173213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329801334361903344344461901 123675500385713754129173213)
        ·
          refine ⟨46378312644642657798439955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123675500385713754129173213 46378312644642657798439955)
          ·
            refine ⟨69567468966963986697659933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46378312644642657798439955 69567468966963986697659933)
            ·
              refine ⟨26087800862611495011622475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69567468966963986697659933 26087800862611495011622475)
              ·
                refine ⟨39131701293917242517433713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26087800862611495011622475 39131701293917242517433713)
                ·
                  refine ⟨29348775970437931888075285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39131701293917242517433713 29348775970437931888075285)
                  ·
                    refine ⟨1375723873614278057253529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29348775970437931888075285 1375723873614278057253529)
                    ·
                      rfl

theorem cell22_4018819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_4018819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018819 prefixEnd_4018819 := by exact prefixLift 4018819
  have htrace : WordTrace (prefixWord ++ tailWord_4018819) baseStart_4018819 baseEnd_4018819 := by
    simpa [prefixWord, tailWord_4018819, baseEnd_4018819] using wordTrace_append hprefix tailTrace_4018819
  have hstable : (prefixWord ++ tailWord_4018819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018819).length < 2 ^ (prefixWord ++ tailWord_4018819).sum := by decide
  have hdescent : baseEnd_4018819 < baseStart_4018819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018842 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_4018842 : Nat := 118140960795 + 4018842 * 2 ^ 59
def prefixEnd_4018842 : Nat := 4983230072969 + 3 ^ 40 * 4018842 * 2
def baseEnd_4018842 : Nat := 1375731746984313663928459

theorem tailTrace_4018842 : CollatzResearch.WordTrace tailWord_4018842 prefixEnd_4018842 1375731746984313663928459 := by
  unfold tailWord_4018842
  simp only [CollatzResearch.WordTrace]
  refine ⟨36644802426607318103628695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97719473137619514943009853 36644802426607318103628695)
  ·
    refine ⟨54967203639910977155443043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36644802426607318103628695 54967203639910977155443043)
    ·
      refine ⟨82450805459866465733164565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54967203639910977155443043 82450805459866465733164565)
      ·
        refine ⟨3864881505931240581242089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82450805459866465733164565 3864881505931240581242089)
        ·
          refine ⟨2898661129448430435931567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864881505931240581242089 2898661129448430435931567)
          ·
            refine ⟨4347991694172645653897351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898661129448430435931567 4347991694172645653897351)
            ·
              refine ⟨6521987541258968480846027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347991694172645653897351 6521987541258968480846027)
              ·
                refine ⟨9782981311888452721269041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521987541258968480846027 9782981311888452721269041)
                ·
                  refine ⟨7337235983916339540951781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9782981311888452721269041 7337235983916339540951781)
                  ·
                    refine ⟨1375731746984313663928459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337235983916339540951781 1375731746984313663928459)
                    ·
                      rfl

theorem cell22_4018842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_4018842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018842 prefixEnd_4018842 := by exact prefixLift 4018842
  have htrace : WordTrace (prefixWord ++ tailWord_4018842) baseStart_4018842 baseEnd_4018842 := by
    simpa [prefixWord, tailWord_4018842, baseEnd_4018842] using wordTrace_append hprefix tailTrace_4018842
  have hstable : (prefixWord ++ tailWord_4018842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018842).length < 2 ^ (prefixWord ++ tailWord_4018842).sum := by decide
  have hdescent : baseEnd_4018842 < baseStart_4018842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018928 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_4018928 : Nat := 118140960795 + 4018928 * 2 ^ 59
def prefixEnd_4018928 : Nat := 4983230072969 + 3 ^ 40 * 4018928 * 2
def baseEnd_4018928 : Nat := 1375761186541838106278195

theorem tailTrace_4018928 : CollatzResearch.WordTrace tailWord_4018928 prefixEnd_4018928 1375761186541838106278195 := by
  unfold tailWord_4018928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73291173192058854551072719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97721564256078472734763625 73291173192058854551072719)
  ·
    refine ⟨109936759788088281826609079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73291173192058854551072719 109936759788088281826609079)
    ·
      refine ⟨164905139682132422739913619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109936759788088281826609079 164905139682132422739913619)
      ·
        refine ⟨247357709523198634109870429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164905139682132422739913619 247357709523198634109870429)
        ·
          refine ⟨92759141071199487791201411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247357709523198634109870429 92759141071199487791201411)
          ·
            refine ⟨139138711606799231686802117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92759141071199487791201411 139138711606799231686802117)
            ·
              refine ⟨26088508426274855941275397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139138711606799231686802117 26088508426274855941275397)
              ·
                refine ⟨4891595329926535488989137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26088508426274855941275397 4891595329926535488989137)
                ·
                  refine ⟨3668696497444901616741853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4891595329926535488989137 3668696497444901616741853)
                  ·
                    refine ⟨1375761186541838106278195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3668696497444901616741853 1375761186541838106278195)
                    ·
                      rfl

theorem cell22_4018928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_4018928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018928 prefixEnd_4018928 := by exact prefixLift 4018928
  have htrace : WordTrace (prefixWord ++ tailWord_4018928) baseStart_4018928 baseEnd_4018928 := by
    simpa [prefixWord, tailWord_4018928, baseEnd_4018928] using wordTrace_append hprefix tailTrace_4018928
  have hstable : (prefixWord ++ tailWord_4018928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018928).length < 2 ^ (prefixWord ++ tailWord_4018928).sum := by decide
  have hdescent : baseEnd_4018928 < baseStart_4018928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4018941 : List Nat := [1, 4, 1, 1, 1, 1, 6, 7]
def baseStart_4018941 : Nat := 118140960795 + 4018941 * 2 ^ 59
def prefixEnd_4018941 : Nat := 4983230072969 + 3 ^ 40 * 4018941 * 2
def baseEnd_4018941 : Nat := 152862848523056711744795

theorem tailTrace_4018941 : CollatzResearch.WordTrace tailWord_4018941 prefixEnd_4018941 152862848523056711744795 := by
  unfold tailWord_4018941
  simp only [CollatzResearch.WordTrace]
  refine ⟨146582820533070612322368677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97721880355380408214912451 146582820533070612322368677)
  ·
    refine ⟨27484278849950739810444127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146582820533070612322368677 27484278849950739810444127)
    ·
      refine ⟨41226418274926109715666191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27484278849950739810444127 41226418274926109715666191)
      ·
        refine ⟨61839627412389164573499287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41226418274926109715666191 61839627412389164573499287)
        ·
          refine ⟨92759441118583746860248931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61839627412389164573499287 92759441118583746860248931)
          ·
            refine ⟨139139161677875620290373397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92759441118583746860248931 139139161677875620290373397)
            ·
              refine ⟨6522148203650419701111253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139139161677875620290373397 6522148203650419701111253)
              ·
                refine ⟨152862848523056711744795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6522148203650419701111253 152862848523056711744795)
                ·
                  rfl

theorem cell22_4018941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 7].length) (baseStart_4018941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4018941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4018941 prefixEnd_4018941 := by exact prefixLift 4018941
  have htrace : WordTrace (prefixWord ++ tailWord_4018941) baseStart_4018941 baseEnd_4018941 := by
    simpa [prefixWord, tailWord_4018941, baseEnd_4018941] using wordTrace_append hprefix tailTrace_4018941
  have hstable : (prefixWord ++ tailWord_4018941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4018941).length < 2 ^ (prefixWord ++ tailWord_4018941).sum := by decide
  have hdescent : baseEnd_4018941 < baseStart_4018941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4018941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019048 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_4019048 : Nat := 118140960795 + 4019048 * 2 ^ 59
def prefixEnd_4019048 : Nat := 4983230072969 + 3 ^ 40 * 4019048 * 2
def baseEnd_4019048 : Nat := 458600754998065931092609

theorem tailTrace_4019048 : CollatzResearch.WordTrace tailWord_4019048 prefixEnd_4019048 458600754998065931092609 := by
  unfold tailWord_4019048
  simp only [CollatzResearch.WordTrace]
  refine ⟨73293361571841484798256899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97724482095788646397675865 73293361571841484798256899)
  ·
    refine ⟨109940042357762227197385349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73293361571841484798256899 109940042357762227197385349)
    ·
      refine ⟨20613757942080417599509753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109940042357762227197385349 20613757942080417599509753)
      ·
        refine ⟨15460318456560313199632315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20613757942080417599509753 15460318456560313199632315)
        ·
          refine ⟨23190477684840469799448473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460318456560313199632315 23190477684840469799448473)
          ·
            refine ⟨17392858263630352349586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23190477684840469799448473 17392858263630352349586355)
            ·
              refine ⟨26089287395445528524379533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17392858263630352349586355 26089287395445528524379533)
              ·
                refine ⟨9783482773292073196642325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26089287395445528524379533 9783482773292073196642325)
                ·
                  refine ⟨458600754998065931092609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9783482773292073196642325 458600754998065931092609)
                  ·
                    rfl

theorem cell22_4019048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_4019048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019048 prefixEnd_4019048 := by exact prefixLift 4019048
  have htrace : WordTrace (prefixWord ++ tailWord_4019048) baseStart_4019048 baseEnd_4019048 := by
    simpa [prefixWord, tailWord_4019048, baseEnd_4019048] using wordTrace_append hprefix tailTrace_4019048
  have hstable : (prefixWord ++ tailWord_4019048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019048).length < 2 ^ (prefixWord ++ tailWord_4019048).sum := by decide
  have hdescent : baseEnd_4019048 < baseStart_4019048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019080 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_4019080 : Nat := 118140960795 + 4019080 * 2 ^ 59
def prefixEnd_4019080 : Nat := 4983230072969 + 3 ^ 40 * 4019080 * 2
def baseEnd_4019080 : Nat := 1375813219248160376477729

theorem tailTrace_4019080 : CollatzResearch.WordTrace tailWord_4019080 prefixEnd_4019080 1375813219248160376477729 := by
  unfold tailWord_4019080
  simp only [CollatzResearch.WordTrace]
  refine ⟨73293945139783519530839347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97725260186378026041119129 73293945139783519530839347)
  ·
    refine ⟨109940917709675279296259021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73293945139783519530839347 109940917709675279296259021)
    ·
      refine ⟨41227844141128229736097133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109940917709675279296259021 41227844141128229736097133)
      ·
        refine ⟨15460441552923086151036425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41227844141128229736097133 15460441552923086151036425)
        ·
          refine ⟨11595331164692314613277319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15460441552923086151036425 11595331164692314613277319)
          ·
            refine ⟨17392996747038471919915979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595331164692314613277319 17392996747038471919915979)
            ·
              refine ⟨26089495120557707879873969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17392996747038471919915979 26089495120557707879873969)
              ·
                refine ⟨19567121340418280909905477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26089495120557707879873969 19567121340418280909905477)
                ·
                  refine ⟨3668835251328427670607277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19567121340418280909905477 3668835251328427670607277)
                  ·
                    refine ⟨1375813219248160376477729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3668835251328427670607277 1375813219248160376477729)
                    ·
                      rfl

theorem cell22_4019080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_4019080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019080 prefixEnd_4019080 := by exact prefixLift 4019080
  have htrace : WordTrace (prefixWord ++ tailWord_4019080) baseStart_4019080 baseEnd_4019080 := by
    simpa [prefixWord, tailWord_4019080, baseEnd_4019080] using wordTrace_append hprefix tailTrace_4019080
  have hstable : (prefixWord ++ tailWord_4019080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019080).length < 2 ^ (prefixWord ++ tailWord_4019080).sum := by decide
  have hdescent : baseEnd_4019080 < baseStart_4019080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019082 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_4019082 : Nat := 118140960795 + 4019082 * 2 ^ 59
def prefixEnd_4019082 : Nat := 4983230072969 + 3 ^ 40 * 4019082 * 2
def baseEnd_4019082 : Nat := 458604634629677679309241

theorem tailTrace_4019082 : CollatzResearch.WordTrace tailWord_4019082 prefixEnd_4019082 458604634629677679309241 := by
  unfold tailWord_4019082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646990806389948350812875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97725308817039862268834333 36646990806389948350812875)
  ·
    refine ⟨54970486209584922526219313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36646990806389948350812875 54970486209584922526219313)
    ·
      refine ⟨41227864657188691894664485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54970486209584922526219313 41227864657188691894664485)
      ·
        refine ⟨7730224623222879730249591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41227864657188691894664485 7730224623222879730249591)
        ·
          refine ⟨11595336934834319595374387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730224623222879730249591 11595336934834319595374387)
          ·
            refine ⟨17393005402251479393061581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595336934834319595374387 17393005402251479393061581)
            ·
              refine ⟨6522377025844304772398093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17393005402251479393061581 6522377025844304772398093)
              ·
                refine ⟨2445891384691614289649285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6522377025844304772398093 2445891384691614289649285)
                ·
                  refine ⟨458604634629677679309241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445891384691614289649285 458604634629677679309241)
                  ·
                    rfl

theorem cell22_4019082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_4019082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019082 prefixEnd_4019082 := by exact prefixLift 4019082
  have htrace : WordTrace (prefixWord ++ tailWord_4019082) baseStart_4019082 baseEnd_4019082 := by
    simpa [prefixWord, tailWord_4019082, baseEnd_4019082] using wordTrace_append hprefix tailTrace_4019082
  have hstable : (prefixWord ++ tailWord_4019082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019082).length < 2 ^ (prefixWord ++ tailWord_4019082).sum := by decide
  have hdescent : baseEnd_4019082 < baseStart_4019082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019093 : List Nat := [1, 3, 2, 1, 1, 6, 8]
def baseStart_4019093 : Nat := 118140960795 + 4019093 * 2 ^ 59
def prefixEnd_4019093 : Nat := 4983230072969 + 3 ^ 40 * 4019093 * 2
def baseEnd_4019093 : Nat := 50956209978290099107507

theorem tailTrace_4019093 : CollatzResearch.WordTrace tailWord_4019093 prefixEnd_4019093 50956209978290099107507 := by
  unfold tailWord_4019093
  simp only [CollatzResearch.WordTrace]
  refine ⟨146588364428519942281901933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97725576285679961521267955 146588364428519942281901933)
  ·
    refine ⟨54970636660694978355713225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146588364428519942281901933 54970636660694978355713225)
    ·
      refine ⟨41227977495521233766784919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54970636660694978355713225 41227977495521233766784919)
      ·
        refine ⟨61841966243281850650177379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41227977495521233766784919 61841966243281850650177379)
        ·
          refine ⟨92762949364922775975266069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61841966243281850650177379 92762949364922775975266069)
          ·
            refine ⟨4348263251480755123840597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92762949364922775975266069 4348263251480755123840597)
            ·
              refine ⟨50956209978290099107507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4348263251480755123840597 50956209978290099107507)
              ·
                rfl

theorem cell22_4019093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 8].length) (baseStart_4019093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019093 prefixEnd_4019093 := by exact prefixLift 4019093
  have htrace : WordTrace (prefixWord ++ tailWord_4019093) baseStart_4019093 baseEnd_4019093 := by
    simpa [prefixWord, tailWord_4019093, baseEnd_4019093] using wordTrace_append hprefix tailTrace_4019093
  have hstable : (prefixWord ++ tailWord_4019093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019093).length < 2 ^ (prefixWord ++ tailWord_4019093).sum := by decide
  have hdescent : baseEnd_4019093 < baseStart_4019093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019125 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4019125 : Nat := 118140960795 + 4019125 * 2 ^ 59
def prefixEnd_4019125 : Nat := 4983230072969 + 3 ^ 40 * 4019125 * 2
def baseEnd_4019125 : Nat := 1375828623667795259102591

theorem tailTrace_4019125 : CollatzResearch.WordTrace tailWord_4019125 prefixEnd_4019125 1375828623667795259102591 := by
  unfold tailWord_4019125
  simp only [CollatzResearch.WordTrace]
  refine ⟨146589531564404011747066829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97726354376269341164711219 146589531564404011747066829)
  ·
    refine ⟨54971074336651504405150061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146589531564404011747066829 54971074336651504405150061)
    ·
      refine ⟨20614152876244314151931273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54971074336651504405150061 20614152876244314151931273)
      ·
        refine ⟨15460614657183235613948455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20614152876244314151931273 15460614657183235613948455)
        ·
          refine ⟨23190921985774853420922683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460614657183235613948455 23190921985774853420922683)
          ·
            refine ⟨34786382978662280131384025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23190921985774853420922683 34786382978662280131384025)
            ·
              refine ⟨26089787233996710098538019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34786382978662280131384025 26089787233996710098538019)
              ·
                refine ⟨39134680850995065147807029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26089787233996710098538019 39134680850995065147807029)
                ·
                  refine ⟨3668876329780787357606909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39134680850995065147807029 3668876329780787357606909)
                  ·
                    refine ⟨1375828623667795259102591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3668876329780787357606909 1375828623667795259102591)
                    ·
                      rfl

theorem cell22_4019125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4019125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019125 prefixEnd_4019125 := by exact prefixLift 4019125
  have htrace : WordTrace (prefixWord ++ tailWord_4019125) baseStart_4019125 baseEnd_4019125 := by
    simpa [prefixWord, tailWord_4019125, baseEnd_4019125] using wordTrace_append hprefix tailTrace_4019125
  have hstable : (prefixWord ++ tailWord_4019125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019125).length < 2 ^ (prefixWord ++ tailWord_4019125).sum := by decide
  have hdescent : baseEnd_4019125 < baseStart_4019125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019153 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_4019153 : Nat := 118140960795 + 4019153 * 2 ^ 59
def prefixEnd_4019153 : Nat := 4983230072969 + 3 ^ 40 * 4019153 * 2
def baseEnd_4019153 : Nat := 1375838208640012519402505

theorem tailTrace_4019153 : CollatzResearch.WordTrace tailWord_4019153 prefixEnd_4019153 1375838208640012519402505 := by
  unfold tailWord_4019153
  simp only [CollatzResearch.WordTrace]
  refine ⟨146590552808302572529086113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97727035205535048352724075 146590552808302572529086113)
  ·
    refine ⟨109942914606226929396814585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146590552808302572529086113 109942914606226929396814585)
    ·
      refine ⟨82457185954670197047610939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109942914606226929396814585 82457185954670197047610939)
      ·
        refine ⟨123685778932005295571416409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82457185954670197047610939 123685778932005295571416409)
        ·
          refine ⟨92764334199003971678562307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123685778932005295571416409 92764334199003971678562307)
          ·
            refine ⟨139146501298505957517843461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92764334199003971678562307 139146501298505957517843461)
            ·
              refine ⟨26089968993469867034595649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139146501298505957517843461 26089968993469867034595649)
              ·
                refine ⟨19567476745102400275946737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26089968993469867034595649 19567476745102400275946737)
                ·
                  refine ⟨14675607558826800206960053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19567476745102400275946737 14675607558826800206960053)
                  ·
                    refine ⟨1375838208640012519402505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14675607558826800206960053 1375838208640012519402505)
                    ·
                      rfl

theorem cell22_4019153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_4019153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019153 prefixEnd_4019153 := by exact prefixLift 4019153
  have htrace : WordTrace (prefixWord ++ tailWord_4019153) baseStart_4019153 baseEnd_4019153 := by
    simpa [prefixWord, tailWord_4019153, baseEnd_4019153] using wordTrace_append hprefix tailTrace_4019153
  have hstable : (prefixWord ++ tailWord_4019153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019153).length < 2 ^ (prefixWord ++ tailWord_4019153).sum := by decide
  have hdescent : baseEnd_4019153 < baseStart_4019153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019183 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 8]
def baseStart_4019183 : Nat := 118140960795 + 4019183 * 2 ^ 59
def prefixEnd_4019183 : Nat := 4983230072969 + 3 ^ 40 * 4019183 * 2
def baseEnd_4019183 : Nat := 458616159417700813717471

theorem tailTrace_4019183 : CollatzResearch.WordTrace tailWord_4019183 prefixEnd_4019183 458616159417700813717471 := by
  unfold tailWord_4019183
  simp only [CollatzResearch.WordTrace]
  refine ⟨146591646998193887652678203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97727764665462591768452135 146591646998193887652678203)
  ·
    refine ⟨219887470497290831479017305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146591646998193887652678203 219887470497290831479017305)
    ·
      refine ⟨164915602872968123609262979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219887470497290831479017305 164915602872968123609262979)
      ·
        refine ⟨247373404309452185413894469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164915602872968123609262979 247373404309452185413894469)
        ·
          refine ⟨46382513308022284765105213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247373404309452185413894469 46382513308022284765105213)
          ·
            refine ⟨17393442490508356786914455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46382513308022284765105213 17393442490508356786914455)
            ·
              refine ⟨26090163735762535180371683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17393442490508356786914455 26090163735762535180371683)
              ·
                refine ⟨39135245603643802770557525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26090163735762535180371683 39135245603643802770557525)
                ·
                  refine ⟨458616159417700813717471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39135245603643802770557525 458616159417700813717471)
                  ·
                    rfl

theorem cell22_4019183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_4019183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019183 prefixEnd_4019183 := by exact prefixLift 4019183
  have htrace : WordTrace (prefixWord ++ tailWord_4019183) baseStart_4019183 baseEnd_4019183 := by
    simpa [prefixWord, tailWord_4019183, baseEnd_4019183] using wordTrace_append hprefix tailTrace_4019183
  have hstable : (prefixWord ++ tailWord_4019183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019183).length < 2 ^ (prefixWord ++ tailWord_4019183).sum := by decide
  have hdescent : baseEnd_4019183 < baseStart_4019183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019185 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_4019185 : Nat := 118140960795 + 4019185 * 2 ^ 59
def prefixEnd_4019185 : Nat := 4983230072969 + 3 ^ 40 * 4019185 * 2
def baseEnd_4019185 : Nat := 1375849162893975102602407

theorem tailTrace_4019185 : CollatzResearch.WordTrace tailWord_4019185 prefixEnd_4019185 1375849162893975102602407 := by
  unfold tailWord_4019185
  simp only [CollatzResearch.WordTrace]
  refine ⟨146591719944186641994251009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97727813296124427996167339 146591719944186641994251009)
  ·
    refine ⟨109943789958139981495688257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146591719944186641994251009 109943789958139981495688257)
    ·
      refine ⟨82457842468604986121766193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109943789958139981495688257 82457842468604986121766193)
      ·
        refine ⟨61843381851453739591324645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82457842468604986121766193 61843381851453739591324645)
        ·
          refine ⟨11595634097147576173373371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61843381851453739591324645 11595634097147576173373371)
          ·
            refine ⟨17393451145721364260060057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595634097147576173373371 17393451145721364260060057)
            ·
              refine ⟨13045088359291023195045043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17393451145721364260060057 13045088359291023195045043)
              ·
                refine ⟨19567632538936534792567565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13045088359291023195045043 19567632538936534792567565)
                ·
                  refine ⟨7337862202101200547212837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19567632538936534792567565 7337862202101200547212837)
                  ·
                    refine ⟨1375849162893975102602407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337862202101200547212837 1375849162893975102602407)
                    ·
                      rfl

theorem cell22_4019185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_4019185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019185 prefixEnd_4019185 := by exact prefixLift 4019185
  have htrace : WordTrace (prefixWord ++ tailWord_4019185) baseStart_4019185 baseEnd_4019185 := by
    simpa [prefixWord, tailWord_4019185, baseEnd_4019185] using wordTrace_append hprefix tailTrace_4019185
  have hstable : (prefixWord ++ tailWord_4019185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019185).length < 2 ^ (prefixWord ++ tailWord_4019185).sum := by decide
  have hdescent : baseEnd_4019185 < baseStart_4019185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019243 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_4019243 : Nat := 118140960795 + 4019243 * 2 ^ 59
def prefixEnd_4019243 : Nat := 4983230072969 + 3 ^ 40 * 4019243 * 2
def baseEnd_4019243 : Nat := 1375869017479282284652229

theorem tailTrace_4019243 : CollatzResearch.WordTrace tailWord_4019243 prefixEnd_4019243 1375869017479282284652229 := by
  unfold tailWord_4019243
  simp only [CollatzResearch.WordTrace]
  refine ⟨146593835377976517899862383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97729223585317678599908255 146593835377976517899862383)
  ·
    refine ⟨219890753066964776849793575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146593835377976517899862383 219890753066964776849793575)
    ·
      refine ⟨329836129600447165274690363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219890753066964776849793575 329836129600447165274690363)
      ·
        refine ⟨494754194400670747912035545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329836129600447165274690363 494754194400670747912035545)
        ·
          refine ⟨371065645800503060934026659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494754194400670747912035545 371065645800503060934026659)
          ·
            refine ⟨556598468700754591401039989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371065645800503060934026659 556598468700754591401039989)
            ·
              refine ⟨52181106440695742943847499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556598468700754591401039989 52181106440695742943847499)
              ·
                refine ⟨78271659661043614415771249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52181106440695742943847499 78271659661043614415771249)
                ·
                  refine ⟨58703744745782710811828437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78271659661043614415771249 58703744745782710811828437)
                  ·
                    refine ⟨1375869017479282284652229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58703744745782710811828437 1375869017479282284652229)
                    ·
                      rfl

theorem cell22_4019243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_4019243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019243 prefixEnd_4019243 := by exact prefixLift 4019243
  have htrace : WordTrace (prefixWord ++ tailWord_4019243) baseStart_4019243 baseEnd_4019243 := by
    simpa [prefixWord, tailWord_4019243, baseEnd_4019243] using wordTrace_append hprefix tailTrace_4019243
  have hstable : (prefixWord ++ tailWord_4019243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019243).length < 2 ^ (prefixWord ++ tailWord_4019243).sum := by decide
  have hdescent : baseEnd_4019243 < baseStart_4019243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019262 : List Nat := [4, 2, 1, 3, 1, 3, 8]
def baseStart_4019262 : Nat := 118140960795 + 4019262 * 2 ^ 59
def prefixEnd_4019262 : Nat := 4983230072969 + 3 ^ 40 * 4019262 * 2
def baseEnd_4019262 : Nat := 50958352650650835867673

theorem tailTrace_4019262 : CollatzResearch.WordTrace tailWord_4019262 prefixEnd_4019262 50958352650650835867673 := by
  unfold tailWord_4019262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18324316045613460518100505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97729685576605122763202693 18324316045613460518100505)
  ·
    refine ⟨13743237034210095388575379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18324316045613460518100505 13743237034210095388575379)
    ·
      refine ⟨20614855551315143082863069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13743237034210095388575379 20614855551315143082863069)
      ·
        refine ⟨7730570831743178656073651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20614855551315143082863069 7730570831743178656073651)
        ·
          refine ⟨11595856247614767984110477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730570831743178656073651 11595856247614767984110477)
          ·
            refine ⟨4348446092855537994041429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11595856247614767984110477 4348446092855537994041429)
            ·
              refine ⟨50958352650650835867673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4348446092855537994041429 50958352650650835867673)
              ·
                rfl

theorem cell22_4019262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 8].length) (baseStart_4019262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019262 prefixEnd_4019262 := by exact prefixLift 4019262
  have htrace : WordTrace (prefixWord ++ tailWord_4019262) baseStart_4019262 baseEnd_4019262 := by
    simpa [prefixWord, tailWord_4019262, baseEnd_4019262] using wordTrace_append hprefix tailTrace_4019262
  have hstable : (prefixWord ++ tailWord_4019262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019262).length < 2 ^ (prefixWord ++ tailWord_4019262).sum := by decide
  have hdescent : baseEnd_4019262 < baseStart_4019262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019335 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 6]
def baseStart_4019335 : Nat := 118140960795 + 4019335 * 2 ^ 59
def prefixEnd_4019335 : Nat := 4983230072969 + 3 ^ 40 * 4019335 * 2
def baseEnd_4019335 : Nat := 458633503653141570450649

theorem tailTrace_4019335 : CollatzResearch.WordTrace tailWord_4019335 prefixEnd_4019335 458633503653141570450649 := by
  unfold tailWord_4019335
  simp only [CollatzResearch.WordTrace]
  refine ⟨146597190893643217612211459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97731460595762145074807639 146597190893643217612211459)
  ·
    refine ⟨219895786340464826418317189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146597190893643217612211459 219895786340464826418317189)
    ·
      refine ⟨41230459938837154953434473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219895786340464826418317189 41230459938837154953434473)
      ·
        refine ⟨30922844954127866215075855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41230459938837154953434473 30922844954127866215075855)
        ·
          refine ⟨46384267431191799322613783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30922844954127866215075855 46384267431191799322613783)
          ·
            refine ⟨69576401146787698983920675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46384267431191799322613783 69576401146787698983920675)
            ·
              refine ⟨104364601720181548475881013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69576401146787698983920675 104364601720181548475881013)
              ·
                refine ⟨9784181411267020169613845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104364601720181548475881013 9784181411267020169613845)
                ·
                  refine ⟨458633503653141570450649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9784181411267020169613845 458633503653141570450649)
                  ·
                    rfl

theorem cell22_4019335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_4019335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019335 prefixEnd_4019335 := by exact prefixLift 4019335
  have htrace : WordTrace (prefixWord ++ tailWord_4019335) baseStart_4019335 baseEnd_4019335 := by
    simpa [prefixWord, tailWord_4019335, baseEnd_4019335] using wordTrace_append hprefix tailTrace_4019335
  have hstable : (prefixWord ++ tailWord_4019335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019335).length < 2 ^ (prefixWord ++ tailWord_4019335).sum := by decide
  have hdescent : baseEnd_4019335 < baseStart_4019335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019352 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_4019352 : Nat := 118140960795 + 4019352 * 2 ^ 59
def prefixEnd_4019352 : Nat := 4983230072969 + 3 ^ 40 * 4019352 * 2
def baseEnd_4019352 : Nat := 458635443468947444558965

theorem tailTrace_4019352 : CollatzResearch.WordTrace tailWord_4019352 prefixEnd_4019352 458635443468947444558965 := by
  unfold tailWord_4019352
  simp only [CollatzResearch.WordTrace]
  refine ⟨73298905467290814757790155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97731873956387753010386873 73298905467290814757790155)
  ·
    refine ⟨109948358200936222136685233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73298905467290814757790155 109948358200936222136685233)
    ·
      refine ⟨82461268650702166602513925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109948358200936222136685233 82461268650702166602513925)
      ·
        refine ⟨15461487872006656237971361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82461268650702166602513925 15461487872006656237971361)
        ·
          refine ⟨11596115904004992178478521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15461487872006656237971361 11596115904004992178478521)
          ·
            refine ⟨8697086928003744133858891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11596115904004992178478521 8697086928003744133858891)
            ·
              refine ⟨13045630392005616200788337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697086928003744133858891 13045630392005616200788337)
              ·
                refine ⟨9784222794004212150591253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045630392005616200788337 9784222794004212150591253)
                ·
                  refine ⟨458635443468947444558965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9784222794004212150591253 458635443468947444558965)
                  ·
                    rfl

theorem cell22_4019352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_4019352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019352 prefixEnd_4019352 := by exact prefixLift 4019352
  have htrace : WordTrace (prefixWord ++ tailWord_4019352) baseStart_4019352 baseEnd_4019352 := by
    simpa [prefixWord, tailWord_4019352, baseEnd_4019352] using wordTrace_append hprefix tailTrace_4019352
  have hstable : (prefixWord ++ tailWord_4019352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019352).length < 2 ^ (prefixWord ++ tailWord_4019352).sum := by decide
  have hdescent : baseEnd_4019352 < baseStart_4019352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019459 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 5]
def baseStart_4019459 : Nat := 118140960795 + 4019459 * 2 ^ 59
def prefixEnd_4019459 : Nat := 4983230072969 + 3 ^ 40 * 4019459 * 2
def baseEnd_4019459 : Nat := 458647652897843240417189

theorem tailTrace_4019459 : CollatzResearch.WordTrace tailWord_4019459 prefixEnd_4019459 458647652897843240417189 := by
  unfold tailWord_4019459
  simp only [CollatzResearch.WordTrace]
  refine ⟨146601713545193986789725431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97734475696795991193150287 146601713545193986789725431)
  ·
    refine ⟨219902570317790980184588147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146601713545193986789725431 219902570317790980184588147)
    ·
      refine ⟨329853855476686470276882221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219902570317790980184588147 329853855476686470276882221)
      ·
        refine ⟨123695195803757426353830833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329853855476686470276882221 123695195803757426353830833)
        ·
          refine ⟨92771396852818069765373125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123695195803757426353830833 92771396852818069765373125)
          ·
            refine ⟨17394636909903388081007461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92771396852818069765373125 17394636909903388081007461)
            ·
              refine ⟨3261494420606885265188899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17394636909903388081007461 3261494420606885265188899)
              ·
                refine ⟨4892241630910327897783349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261494420606885265188899 4892241630910327897783349)
                ·
                  refine ⟨458647652897843240417189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892241630910327897783349 458647652897843240417189)
                  ·
                    rfl

theorem cell22_4019459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 5].length) (baseStart_4019459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019459 prefixEnd_4019459 := by exact prefixLift 4019459
  have htrace : WordTrace (prefixWord ++ tailWord_4019459) baseStart_4019459 baseEnd_4019459 := by
    simpa [prefixWord, tailWord_4019459, baseEnd_4019459] using wordTrace_append hprefix tailTrace_4019459
  have hstable : (prefixWord ++ tailWord_4019459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019459).length < 2 ^ (prefixWord ++ tailWord_4019459).sum := by decide
  have hdescent : baseEnd_4019459 < baseStart_4019459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019504 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_4019504 : Nat := 118140960795 + 4019504 * 2 ^ 59
def prefixEnd_4019504 : Nat := 4983230072969 + 3 ^ 40 * 4019504 * 2
def baseEnd_4019504 : Nat := 458652787704388201292143

theorem tailTrace_4019504 : CollatzResearch.WordTrace tailWord_4019504 prefixEnd_4019504 458652787704388201292143 := by
  unfold tailWord_4019504
  simp only [CollatzResearch.WordTrace]
  refine ⟨73301677415015479737556783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97735569886687306316742377 73301677415015479737556783)
  ·
    refine ⟨109952516122523219606335175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73301677415015479737556783 109952516122523219606335175)
    ·
      refine ⟨164928774183784829409502763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109952516122523219606335175 164928774183784829409502763)
      ·
        refine ⟨247393161275677244114254145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164928774183784829409502763 247393161275677244114254145)
        ·
          refine ⟨185544870956757933085690609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247393161275677244114254145 185544870956757933085690609)
          ·
            refine ⟨139158653217568449814267957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185544870956757933085690609 139158653217568449814267957)
            ·
              refine ⟨13046123739147042170087621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139158653217568449814267957 13046123739147042170087621)
              ·
                refine ⟨2446148201090070406891429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13046123739147042170087621 2446148201090070406891429)
                ·
                  refine ⟨458652787704388201292143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446148201090070406891429 458652787704388201292143)
                  ·
                    rfl

theorem cell22_4019504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_4019504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019504 prefixEnd_4019504 := by exact prefixLift 4019504
  have htrace : WordTrace (prefixWord ++ tailWord_4019504) baseStart_4019504 baseEnd_4019504 := by
    simpa [prefixWord, tailWord_4019504, baseEnd_4019504] using wordTrace_append hprefix tailTrace_4019504
  have hstable : (prefixWord ++ tailWord_4019504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019504).length < 2 ^ (prefixWord ++ tailWord_4019504).sum := by decide
  have hdescent : baseEnd_4019504 < baseStart_4019504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019519 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 1, 5]
def baseStart_4019519 : Nat := 118140960795 + 4019519 * 2 ^ 59
def prefixEnd_4019519 : Nat := 4983230072969 + 3 ^ 40 * 4019519 * 2
def baseEnd_4019519 : Nat := 1375963497919709564751383

theorem tailTrace_4019519 : CollatzResearch.WordTrace tailWord_4019519 prefixEnd_4019519 1375963497919709564751383 := by
  unfold tailWord_4019519
  simp only [CollatzResearch.WordTrace]
  refine ⟨146603901924976617036909611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97735934616651078024606407 146603901924976617036909611)
  ·
    refine ⟨219905852887464925555364417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146603901924976617036909611 219905852887464925555364417)
    ·
      refine ⟨164929389665598694166523313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219905852887464925555364417 164929389665598694166523313)
      ·
        refine ⟨123697042249199020624892485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164929389665598694166523313 123697042249199020624892485)
        ·
          refine ⟨23193195421724816367167341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123697042249199020624892485 23193195421724816367167341)
          ·
            refine ⟨8697448283146806137687753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23193195421724816367167341 8697448283146806137687753)
            ·
              refine ⟨6523086212360104603265815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697448283146806137687753 6523086212360104603265815)
              ·
                refine ⟨9784629318540156904898723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523086212360104603265815 9784629318540156904898723)
                ·
                  refine ⟨14676943977810235357348085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784629318540156904898723 14676943977810235357348085)
                  ·
                    refine ⟨1375963497919709564751383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14676943977810235357348085 1375963497919709564751383)
                    ·
                      rfl

theorem cell22_4019519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_4019519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019519 prefixEnd_4019519 := by exact prefixLift 4019519
  have htrace : WordTrace (prefixWord ++ tailWord_4019519) baseStart_4019519 baseEnd_4019519 := by
    simpa [prefixWord, tailWord_4019519, baseEnd_4019519] using wordTrace_append hprefix tailTrace_4019519
  have hstable : (prefixWord ++ tailWord_4019519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019519).length < 2 ^ (prefixWord ++ tailWord_4019519).sum := by decide
  have hdescent : baseEnd_4019519 < baseStart_4019519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019615 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 1, 3]
def baseStart_4019615 : Nat := 118140960795 + 4019615 * 2 ^ 59
def prefixEnd_4019615 : Nat := 4983230072969 + 3 ^ 40 * 4019615 * 2
def baseEnd_4019615 : Nat := 1375996360681597314351089

theorem tailTrace_4019615 : CollatzResearch.WordTrace tailWord_4019615 prefixEnd_4019615 1375996360681597314351089 := by
  unfold tailWord_4019615
  simp only [CollatzResearch.WordTrace]
  refine ⟨146607403332628825432404299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97738268888419216954936199 146607403332628825432404299)
  ·
    refine ⟨219911104998943238148606449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146607403332628825432404299 219911104998943238148606449)
    ·
      refine ⟨164933328749207428611454837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219911104998943238148606449 164933328749207428611454837)
      ·
        refine ⟨15462499570238196432323891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164933328749207428611454837 15462499570238196432323891)
        ·
          refine ⟨23193749355357294648485837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462499570238196432323891 23193749355357294648485837)
          ·
            refine ⟨8697656008258985493182189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23193749355357294648485837 8697656008258985493182189)
            ·
              refine ⟨3261621003097119559943321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8697656008258985493182189 3261621003097119559943321)
              ·
                refine ⟨2446215752322839669957491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261621003097119559943321 2446215752322839669957491)
                ·
                  refine ⟨3669323628484259504936237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446215752322839669957491 3669323628484259504936237)
                  ·
                    refine ⟨1375996360681597314351089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3669323628484259504936237 1375996360681597314351089)
                    ·
                      rfl

theorem cell22_4019615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_4019615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019615 prefixEnd_4019615 := by exact prefixLift 4019615
  have htrace : WordTrace (prefixWord ++ tailWord_4019615) baseStart_4019615 baseEnd_4019615 := by
    simpa [prefixWord, tailWord_4019615, baseEnd_4019615] using wordTrace_append hprefix tailTrace_4019615
  have hstable : (prefixWord ++ tailWord_4019615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019615).length < 2 ^ (prefixWord ++ tailWord_4019615).sum := by decide
  have hdescent : baseEnd_4019615 < baseStart_4019615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019641 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_4019641 : Nat := 118140960795 + 4019641 * 2 ^ 59
def prefixEnd_4019641 : Nat := 4983230072969 + 3 ^ 40 * 4019641 * 2
def baseEnd_4019641 : Nat := 1376005261012941913201009

theorem tailTrace_4019641 : CollatzResearch.WordTrace tailWord_4019641 prefixEnd_4019641 1376005261012941913201009 := by
  unfold tailWord_4019641
  simp only [CollatzResearch.WordTrace]
  refine ⟨146608351630534631872850777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97738901087023087915233851 146608351630534631872850777)
  ·
    refine ⟨109956263722900973904638083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146608351630534631872850777 109956263722900973904638083)
    ·
      refine ⟨164934395584351460856957125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109956263722900973904638083 164934395584351460856957125)
      ·
        refine ⟨30925199172065898910679461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164934395584351460856957125 30925199172065898910679461)
        ·
          refine ⟨5798474844762356045752399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30925199172065898910679461 5798474844762356045752399)
          ·
            refine ⟨8697712267143534068628599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798474844762356045752399 8697712267143534068628599)
            ·
              refine ⟨13046568400715301102942899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697712267143534068628599 13046568400715301102942899)
              ·
                refine ⟨19569852601072951654414349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13046568400715301102942899 19569852601072951654414349)
                ·
                  refine ⟨7338694725402356870405381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19569852601072951654414349 7338694725402356870405381)
                  ·
                    refine ⟨1376005261012941913201009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7338694725402356870405381 1376005261012941913201009)
                    ·
                      rfl

theorem cell22_4019641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_4019641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019641 prefixEnd_4019641 := by exact prefixLift 4019641
  have htrace : WordTrace (prefixWord ++ tailWord_4019641) baseStart_4019641 baseEnd_4019641 := by
    simpa [prefixWord, tailWord_4019641, baseEnd_4019641] using wordTrace_append hprefix tailTrace_4019641
  have hstable : (prefixWord ++ tailWord_4019641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019641).length < 2 ^ (prefixWord ++ tailWord_4019641).sum := by decide
  have hdescent : baseEnd_4019641 < baseStart_4019641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019656 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_4019656 : Nat := 118140960795 + 4019656 * 2 ^ 59
def prefixEnd_4019656 : Nat := 4983230072969 + 3 ^ 40 * 4019656 * 2
def baseEnd_4019656 : Nat := 458670131939828958025321

theorem tailTrace_4019656 : CollatzResearch.WordTrace tailWord_4019656 prefixEnd_4019656 458670131939828958025321 := by
  unfold tailWord_4019656
  simp only [CollatzResearch.WordTrace]
  refine ⟨73304449362740144717323411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97739265816986859623097881 73304449362740144717323411)
  ·
    refine ⟨109956674044110217075985117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73304449362740144717323411 109956674044110217075985117)
    ·
      refine ⟨41233752766541331403494419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109956674044110217075985117 41233752766541331403494419)
      ·
        refine ⟨61850629149811997105241629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41233752766541331403494419 61850629149811997105241629)
        ·
          refine ⟨23193985931179498914465611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61850629149811997105241629 23193985931179498914465611)
          ·
            refine ⟨34790978896769248371698417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23193985931179498914465611 34790978896769248371698417)
            ·
              refine ⟨26093234172576936278773813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34790978896769248371698417 26093234172576936278773813)
              ·
                refine ⟨2446240703679087776135045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26093234172576936278773813 2446240703679087776135045)
                ·
                  refine ⟨458670131939828958025321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446240703679087776135045 458670131939828958025321)
                  ·
                    rfl

theorem cell22_4019656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_4019656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019656 prefixEnd_4019656 := by exact prefixLift 4019656
  have htrace : WordTrace (prefixWord ++ tailWord_4019656) baseStart_4019656 baseEnd_4019656 := by
    simpa [prefixWord, tailWord_4019656, baseEnd_4019656] using wordTrace_append hprefix tailTrace_4019656
  have hstable : (prefixWord ++ tailWord_4019656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019656).length < 2 ^ (prefixWord ++ tailWord_4019656).sum := by decide
  have hdescent : baseEnd_4019656 < baseStart_4019656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019658 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_4019658 : Nat := 118140960795 + 4019658 * 2 ^ 59
def prefixEnd_4019658 : Nat := 4983230072969 + 3 ^ 40 * 4019658 * 2
def baseEnd_4019658 : Nat := 1376011080460359535525957

theorem tailTrace_4019658 : CollatzResearch.WordTrace tailWord_4019658 prefixEnd_4019658 1376011080460359535525957 := by
  unfold tailWord_4019658
  simp only [CollatzResearch.WordTrace]
  refine ⟨36652242917868260944054907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97739314447648695850813085 36652242917868260944054907)
  ·
    refine ⟨54978364376802391416082361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36652242917868260944054907 54978364376802391416082361)
    ·
      refine ⟨41233773282601793562061771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54978364376802391416082361 41233773282601793562061771)
      ·
        refine ⟨61850659923902690343092657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41233773282601793562061771 61850659923902690343092657)
        ·
          refine ⟨46387994942927017757319493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61850659923902690343092657 46387994942927017757319493)
          ·
            refine ⟨8697749051798815829497405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46387994942927017757319493 8697749051798815829497405)
            ·
              refine ⟨3261655894424555936061527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8697749051798815829497405 3261655894424555936061527)
              ·
                refine ⟨4892483841636833904092291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261655894424555936061527 4892483841636833904092291)
                ·
                  refine ⟨7338725762455250856138437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892483841636833904092291 7338725762455250856138437)
                  ·
                    refine ⟨1376011080460359535525957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7338725762455250856138437 1376011080460359535525957)
                    ·
                      rfl

theorem cell22_4019658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_4019658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019658 prefixEnd_4019658 := by exact prefixLift 4019658
  have htrace : WordTrace (prefixWord ++ tailWord_4019658) baseStart_4019658 baseEnd_4019658 := by
    simpa [prefixWord, tailWord_4019658, baseEnd_4019658] using wordTrace_append hprefix tailTrace_4019658
  have hstable : (prefixWord ++ tailWord_4019658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019658).length < 2 ^ (prefixWord ++ tailWord_4019658).sum := by decide
  have hdescent : baseEnd_4019658 < baseStart_4019658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019673 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 4]
def baseStart_4019673 : Nat := 118140960795 + 4019673 * 2 ^ 59
def prefixEnd_4019673 : Nat := 4983230072969 + 3 ^ 40 * 4019673 * 2
def baseEnd_4019673 : Nat := 458672071755634832133637

theorem tailTrace_4019673 : CollatzResearch.WordTrace tailWord_4019673 prefixEnd_4019673 458672071755634832133637 := by
  unfold tailWord_4019673
  simp only [CollatzResearch.WordTrace]
  refine ⟨146609518766418701338015673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97739679177612467558677115 146609518766418701338015673)
  ·
    refine ⟨109957139074814026003511755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146609518766418701338015673 109957139074814026003511755)
    ·
      refine ⟨164935708612221039005267633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109957139074814026003511755 164935708612221039005267633)
      ·
        refine ⟨123701781459165779253950725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164935708612221039005267633 123701781459165779253950725)
        ·
          refine ⟨23194084023593583610115761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123701781459165779253950725 23194084023593583610115761)
          ·
            refine ⟨17395563017695187707586821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23194084023593583610115761 17395563017695187707586821)
            ·
              refine ⟨3261668065817847695172529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17395563017695187707586821 3261668065817847695172529)
              ·
                refine ⟨2446251049363385771379397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261668065817847695172529 2446251049363385771379397)
                ·
                  refine ⟨458672071755634832133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446251049363385771379397 458672071755634832133637)
                  ·
                    rfl

theorem cell22_4019673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_4019673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019673 prefixEnd_4019673 := by exact prefixLift 4019673
  have htrace : WordTrace (prefixWord ++ tailWord_4019673) baseStart_4019673 baseEnd_4019673 := by
    simpa [prefixWord, tailWord_4019673, baseEnd_4019673] using wordTrace_append hprefix tailTrace_4019673
  have hstable : (prefixWord ++ tailWord_4019673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019673).length < 2 ^ (prefixWord ++ tailWord_4019673).sum := by decide
  have hdescent : baseEnd_4019673 < baseStart_4019673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019729 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 7]
def baseStart_4019729 : Nat := 118140960795 + 4019729 * 2 ^ 59
def prefixEnd_4019729 : Nat := 4983230072969 + 3 ^ 40 * 4019729 * 2
def baseEnd_4019729 : Nat := 458678461737113005666913

theorem tailTrace_4019729 : CollatzResearch.WordTrace tailWord_4019729 prefixEnd_4019729 458678461737113005666913 := by
  unfold tailWord_4019729
  simp only [CollatzResearch.WordTrace]
  refine ⟨146611561254215822902054241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97741040836143881934702827 146611561254215822902054241)
  ·
    refine ⟨109958670940661867176540681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146611561254215822902054241 109958670940661867176540681)
    ·
      refine ⟨82469003205496400382405511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109958670940661867176540681 82469003205496400382405511)
      ·
        refine ⟨123703504808244600573608267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82469003205496400382405511 123703504808244600573608267)
        ·
          refine ⟨185555257212366900860412401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123703504808244600573608267 185555257212366900860412401)
          ·
            refine ⟨139166442909275175645309301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185555257212366900860412401 139166442909275175645309301)
            ·
              refine ⟨13046854022744547716747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139166442909275175645309301 13046854022744547716747747)
              ·
                refine ⟨19570281034116821575121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13046854022744547716747747 19570281034116821575121621)
                ·
                  refine ⟨458678461737113005666913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19570281034116821575121621 458678461737113005666913)
                  ·
                    rfl

theorem cell22_4019729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_4019729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019729 prefixEnd_4019729 := by exact prefixLift 4019729
  have htrace : WordTrace (prefixWord ++ tailWord_4019729) baseStart_4019729 baseEnd_4019729 := by
    simpa [prefixWord, tailWord_4019729, baseEnd_4019729] using wordTrace_append hprefix tailTrace_4019729
  have hstable : (prefixWord ++ tailWord_4019729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019729).length < 2 ^ (prefixWord ++ tailWord_4019729).sum := by decide
  have hdescent : baseEnd_4019729 < baseStart_4019729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019733 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_4019733 : Nat := 118140960795 + 4019733 * 2 ^ 59
def prefixEnd_4019733 : Nat := 4983230072969 + 3 ^ 40 * 4019733 * 2
def baseEnd_4019733 : Nat := 1376036754493084339900727

theorem tailTrace_4019733 : CollatzResearch.WordTrace tailWord_4019733 prefixEnd_4019733 1376036754493084339900727 := by
  unfold tailWord_4019733
  simp only [CollatzResearch.WordTrace]
  refine ⟨146611707146201331585199853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97741138097467554390133235 146611707146201331585199853)
  ·
    refine ⟨54979390179825499344449945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146611707146201331585199853 54979390179825499344449945)
    ·
      refine ⟨41234542634869124508337459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54979390179825499344449945 41234542634869124508337459)
      ·
        refine ⟨61851813952303686762506189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41234542634869124508337459 61851813952303686762506189)
        ·
          refine ⟨23194430232113882535939821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61851813952303686762506189 23194430232113882535939821)
          ·
            refine ⟨8697911337042705950977433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23194430232113882535939821 8697911337042705950977433)
            ·
              refine ⟨6523433502782029463233075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697911337042705950977433 6523433502782029463233075)
              ·
                refine ⟨9785150254173044194849613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523433502782029463233075 9785150254173044194849613)
                ·
                  refine ⟨3669431345314891573068605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9785150254173044194849613 3669431345314891573068605)
                  ·
                    refine ⟨1376036754493084339900727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3669431345314891573068605 1376036754493084339900727)
                    ·
                      rfl

theorem cell22_4019733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_4019733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019733 prefixEnd_4019733 := by exact prefixLift 4019733
  have htrace : WordTrace (prefixWord ++ tailWord_4019733) baseStart_4019733 baseEnd_4019733 := by
    simpa [prefixWord, tailWord_4019733, baseEnd_4019733] using wordTrace_append hprefix tailTrace_4019733
  have hstable : (prefixWord ++ tailWord_4019733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019733).length < 2 ^ (prefixWord ++ tailWord_4019733).sum := by decide
  have hdescent : baseEnd_4019733 < baseStart_4019733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019746 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4019746 : Nat := 118140960795 + 4019746 * 2 ^ 59
def prefixEnd_4019746 : Nat := 4983230072969 + 3 ^ 40 * 4019746 * 2
def baseEnd_4019746 : Nat := 458680401552918879775229

theorem tailTrace_4019746 : CollatzResearch.WordTrace tailWord_4019746 prefixEnd_4019746 458680401552918879775229 := by
  unfold tailWord_4019746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36653045323788558701355773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97741454196769489870282061 36653045323788558701355773)
  ·
    refine ⟨13744891996420709513008415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36653045323788558701355773 13744891996420709513008415)
    ·
      refine ⟨20617337994631064269512623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13744891996420709513008415 20617337994631064269512623)
      ·
        refine ⟨30926006991946596404268935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20617337994631064269512623 30926006991946596404268935)
        ·
          refine ⟨46389010487919894606403403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30926006991946596404268935 46389010487919894606403403)
          ·
            refine ⟨69583515731879841909605105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46389010487919894606403403 69583515731879841909605105)
            ·
              refine ⟨52187636798909881432203829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69583515731879841909605105 52187636798909881432203829)
              ·
                refine ⟨4892590949897801384269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52187636798909881432203829 4892590949897801384269109)
                ·
                  refine ⟨458680401552918879775229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892590949897801384269109 458680401552918879775229)
                  ·
                    rfl

theorem cell22_4019746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4019746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019746 prefixEnd_4019746 := by exact prefixLift 4019746
  have htrace : WordTrace (prefixWord ++ tailWord_4019746) baseStart_4019746 baseEnd_4019746 := by
    simpa [prefixWord, tailWord_4019746, baseEnd_4019746] using wordTrace_append hprefix tailTrace_4019746
  have hstable : (prefixWord ++ tailWord_4019746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019746).length < 2 ^ (prefixWord ++ tailWord_4019746).sum := by decide
  have hdescent : baseEnd_4019746 < baseStart_4019746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019870 : List Nat := [4, 3, 1, 1, 1, 3, 3, 6]
def baseStart_4019870 : Nat := 118140960795 + 4019870 * 2 ^ 59
def prefixEnd_4019870 : Nat := 4983230072969 + 3 ^ 40 * 4019870 * 2
def baseEnd_4019870 : Nat := 152898183599206849913923

theorem tailTrace_4019870 : CollatzResearch.WordTrace tailWord_4019870 prefixEnd_4019870 152898183599206849913923 := by
  unfold tailWord_4019870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327087993338125497867133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97744469297803335988624709 18327087993338125497867133)
  ·
    refine ⟨6872657997501797061700175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18327087993338125497867133 6872657997501797061700175)
    ·
      refine ⟨10308986996252695592550263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872657997501797061700175 10308986996252695592550263)
      ·
        refine ⟨15463480494379043388825395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308986996252695592550263 15463480494379043388825395)
        ·
          refine ⟨23195220741568565083238093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15463480494379043388825395 23195220741568565083238093)
          ·
            refine ⟨8698207778088211906214285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23195220741568565083238093 8698207778088211906214285)
            ·
              refine ⟨3261827916783079464830357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8698207778088211906214285 3261827916783079464830357)
              ·
                refine ⟨152898183599206849913923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3261827916783079464830357 152898183599206849913923)
                ·
                  rfl

theorem cell22_4019870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_4019870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019870 prefixEnd_4019870 := by exact prefixLift 4019870
  have htrace : WordTrace (prefixWord ++ tailWord_4019870) baseStart_4019870 baseEnd_4019870 := by
    simpa [prefixWord, tailWord_4019870, baseEnd_4019870] using wordTrace_append hprefix tailTrace_4019870
  have hstable : (prefixWord ++ tailWord_4019870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019870).length < 2 ^ (prefixWord ++ tailWord_4019870).sum := by decide
  have hdescent : baseEnd_4019870 < baseStart_4019870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019898 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_4019898 : Nat := 118140960795 + 4019898 * 2 ^ 59
def prefixEnd_4019898 : Nat := 4983230072969 + 3 ^ 40 * 4019898 * 2
def baseEnd_4019898 : Nat := 458697745788359636508407

theorem tailTrace_4019898 : CollatzResearch.WordTrace tailWord_4019898 prefixEnd_4019898 458697745788359636508407 := by
  unfold tailWord_4019898
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654431297650891191239087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97745150127069043176637565 36654431297650891191239087)
  ·
    refine ⟨54981646946476336786858631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36654431297650891191239087 54981646946476336786858631)
    ·
      refine ⟨82472470419714505180287947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54981646946476336786858631 82472470419714505180287947)
      ·
        refine ⟨123708705629571757770431921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82472470419714505180287947 123708705629571757770431921)
        ·
          refine ⟨92781529222178818327823941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123708705629571757770431921 92781529222178818327823941)
          ·
            refine ⟨17396536729158528436466989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92781529222178818327823941 17396536729158528436466989)
            ·
              refine ⟨6523701273434448163675121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17396536729158528436466989 6523701273434448163675121)
              ·
                refine ⟨4892775955075836122756341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523701273434448163675121 4892775955075836122756341)
                ·
                  refine ⟨458697745788359636508407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892775955075836122756341 458697745788359636508407)
                  ·
                    rfl

theorem cell22_4019898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_4019898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019898 prefixEnd_4019898 := by exact prefixLift 4019898
  have htrace : WordTrace (prefixWord ++ tailWord_4019898) baseStart_4019898 baseEnd_4019898 := by
    simpa [prefixWord, tailWord_4019898, baseEnd_4019898] using wordTrace_append hprefix tailTrace_4019898
  have hstable : (prefixWord ++ tailWord_4019898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019898).length < 2 ^ (prefixWord ++ tailWord_4019898).sum := by decide
  have hdescent : baseEnd_4019898 < baseStart_4019898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019902 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4019902 : Nat := 118140960795 + 4019902 * 2 ^ 59
def prefixEnd_4019902 : Nat := 4983230072969 + 3 ^ 40 * 4019902 * 2
def baseEnd_4019902 : Nat := 1376094606646824232425209

theorem tailTrace_4019902 : CollatzResearch.WordTrace tailWord_4019902 prefixEnd_4019902 1376094606646824232425209 := by
  unfold tailWord_4019902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327233885323634181012745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97745247388392715632067973 18327233885323634181012745)
  ·
    refine ⟨13745425413992725635759559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18327233885323634181012745 13745425413992725635759559)
    ·
      refine ⟨20618138120989088453639339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13745425413992725635759559 20618138120989088453639339)
      ·
        refine ⟨30927207181483632680459009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618138120989088453639339 30927207181483632680459009)
        ·
          refine ⟨23195405386112724510344257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30927207181483632680459009 23195405386112724510344257)
          ·
            refine ⟨17396554039584543382758193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23195405386112724510344257 17396554039584543382758193)
            ·
              refine ⟨13047415529688407537068645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17396554039584543382758193 13047415529688407537068645)
              ·
                refine ⟨2446390411816576413200371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13047415529688407537068645 2446390411816576413200371)
                ·
                  refine ⟨3669585617724864619800557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446390411816576413200371 3669585617724864619800557)
                  ·
                    refine ⟨1376094606646824232425209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3669585617724864619800557 1376094606646824232425209)
                    ·
                      rfl

theorem cell22_4019902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4019902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019902 prefixEnd_4019902 := by exact prefixLift 4019902
  have htrace : WordTrace (prefixWord ++ tailWord_4019902) baseStart_4019902 baseEnd_4019902 := by
    simpa [prefixWord, tailWord_4019902, baseEnd_4019902] using wordTrace_append hprefix tailTrace_4019902
  have hstable : (prefixWord ++ tailWord_4019902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019902).length < 2 ^ (prefixWord ++ tailWord_4019902).sum := by decide
  have hdescent : baseEnd_4019902 < baseStart_4019902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4019971 : List Nat := [1, 1, 1, 3, 2, 2, 3, 9]
def baseStart_4019971 : Nat := 118140960795 + 4019971 * 2 ^ 59
def prefixEnd_4019971 : Nat := 4983230072969 + 3 ^ 40 * 4019971 * 2
def baseEnd_4019971 : Nat := 152902025195214561383333

theorem tailTrace_4019971 : CollatzResearch.WordTrace tailWord_4019971 prefixEnd_4019971 152902025195214561383333 := by
  unfold tailWord_4019971
  simp only [CollatzResearch.WordTrace]
  refine ⟨146620387719339098232363767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97746925146226065488242511 146620387719339098232363767)
  ·
    refine ⟨219930581579008647348545651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146620387719339098232363767 219930581579008647348545651)
    ·
      refine ⟨329895872368512971022818477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219930581579008647348545651 329895872368512971022818477)
      ·
        refine ⟨123710952138192364133556929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329895872368512971022818477 123710952138192364133556929)
        ·
          refine ⟨92783214103644273100167697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123710952138192364133556929 92783214103644273100167697)
          ·
            refine ⟨69587410577733204825125773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92783214103644273100167697 69587410577733204825125773)
            ·
              refine ⟨26095278966649951809422165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69587410577733204825125773 26095278966649951809422165)
              ·
                refine ⟨152902025195214561383333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26095278966649951809422165 152902025195214561383333)
                ·
                  rfl

theorem cell22_4019971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 9].length) (baseStart_4019971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4019971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4019971 prefixEnd_4019971 := by exact prefixLift 4019971
  have htrace : WordTrace (prefixWord ++ tailWord_4019971) baseStart_4019971 baseEnd_4019971 := by
    simpa [prefixWord, tailWord_4019971, baseEnd_4019971] using wordTrace_append hprefix tailTrace_4019971
  have hstable : (prefixWord ++ tailWord_4019971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4019971).length < 2 ^ (prefixWord ++ tailWord_4019971).sum := by decide
  have hdescent : baseEnd_4019971 < baseStart_4019971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4019971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020018 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_4020018 : Nat := 118140960795 + 4020018 * 2 ^ 59
def prefixEnd_4020018 : Nat := 4983230072969 + 3 ^ 40 * 4020018 * 2
def baseEnd_4020018 : Nat := 1376134315817438596524853

theorem tailTrace_4020018 : CollatzResearch.WordTrace tailWord_4020018 prefixEnd_4020018 1376134315817438596524853 := by
  unfold tailWord_4020018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36655525487542206314831177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97748067966779216839549805 36655525487542206314831177)
  ·
    refine ⟨27491644115656654736123383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36655525487542206314831177 27491644115656654736123383)
    ·
      refine ⟨41237466173484982104185075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27491644115656654736123383 41237466173484982104185075)
      ·
        refine ⟨61856199260227473156277613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41237466173484982104185075 61856199260227473156277613)
        ·
          refine ⟨23196074722585302433604105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61856199260227473156277613 23196074722585302433604105)
          ·
            refine ⟨17397056041938976825203079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23196074722585302433604105 17397056041938976825203079)
            ·
              refine ⟨26095584062908465237804619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17397056041938976825203079 26095584062908465237804619)
              ·
                refine ⟨39143376094362697856706929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26095584062908465237804619 39143376094362697856706929)
                ·
                  refine ⟨29357532070772023392530197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39143376094362697856706929 29357532070772023392530197)
                  ·
                    refine ⟨1376134315817438596524853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29357532070772023392530197 1376134315817438596524853)
                    ·
                      rfl

theorem cell22_4020018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_4020018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020018 prefixEnd_4020018 := by exact prefixLift 4020018
  have htrace : WordTrace (prefixWord ++ tailWord_4020018) baseStart_4020018 baseEnd_4020018 := by
    simpa [prefixWord, tailWord_4020018, baseEnd_4020018] using wordTrace_append hprefix tailTrace_4020018
  have hstable : (prefixWord ++ tailWord_4020018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020018).length < 2 ^ (prefixWord ++ tailWord_4020018).sum := by decide
  have hdescent : baseEnd_4020018 < baseStart_4020018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020022 : List Nat := [5, 1, 2, 2, 1, 3, 1, 7]
def baseStart_4020022 : Nat := 118140960795 + 4020022 * 2 ^ 59
def prefixEnd_4020022 : Nat := 4983230072969 + 3 ^ 40 * 4020022 * 2
def baseEnd_4020022 : Nat := 152903965011020435491649

theorem tailTrace_4020022 : CollatzResearch.WordTrace tailWord_4020022 prefixEnd_4020022 152903965011020435491649 := by
  unfold tailWord_4020022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163890490134645871404395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97748165228102889294980213 9163890490134645871404395)
  ·
    refine ⟨13745835735201968807106593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9163890490134645871404395 13745835735201968807106593)
    ·
      refine ⟨10309376801401476605329945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13745835735201968807106593 10309376801401476605329945)
      ·
        refine ⟨7732032601051107453997459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10309376801401476605329945 7732032601051107453997459)
        ·
          refine ⟨11598048901576661180996189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732032601051107453997459 11598048901576661180996189)
          ·
            refine ⟨4349268338091247942873571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11598048901576661180996189 4349268338091247942873571)
            ·
              refine ⟨6523902507136871914310357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349268338091247942873571 6523902507136871914310357)
              ·
                refine ⟨152903965011020435491649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6523902507136871914310357 152903965011020435491649)
                ·
                  rfl

theorem cell22_4020022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_4020022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020022 prefixEnd_4020022 := by exact prefixLift 4020022
  have htrace : WordTrace (prefixWord ++ tailWord_4020022) baseStart_4020022 baseEnd_4020022 := by
    simpa [prefixWord, tailWord_4020022, baseEnd_4020022] using wordTrace_append hprefix tailTrace_4020022
  have hstable : (prefixWord ++ tailWord_4020022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020022).length < 2 ^ (prefixWord ++ tailWord_4020022).sum := by decide
  have hdescent : baseEnd_4020022 < baseStart_4020022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020067 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 5]
def baseStart_4020067 : Nat := 118140960795 + 4020067 * 2 ^ 59
def prefixEnd_4020067 : Nat := 4983230072969 + 3 ^ 40 * 4020067 * 2
def baseEnd_4020067 : Nat := 458717029839606267349901

theorem tailTrace_4020067 : CollatzResearch.WordTrace tailWord_4020067 prefixEnd_4020067 458717029839606267349901 := by
  unfold tailWord_4020067
  simp only [CollatzResearch.WordTrace]
  refine ⟨146623889126991306627858455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97749259417994204418572303 146623889126991306627858455)
  ·
    refine ⟨219935833690486959941787683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146623889126991306627858455 219935833690486959941787683)
    ·
      refine ⟨329903750535730439912681525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219935833690486959941787683 329903750535730439912681525)
      ·
        refine ⟨30928476612724728741813893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329903750535730439912681525 30928476612724728741813893)
        ·
          refine ⟨5799089364885886639090105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30928476612724728741813893 5799089364885886639090105)
          ·
            refine ⟨4349317023664414979317579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799089364885886639090105 4349317023664414979317579)
            ·
              refine ⟨6523975535496622468976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349317023664414979317579 6523975535496622468976369)
              ·
                refine ⟨4892981651622466851732277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523975535496622468976369 4892981651622466851732277)
                ·
                  refine ⟨458717029839606267349901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892981651622466851732277 458717029839606267349901)
                  ·
                    rfl

theorem cell22_4020067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 5].length) (baseStart_4020067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020067 prefixEnd_4020067 := by exact prefixLift 4020067
  have htrace : WordTrace (prefixWord ++ tailWord_4020067) baseStart_4020067 baseEnd_4020067 := by
    simpa [prefixWord, tailWord_4020067, baseEnd_4020067] using wordTrace_append hprefix tailTrace_4020067
  have hstable : (prefixWord ++ tailWord_4020067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020067).length < 2 ^ (prefixWord ++ tailWord_4020067).sum := by decide
  have hdescent : baseEnd_4020067 < baseStart_4020067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020125 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4020125 : Nat := 118140960795 + 4020125 * 2 ^ 59
def prefixEnd_4020125 : Nat := 4983230072969 + 3 ^ 40 * 4020125 * 2
def baseEnd_4020125 : Nat := 1376170944104125984099525

theorem tailTrace_4020125 : CollatzResearch.WordTrace tailWord_4020125 prefixEnd_4020125 1376170944104125984099525 := by
  unfold tailWord_4020125
  simp only [CollatzResearch.WordTrace]
  refine ⟨146626004560781182533469829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97750669707187455022313219 146626004560781182533469829)
  ·
    refine ⟨27492375855146471725025593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146626004560781182533469829 27492375855146471725025593)
    ·
      refine ⟨20619281891359853793769195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27492375855146471725025593 20619281891359853793769195)
      ·
        refine ⟨30928922837039780690653793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20619281891359853793769195 30928922837039780690653793)
        ·
          refine ⟨23196692127779835517990345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30928922837039780690653793 23196692127779835517990345)
          ·
            refine ⟨17397519095834876638492759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23196692127779835517990345 17397519095834876638492759)
            ·
              refine ⟨26096278643752314957739139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17397519095834876638492759 26096278643752314957739139)
              ·
                refine ⟨39144417965628472436608709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26096278643752314957739139 39144417965628472436608709)
                ·
                  refine ⟨7339578368555338581864133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39144417965628472436608709 7339578368555338581864133)
                  ·
                    refine ⟨1376170944104125984099525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7339578368555338581864133 1376170944104125984099525)
                    ·
                      rfl

theorem cell22_4020125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4020125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020125 prefixEnd_4020125 := by exact prefixLift 4020125
  have htrace : WordTrace (prefixWord ++ tailWord_4020125) baseStart_4020125 baseEnd_4020125 := by
    simpa [prefixWord, tailWord_4020125, baseEnd_4020125] using wordTrace_append hprefix tailTrace_4020125
  have hstable : (prefixWord ++ tailWord_4020125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020125).length < 2 ^ (prefixWord ++ tailWord_4020125).sum := by decide
  have hdescent : baseEnd_4020125 < baseStart_4020125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020129 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 6]
def baseStart_4020129 : Nat := 118140960795 + 4020129 * 2 ^ 59
def prefixEnd_4020129 : Nat := 4983230072969 + 3 ^ 40 * 4020129 * 2
def baseEnd_4020129 : Nat := 458724104461957102333171

theorem tailTrace_4020129 : CollatzResearch.WordTrace tailWord_4020129 prefixEnd_4020129 458724104461957102333171 := by
  unfold tailWord_4020129
  simp only [CollatzResearch.WordTrace]
  refine ⟨146626150452766691216615441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97750766968511127477743627 146626150452766691216615441)
  ·
    refine ⟨109969612839575018412461581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146626150452766691216615441 109969612839575018412461581)
    ·
      refine ⟨41238604814840631904673093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109969612839575018412461581 41238604814840631904673093)
      ·
        refine ⟨7732238402782618482126205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41238604814840631904673093 7732238402782618482126205)
        ·
          refine ⟨2899589401043481930797327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7732238402782618482126205 2899589401043481930797327)
          ·
            refine ⟨4349384101565222896195991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899589401043481930797327 4349384101565222896195991)
            ·
              refine ⟨6524076152347834344293987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349384101565222896195991 6524076152347834344293987)
              ·
                refine ⟨9786114228521751516440981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524076152347834344293987 9786114228521751516440981)
                ·
                  refine ⟨458724104461957102333171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9786114228521751516440981 458724104461957102333171)
                  ·
                    rfl

theorem cell22_4020129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_4020129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020129 prefixEnd_4020129 := by exact prefixLift 4020129
  have htrace : WordTrace (prefixWord ++ tailWord_4020129) baseStart_4020129 baseEnd_4020129 := by
    simpa [prefixWord, tailWord_4020129, baseEnd_4020129] using wordTrace_append hprefix tailTrace_4020129
  have hstable : (prefixWord ++ tailWord_4020129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020129).length < 2 ^ (prefixWord ++ tailWord_4020129).sum := by decide
  have hdescent : baseEnd_4020129 < baseStart_4020129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020148 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4020148 : Nat := 118140960795 + 4020148 * 2 ^ 59
def prefixEnd_4020148 : Nat := 4983230072969 + 3 ^ 40 * 4020148 * 2
def baseEnd_4020148 : Nat := 1376178817474161590774455

theorem tailTrace_4020148 : CollatzResearch.WordTrace tailWord_4020148 prefixEnd_4020148 1376178817474161590774455 := by
  unfold tailWord_4020148
  simp only [CollatzResearch.WordTrace]
  refine ⟨73313421719848928730778549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97751228959798571641038065 73313421719848928730778549)
  ·
    refine ⟨6873133286235837068510489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73313421719848928730778549 6873133286235837068510489)
    ·
      refine ⟨5154849964676877801382867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6873133286235837068510489 5154849964676877801382867)
      ·
        refine ⟨7732274947015316702074301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154849964676877801382867 7732274947015316702074301)
        ·
          refine ⟨2899603105130743763277863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7732274947015316702074301 2899603105130743763277863)
          ·
            refine ⟨4349404657696115644916795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899603105130743763277863 4349404657696115644916795)
            ·
              refine ⟨6524106986544173467375193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349404657696115644916795 6524106986544173467375193)
              ·
                refine ⟨4893080239908130100531395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524106986544173467375193 4893080239908130100531395)
                ·
                  refine ⟨7339620359862195150797093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893080239908130100531395 7339620359862195150797093)
                  ·
                    refine ⟨1376178817474161590774455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7339620359862195150797093 1376178817474161590774455)
                    ·
                      rfl

theorem cell22_4020148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4020148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020148 prefixEnd_4020148 := by exact prefixLift 4020148
  have htrace : WordTrace (prefixWord ++ tailWord_4020148) baseStart_4020148 baseEnd_4020148 := by
    simpa [prefixWord, tailWord_4020148, baseEnd_4020148] using wordTrace_append hprefix tailTrace_4020148
  have hstable : (prefixWord ++ tailWord_4020148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020148).length < 2 ^ (prefixWord ++ tailWord_4020148).sum := by decide
  have hdescent : baseEnd_4020148 < baseStart_4020148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020232 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4020232 : Nat := 118140960795 + 4020232 * 2 ^ 59
def prefixEnd_4020232 : Nat := 4983230072969 + 3 ^ 40 * 4020232 * 2
def baseEnd_4020232 : Nat := 1376207572390813371674197

theorem tailTrace_4020232 : CollatzResearch.WordTrace tailWord_4020232 prefixEnd_4020232 1376207572390813371674197 := by
  unfold tailWord_4020232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73314953585696769903807475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97753271447595693205076633 73314953585696769903807475)
  ·
    refine ⟨109972430378545154855711213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73314953585696769903807475 109972430378545154855711213)
    ·
      refine ⟨41239661391954433070891705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109972430378545154855711213 41239661391954433070891705)
      ·
        refine ⟨30929746043965824803168779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41239661391954433070891705 30929746043965824803168779)
        ·
          refine ⟨46394619065948737204753169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30929746043965824803168779 46394619065948737204753169)
          ·
            refine ⟨34795964299461552903564877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46394619065948737204753169 34795964299461552903564877)
            ·
              refine ⟨13048486612298082338836829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34795964299461552903564877 13048486612298082338836829)
              ·
                refine ⟨4893182479611780877063811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13048486612298082338836829 4893182479611780877063811)
                ·
                  refine ⟨7339773719417671315595717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893182479611780877063811 7339773719417671315595717)
                  ·
                    refine ⟨1376207572390813371674197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7339773719417671315595717 1376207572390813371674197)
                    ·
                      rfl

theorem cell22_4020232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4020232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020232 prefixEnd_4020232 := by exact prefixLift 4020232
  have htrace : WordTrace (prefixWord ++ tailWord_4020232) baseStart_4020232 baseEnd_4020232 := by
    simpa [prefixWord, tailWord_4020232, baseEnd_4020232] using wordTrace_append hprefix tailTrace_4020232
  have hstable : (prefixWord ++ tailWord_4020232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020232).length < 2 ^ (prefixWord ++ tailWord_4020232).sum := by decide
  have hdescent : baseEnd_4020232 < baseStart_4020232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020281 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 4]
def baseStart_4020281 : Nat := 118140960795 + 4020281 * 2 ^ 59
def prefixEnd_4020281 : Nat := 4983230072969 + 3 ^ 40 * 4020281 * 2
def baseEnd_4020281 : Nat := 458741448697397859066349

theorem tailTrace_4020281 : CollatzResearch.WordTrace tailWord_4020281 prefixEnd_4020281 458741448697397859066349 := by
  unfold tailWord_4020281
  simp only [CollatzResearch.WordTrace]
  refine ⟨146631694348216021176148697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97754462898810680784099131 146631694348216021176148697)
  ·
    refine ⟨109973770761162015882111523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146631694348216021176148697 109973770761162015882111523)
    ·
      refine ⟨164960656141743023823167285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109973770761162015882111523 164960656141743023823167285)
      ·
        refine ⟨15465061513288408483421933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164960656141743023823167285 15465061513288408483421933)
        ·
          refine ⟨5799398067483153181283225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15465061513288408483421933 5799398067483153181283225)
          ·
            refine ⟨4349548550612364885962419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799398067483153181283225 4349548550612364885962419)
            ·
              refine ⟨6524322825918547328943629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349548550612364885962419 6524322825918547328943629)
              ·
                refine ⟨2446621059719455248353861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6524322825918547328943629 2446621059719455248353861)
                ·
                  refine ⟨458741448697397859066349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446621059719455248353861 458741448697397859066349)
                  ·
                    rfl

theorem cell22_4020281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_4020281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020281 prefixEnd_4020281 := by exact prefixLift 4020281
  have htrace : WordTrace (prefixWord ++ tailWord_4020281) baseStart_4020281 baseEnd_4020281 := by
    simpa [prefixWord, tailWord_4020281, baseEnd_4020281] using wordTrace_append hprefix tailTrace_4020281
  have hstable : (prefixWord ++ tailWord_4020281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020281).length < 2 ^ (prefixWord ++ tailWord_4020281).sum := by decide
  have hdescent : baseEnd_4020281 < baseStart_4020281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020305 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_4020305 : Nat := 118140960795 + 4020305 * 2 ^ 59
def prefixEnd_4020305 : Nat := 4983230072969 + 3 ^ 40 * 4020305 * 2
def baseEnd_4020305 : Nat := 1376232561782665514598973

theorem tailTrace_4020305 : CollatzResearch.WordTrace tailWord_4020305 prefixEnd_4020305 1376232561782665514598973 := by
  unfold tailWord_4020305
  simp only [CollatzResearch.WordTrace]
  refine ⟨146632569700129073275022369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97755046466752715516681579 146632569700129073275022369)
  ·
    refine ⟨109974427275096804956266777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146632569700129073275022369 109974427275096804956266777)
    ·
      refine ⟨82480820456322603717200083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109974427275096804956266777 82480820456322603717200083)
      ·
        refine ⟨123721230684483905575800125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82480820456322603717200083 123721230684483905575800125)
        ·
          refine ⟨46395461506681464590925047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123721230684483905575800125 46395461506681464590925047)
          ·
            refine ⟨69593192260022196886387571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46395461506681464590925047 69593192260022196886387571)
            ·
              refine ⟨104389788390033295329581357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69593192260022196886387571 104389788390033295329581357)
              ·
                refine ⟨39146170646262485748593009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104389788390033295329581357 39146170646262485748593009)
                ·
                  refine ⟨29359627984696864311444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39146170646262485748593009 29359627984696864311444757)
                  ·
                    refine ⟨1376232561782665514598973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29359627984696864311444757 1376232561782665514598973)
                    ·
                      rfl

theorem cell22_4020305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_4020305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020305 prefixEnd_4020305 := by exact prefixLift 4020305
  have htrace : WordTrace (prefixWord ++ tailWord_4020305) baseStart_4020305 baseEnd_4020305 := by
    simpa [prefixWord, tailWord_4020305, baseEnd_4020305] using wordTrace_append hprefix tailTrace_4020305
  have hstable : (prefixWord ++ tailWord_4020305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020305).length < 2 ^ (prefixWord ++ tailWord_4020305).sum := by decide
  have hdescent : baseEnd_4020305 < baseStart_4020305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020401 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_4020401 : Nat := 118140960795 + 4020401 * 2 ^ 59
def prefixEnd_4020401 : Nat := 4983230072969 + 3 ^ 40 * 4020401 * 2
def baseEnd_4020401 : Nat := 1376265424544553264198679

theorem tailTrace_4020401 : CollatzResearch.WordTrace tailWord_4020401 prefixEnd_4020401 1376265424544553264198679 := by
  unfold tailWord_4020401
  simp only [CollatzResearch.WordTrace]
  refine ⟨146636071107781281670517057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97757380738520854447011371 146636071107781281670517057)
  ·
    refine ⟨109977053330835961252887793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146636071107781281670517057 109977053330835961252887793)
    ·
      refine ⟨82482789998126970939665845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109977053330835961252887793 82482789998126970939665845)
      ·
        refine ⟨7732761562324403525593673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82482789998126970939665845 7732761562324403525593673)
        ·
          refine ⟨5799571171743302644195255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7732761562324403525593673 5799571171743302644195255)
          ·
            refine ⟨8699356757614953966292883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799571171743302644195255 8699356757614953966292883)
            ·
              refine ⟨13049035136422430949439325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8699356757614953966292883 13049035136422430949439325)
              ·
                refine ⟨4893388176158411606039747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13049035136422430949439325 4893388176158411606039747)
                ·
                  refine ⟨7340082264237617409059621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893388176158411606039747 7340082264237617409059621)
                  ·
                    refine ⟨1376265424544553264198679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7340082264237617409059621 1376265424544553264198679)
                    ·
                      rfl

theorem cell22_4020401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_4020401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020401 prefixEnd_4020401 := by exact prefixLift 4020401
  have htrace : WordTrace (prefixWord ++ tailWord_4020401) baseStart_4020401 baseEnd_4020401 := by
    simpa [prefixWord, tailWord_4020401, baseEnd_4020401] using wordTrace_append hprefix tailTrace_4020401
  have hstable : (prefixWord ++ tailWord_4020401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020401).length < 2 ^ (prefixWord ++ tailWord_4020401).sum := by decide
  have hdescent : baseEnd_4020401 < baseStart_4020401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020431 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 2, 3]
def baseStart_4020431 : Nat := 118140960795 + 4020431 * 2 ^ 59
def prefixEnd_4020431 : Nat := 4983230072969 + 3 ^ 40 * 4020431 * 2
def baseEnd_4020431 : Nat := 1376275694157643185948587

theorem tailTrace_4020431 : CollatzResearch.WordTrace tailWord_4020431 prefixEnd_4020431 1376275694157643185948587 := by
  unfold tailWord_4020431
  simp only [CollatzResearch.WordTrace]
  refine ⟨146637165297672596794109147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97758110198448397862739431 146637165297672596794109147)
  ·
    refine ⟨219955747946508895191163721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146637165297672596794109147 219955747946508895191163721)
    ·
      refine ⟨164966810959881671393372791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219955747946508895191163721 164966810959881671393372791)
      ·
        refine ⟨247450216439822507090059187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164966810959881671393372791 247450216439822507090059187)
        ·
          refine ⟨371175324659733760635088781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247450216439822507090059187 371175324659733760635088781)
          ·
            refine ⟨139190746747400160238158293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371175324659733760635088781 139190746747400160238158293)
            ·
              refine ⟨3262283126892191255581835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139190746747400160238158293 3262283126892191255581835)
              ·
                refine ⟨4893424690338286883372753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262283126892191255581835 4893424690338286883372753)
                ·
                  refine ⟨3670068517753715162529565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4893424690338286883372753 3670068517753715162529565)
                  ·
                    refine ⟨1376275694157643185948587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670068517753715162529565 1376275694157643185948587)
                    ·
                      rfl

theorem cell22_4020431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_4020431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020431 prefixEnd_4020431 := by exact prefixLift 4020431
  have htrace : WordTrace (prefixWord ++ tailWord_4020431) baseStart_4020431 baseEnd_4020431 := by
    simpa [prefixWord, tailWord_4020431, baseEnd_4020431] using wordTrace_append hprefix tailTrace_4020431
  have hstable : (prefixWord ++ tailWord_4020431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020431).length < 2 ^ (prefixWord ++ tailWord_4020431).sum := by decide
  have hdescent : baseEnd_4020431 < baseStart_4020431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020461 : List Nat := [1, 5, 1, 2, 4, 1, 8]
def baseStart_4020461 : Nat := 118140960795 + 4020461 * 2 ^ 59
def prefixEnd_4020461 : Nat := 4983230072969 + 3 ^ 40 * 4020461 * 2
def baseEnd_4020461 : Nat := 50973554213730855840685

theorem tailTrace_4020461 : CollatzResearch.WordTrace tailWord_4020461 prefixEnd_4020461 50973554213730855840685 := by
  unfold tailWord_4020461
  simp only [CollatzResearch.WordTrace]
  refine ⟨146638259487563911917701237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97758839658375941278467491 146638259487563911917701237)
  ·
    refine ⟨13747336826959116742284491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146638259487563911917701237 13747336826959116742284491)
    ·
      refine ⟨20621005240438675113426737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13747336826959116742284491 20621005240438675113426737)
      ·
        refine ⟨15465753930329006335070053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20621005240438675113426737 15465753930329006335070053)
        ·
          refine ⟨2899828861936688687825635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15465753930329006335070053 2899828861936688687825635)
          ·
            refine ⟨4349743292905033031738453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899828861936688687825635 4349743292905033031738453)
            ·
              refine ⟨50973554213730855840685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4349743292905033031738453 50973554213730855840685)
              ·
                rfl

theorem cell22_4020461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 8].length) (baseStart_4020461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020461 prefixEnd_4020461 := by exact prefixLift 4020461
  have htrace : WordTrace (prefixWord ++ tailWord_4020461) baseStart_4020461 baseEnd_4020461 := by
    simpa [prefixWord, tailWord_4020461, baseEnd_4020461] using wordTrace_append hprefix tailTrace_4020461
  have hstable : (prefixWord ++ tailWord_4020461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020461).length < 2 ^ (prefixWord ++ tailWord_4020461).sum := by decide
  have hdescent : baseEnd_4020461 < baseStart_4020461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020476 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_4020476 : Nat := 118140960795 + 4020476 * 2 ^ 59
def prefixEnd_4020476 : Nat := 4983230072969 + 3 ^ 40 * 4020476 * 2
def baseEnd_4020476 : Nat := 1376291098577278068573449

theorem tailTrace_4020476 : CollatzResearch.WordTrace tailWord_4020476 prefixEnd_4020476 1376291098577278068573449 := by
  unfold tailWord_4020476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73319403291254784739748641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97759204388339712986331521 73319403291254784739748641)
  ·
    refine ⟨54989552468441088554811481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73319403291254784739748641 54989552468441088554811481)
    ·
      refine ⟨41242164351330816416108611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54989552468441088554811481 41242164351330816416108611)
      ·
        refine ⟨61863246526996224624162917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41242164351330816416108611 61863246526996224624162917)
        ·
          refine ⟨11599358723811792117030547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61863246526996224624162917 11599358723811792117030547)
          ·
            refine ⟨17399038085717688175545821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599358723811792117030547 17399038085717688175545821)
            ·
              refine ⟨6524639282144133065829683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17399038085717688175545821 6524639282144133065829683)
              ·
                refine ⟨9786958923216199598744525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524639282144133065829683 9786958923216199598744525)
                ·
                  refine ⟨3670109596206074849529197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9786958923216199598744525 3670109596206074849529197)
                  ·
                    refine ⟨1376291098577278068573449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670109596206074849529197 1376291098577278068573449)
                    ·
                      rfl

theorem cell22_4020476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_4020476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020476 prefixEnd_4020476 := by exact prefixLift 4020476
  have htrace : WordTrace (prefixWord ++ tailWord_4020476) baseStart_4020476 baseEnd_4020476 := by
    simpa [prefixWord, tailWord_4020476, baseEnd_4020476] using wordTrace_append hprefix tailTrace_4020476
  have hstable : (prefixWord ++ tailWord_4020476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020476).length < 2 ^ (prefixWord ++ tailWord_4020476).sum := by decide
  have hdescent : baseEnd_4020476 < baseStart_4020476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020489 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 5]
def baseStart_4020489 : Nat := 118140960795 + 4020489 * 2 ^ 59
def prefixEnd_4020489 : Nat := 4983230072969 + 3 ^ 40 * 4020489 * 2
def baseEnd_4020489 : Nat := 458765182914316789332803

theorem tailTrace_4020489 : CollatzResearch.WordTrace tailWord_4020489 prefixEnd_4020489 458765182914316789332803 := by
  unfold tailWord_4020489
  simp only [CollatzResearch.WordTrace]
  refine ⟨146639280731462472699720521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97759520487641648466480347 146639280731462472699720521)
  ·
    refine ⟨109979460548596854524790391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146639280731462472699720521 109979460548596854524790391)
    ·
      refine ⟨164969190822895281787185587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109979460548596854524790391 164969190822895281787185587)
      ·
        refine ⟨247453786234342922680778381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164969190822895281787185587 247453786234342922680778381)
        ·
          refine ⟨92795169837878596005291893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247453786234342922680778381 92795169837878596005291893)
          ·
            refine ⟨8699547172301118375496115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92795169837878596005291893 8699547172301118375496115)
            ·
              refine ⟨13049320758451677563244173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8699547172301118375496115 13049320758451677563244173)
              ·
                refine ⟨4893495284419379086216565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13049320758451677563244173 4893495284419379086216565)
                ·
                  refine ⟨458765182914316789332803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4893495284419379086216565 458765182914316789332803)
                  ·
                    rfl

theorem cell22_4020489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_4020489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020489 prefixEnd_4020489 := by exact prefixLift 4020489
  have htrace : WordTrace (prefixWord ++ tailWord_4020489) baseStart_4020489 baseEnd_4020489 := by
    simpa [prefixWord, tailWord_4020489, baseEnd_4020489] using wordTrace_append hprefix tailTrace_4020489
  have hstable : (prefixWord ++ tailWord_4020489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020489).length < 2 ^ (prefixWord ++ tailWord_4020489).sum := by decide
  have hdescent : baseEnd_4020489 < baseStart_4020489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020549 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_4020549 : Nat := 118140960795 + 4020549 * 2 ^ 59
def prefixEnd_4020549 : Nat := 4983230072969 + 3 ^ 40 * 4020549 * 2
def baseEnd_4020549 : Nat := 1376316087969130211498225

theorem tailTrace_4020549 : CollatzResearch.WordTrace tailWord_4020549 prefixEnd_4020549 1376316087969130211498225 := by
  unfold tailWord_4020549
  simp only [CollatzResearch.WordTrace]
  refine ⟨146641469111245102946904701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97760979407496735297936467 146641469111245102946904701)
  ·
    refine ⟨54990550916716913605089263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146641469111245102946904701 54990550916716913605089263)
    ·
      refine ⟨82485826375075370407633895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54990550916716913605089263 82485826375075370407633895)
      ·
        refine ⟨123728739562613055611450843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82485826375075370407633895 123728739562613055611450843)
        ·
          refine ⟨185593109343919583417176265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123728739562613055611450843 185593109343919583417176265)
          ·
            refine ⟨139194832007939687562882199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185593109343919583417176265 139194832007939687562882199)
            ·
              refine ⟨208792248011909531344323299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139194832007939687562882199 208792248011909531344323299)
              ·
                refine ⟨313188372017864297016484949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208792248011909531344323299 313188372017864297016484949)
                ·
                  refine ⟨3670176234584347230661933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 313188372017864297016484949 3670176234584347230661933)
                  ·
                    refine ⟨1376316087969130211498225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670176234584347230661933 1376316087969130211498225)
                    ·
                      rfl

theorem cell22_4020549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_4020549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020549 prefixEnd_4020549 := by exact prefixLift 4020549
  have htrace : WordTrace (prefixWord ++ tailWord_4020549) baseStart_4020549 baseEnd_4020549 := by
    simpa [prefixWord, tailWord_4020549, baseEnd_4020549] using wordTrace_append hprefix tailTrace_4020549
  have hstable : (prefixWord ++ tailWord_4020549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020549).length < 2 ^ (prefixWord ++ tailWord_4020549).sum := by decide
  have hdescent : baseEnd_4020549 < baseStart_4020549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020574 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4020574 : Nat := 118140960795 + 4020574 * 2 ^ 59
def prefixEnd_4020574 : Nat := 4983230072969 + 3 ^ 40 * 4020574 * 2
def baseEnd_4020574 : Nat := 458774881993346159874383

theorem tailTrace_4020574 : CollatzResearch.WordTrace tailWord_4020574 prefixEnd_4020574 458774881993346159874383 := by
  unfold tailWord_4020574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18330297617019316527070597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97761587290769688144376517 18330297617019316527070597)
  ·
    refine ⟨3436930803191121848825737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18330297617019316527070597 3436930803191121848825737)
    ·
      refine ⟨2577698102393341386619303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3436930803191121848825737 2577698102393341386619303)
      ·
        refine ⟨3866547153590012079928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577698102393341386619303 3866547153590012079928955)
        ·
          refine ⟨5799820730385018119893433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866547153590012079928955 5799820730385018119893433)
          ·
            refine ⟨4349865547788763589920075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799820730385018119893433 4349865547788763589920075)
            ·
              refine ⟨6524798321683145384880113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349865547788763589920075 6524798321683145384880113)
              ·
                refine ⟨4893598741262359038660085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524798321683145384880113 4893598741262359038660085)
                ·
                  refine ⟨458774881993346159874383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4893598741262359038660085 458774881993346159874383)
                  ·
                    rfl

theorem cell22_4020574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4020574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020574 prefixEnd_4020574 := by exact prefixLift 4020574
  have htrace : WordTrace (prefixWord ++ tailWord_4020574) baseStart_4020574 baseEnd_4020574 := by
    simpa [prefixWord, tailWord_4020574, baseEnd_4020574] using wordTrace_append hprefix tailTrace_4020574
  have hstable : (prefixWord ++ tailWord_4020574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020574).length < 2 ^ (prefixWord ++ tailWord_4020574).sum := by decide
  have hdescent : baseEnd_4020574 < baseStart_4020574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020583 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4020583 : Nat := 118140960795 + 4020583 * 2 ^ 59
def prefixEnd_4020583 : Nat := 4983230072969 + 3 ^ 40 * 4020583 * 2
def baseEnd_4020583 : Nat := 1376327726863965456148121

theorem tailTrace_4020583 : CollatzResearch.WordTrace tailWord_4020583 prefixEnd_4020583 1376327726863965456148121 := by
  unfold tailWord_4020583
  simp only [CollatzResearch.WordTrace]
  refine ⟨146642709193121926753642403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97761806128747951169094935 146642709193121926753642403)
  ·
    refine ⟨219964063789682890130463605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146642709193121926753642403 219964063789682890130463605)
    ·
      refine ⟨20621630980282770949730963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219964063789682890130463605 20621630980282770949730963)
      ·
        refine ⟨30932446470424156424596445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20621630980282770949730963 30932446470424156424596445)
        ·
          refine ⟨11599667426409058659223667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30932446470424156424596445 11599667426409058659223667)
          ·
            refine ⟨17399501139613587988835501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599667426409058659223667 17399501139613587988835501)
            ·
              refine ⟨6524812927355095495813313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17399501139613587988835501 6524812927355095495813313)
              ·
                refine ⟨4893609695516321621859985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524812927355095495813313 4893609695516321621859985)
                ·
                  refine ⟨3670207271637241216394989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4893609695516321621859985 3670207271637241216394989)
                  ·
                    refine ⟨1376327726863965456148121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670207271637241216394989 1376327726863965456148121)
                    ·
                      rfl

theorem cell22_4020583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4020583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020583 prefixEnd_4020583 := by exact prefixLift 4020583
  have htrace : WordTrace (prefixWord ++ tailWord_4020583) baseStart_4020583 baseEnd_4020583 := by
    simpa [prefixWord, tailWord_4020583, baseEnd_4020583] using wordTrace_append hprefix tailTrace_4020583
  have hstable : (prefixWord ++ tailWord_4020583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020583).length < 2 ^ (prefixWord ++ tailWord_4020583).sum := by decide
  have hdescent : baseEnd_4020583 < baseStart_4020583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020645 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_4020645 : Nat := 118140960795 + 4020645 * 2 ^ 59
def prefixEnd_4020645 : Nat := 4983230072969 + 3 ^ 40 * 4020645 * 2
def baseEnd_4020645 : Nat := 1376348950731017961097931

theorem tailTrace_4020645 : CollatzResearch.WordTrace tailWord_4020645 prefixEnd_4020645 1376348950731017961097931 := by
  unfold tailWord_4020645
  simp only [CollatzResearch.WordTrace]
  refine ⟨146644970518897311342399389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97763313679264874228266259 146644970518897311342399389)
  ·
    refine ⟨54991863944586491753399771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146644970518897311342399389 54991863944586491753399771)
    ·
      refine ⟨82487795916879737630099657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54991863944586491753399771 82487795916879737630099657)
      ·
        refine ⟨61865846937659803222574743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82487795916879737630099657 61865846937659803222574743)
        ·
          refine ⟨92798770406489704833862115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61865846937659803222574743 92798770406489704833862115)
          ·
            refine ⟨139198155609734557250793173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92798770406489704833862115 139198155609734557250793173)
            ·
              refine ⟨3262456772103153685565465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139198155609734557250793173 3262456772103153685565465)
              ·
                refine ⟨2446842579077365264174099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262456772103153685565465 2446842579077365264174099)
                ·
                  refine ⟨3670263868616047896261149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446842579077365264174099 3670263868616047896261149)
                  ·
                    refine ⟨1376348950731017961097931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670263868616047896261149 1376348950731017961097931)
                    ·
                      rfl

theorem cell22_4020645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_4020645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020645 prefixEnd_4020645 := by exact prefixLift 4020645
  have htrace : WordTrace (prefixWord ++ tailWord_4020645) baseStart_4020645 baseEnd_4020645 := by
    simpa [prefixWord, tailWord_4020645, baseEnd_4020645] using wordTrace_append hprefix tailTrace_4020645
  have hstable : (prefixWord ++ tailWord_4020645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020645).length < 2 ^ (prefixWord ++ tailWord_4020645).sum := by decide
  have hdescent : baseEnd_4020645 < baseStart_4020645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020701 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4020701 : Nat := 118140960795 + 4020701 * 2 ^ 59
def prefixEnd_4020701 : Nat := 4983230072969 + 3 ^ 40 * 4020701 * 2
def baseEnd_4020701 : Nat := 1376368120675452481697759

theorem tailTrace_4020701 : CollatzResearch.WordTrace tailWord_4020701 prefixEnd_4020701 1376368120675452481697759 := by
  unfold tailWord_4020701
  simp only [CollatzResearch.WordTrace]
  refine ⟨146647013006694432906437957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97764675337796288604291971 146647013006694432906437957)
  ·
    refine ⟨27496314938755206169957117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146647013006694432906437957 27496314938755206169957117)
    ·
      refine ⟨10311118102033202313733919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27496314938755206169957117 10311118102033202313733919)
      ·
        refine ⟨15466677153049803470600879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311118102033202313733919 15466677153049803470600879)
        ·
          refine ⟨23200015729574705205901319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15466677153049803470600879 23200015729574705205901319)
          ·
            refine ⟨34800023594362057808851979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23200015729574705205901319 34800023594362057808851979)
            ·
              refine ⟨52200035391543086713277969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34800023594362057808851979 52200035391543086713277969)
              ·
                refine ⟨39150026543657315034958477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52200035391543086713277969 39150026543657315034958477)
                ·
                  refine ⟨14681259953871493138109429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39150026543657315034958477 14681259953871493138109429)
                  ·
                    refine ⟨1376368120675452481697759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14681259953871493138109429 1376368120675452481697759)
                    ·
                      rfl

theorem cell22_4020701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4020701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020701 prefixEnd_4020701 := by exact prefixLift 4020701
  have htrace : WordTrace (prefixWord ++ tailWord_4020701) baseStart_4020701 baseEnd_4020701 := by
    simpa [prefixWord, tailWord_4020701, baseEnd_4020701] using wordTrace_append hprefix tailTrace_4020701
  have hstable : (prefixWord ++ tailWord_4020701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020701).length < 2 ^ (prefixWord ++ tailWord_4020701).sum := by decide
  have hdescent : baseEnd_4020701 < baseStart_4020701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020703 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 4]
def baseStart_4020703 : Nat := 118140960795 + 4020703 * 2 ^ 59
def prefixEnd_4020703 : Nat := 4983230072969 + 3 ^ 40 * 4020703 * 2
def baseEnd_4020703 : Nat := 458789601772108381049251

theorem tailTrace_4020703 : CollatzResearch.WordTrace tailWord_4020703 prefixEnd_4020703 458789601772108381049251 := by
  unfold tailWord_4020703
  simp only [CollatzResearch.WordTrace]
  refine ⟨146647085952687187248010763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97764723968458124832007175 146647085952687187248010763)
  ·
    refine ⟨219970628929030780872016145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146647085952687187248010763 219970628929030780872016145)
    ·
      refine ⟨164977971696773085654012109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219970628929030780872016145 164977971696773085654012109)
      ·
        refine ⟨61866739386289907120254541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164977971696773085654012109 61866739386289907120254541)
        ·
          refine ⟨23200027269858715170095453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61866739386289907120254541 23200027269858715170095453)
          ·
            refine ⟨8700010226197018188785795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23200027269858715170095453 8700010226197018188785795)
            ·
              refine ⟨13050015339295527283178693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700010226197018188785795 13050015339295527283178693)
              ·
                refine ⟨2446877876117911365596005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13050015339295527283178693 2446877876117911365596005)
                ·
                  refine ⟨458789601772108381049251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446877876117911365596005 458789601772108381049251)
                  ·
                    rfl

theorem cell22_4020703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 4].length) (baseStart_4020703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020703 prefixEnd_4020703 := by exact prefixLift 4020703
  have htrace : WordTrace (prefixWord ++ tailWord_4020703) baseStart_4020703 baseEnd_4020703 := by
    simpa [prefixWord, tailWord_4020703, baseEnd_4020703] using wordTrace_append hprefix tailTrace_4020703
  have hstable : (prefixWord ++ tailWord_4020703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020703).length < 2 ^ (prefixWord ++ tailWord_4020703).sum := by decide
  have hdescent : baseEnd_4020703 < baseStart_4020703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020718 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4020718 : Nat := 118140960795 + 4020718 * 2 ^ 59
def prefixEnd_4020718 : Nat := 4983230072969 + 3 ^ 40 * 4020718 * 2
def baseEnd_4020718 : Nat := 1376373940122870104022707

theorem tailTrace_4020718 : CollatzResearch.WordTrace tailWord_4020718 prefixEnd_4020718 1376373940122870104022707 := by
  unfold tailWord_4020718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18330954130954105601225851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97765088698421896539871205 18330954130954105601225851)
  ·
    refine ⟨27496431196431158401838777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18330954130954105601225851 27496431196431158401838777)
    ·
      refine ⟨20622323397323368801379083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27496431196431158401838777 20622323397323368801379083)
      ·
        refine ⟨30933485095985053202068625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20622323397323368801379083 30933485095985053202068625)
        ·
          refine ⟨23200113821988789901551469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30933485095985053202068625 23200113821988789901551469)
          ·
            refine ⟨8700042683245796213081801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23200113821988789901551469 8700042683245796213081801)
            ·
              refine ⟨6525032012434347159811351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700042683245796213081801 6525032012434347159811351)
              ·
                refine ⟨9787548018651520739717027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525032012434347159811351 9787548018651520739717027)
                ·
                  refine ⟨14681322027977281109575541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787548018651520739717027 14681322027977281109575541)
                  ·
                    refine ⟨1376373940122870104022707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14681322027977281109575541 1376373940122870104022707)
                    ·
                      rfl

theorem cell22_4020718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4020718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020718 prefixEnd_4020718 := by exact prefixLift 4020718
  have htrace : WordTrace (prefixWord ++ tailWord_4020718) baseStart_4020718 baseEnd_4020718 := by
    simpa [prefixWord, tailWord_4020718, baseEnd_4020718] using wordTrace_append hprefix tailTrace_4020718
  have hstable : (prefixWord ++ tailWord_4020718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020718).length < 2 ^ (prefixWord ++ tailWord_4020718).sum := by decide
  have hdescent : baseEnd_4020718 < baseStart_4020718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020782 : List Nat := [4, 1, 3, 1, 4, 1, 2, 6]
def baseStart_4020782 : Nat := 118140960795 + 4020782 * 2 ^ 59
def prefixEnd_4020782 : Nat := 4983230072969 + 3 ^ 40 * 4020782 * 2
def baseEnd_4020782 : Nat := 152932872070088363380279

theorem tailTrace_4020782 : CollatzResearch.WordTrace tailWord_4020782 prefixEnd_4020782 152932872070088363380279 := by
  unfold tailWord_4020782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331245914925122967517075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97766644879600655826757733 18331245914925122967517075)
  ·
    refine ⟨27496868872387684451275613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18331245914925122967517075 27496868872387684451275613)
    ·
      refine ⟨10311325827145381669228355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27496868872387684451275613 10311325827145381669228355)
      ·
        refine ⟨15466988740718072503842533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311325827145381669228355 15466988740718072503842533)
        ·
          refine ⟨2900060388884638594470475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15466988740718072503842533 2900060388884638594470475)
          ·
            refine ⟨4350090583326957891705713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900060388884638594470475 4350090583326957891705713)
            ·
              refine ⟨3262567937495218418779285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350090583326957891705713 3262567937495218418779285)
              ·
                refine ⟨152932872070088363380279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3262567937495218418779285 152932872070088363380279)
                ·
                  rfl

theorem cell22_4020782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_4020782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020782 prefixEnd_4020782 := by exact prefixLift 4020782
  have htrace : WordTrace (prefixWord ++ tailWord_4020782) baseStart_4020782 baseEnd_4020782 := by
    simpa [prefixWord, tailWord_4020782, baseEnd_4020782] using wordTrace_append hprefix tailTrace_4020782
  have hstable : (prefixWord ++ tailWord_4020782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020782).length < 2 ^ (prefixWord ++ tailWord_4020782).sum := by decide
  have hdescent : baseEnd_4020782 < baseStart_4020782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020797 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_4020797 : Nat := 118140960795 + 4020797 * 2 ^ 59
def prefixEnd_4020797 : Nat := 4983230072969 + 3 ^ 40 * 4020797 * 2
def baseEnd_4020797 : Nat := 1376400983437340231297465

theorem tailTrace_4020797 : CollatzResearch.WordTrace tailWord_4020797 prefixEnd_4020797 1376400983437340231297465 := by
  unfold tailWord_4020797
  simp only [CollatzResearch.WordTrace]
  refine ⟨146650514414346641301932645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97767009609564427534621763 146650514414346641301932645)
  ·
    refine ⟨27496971452689995244112371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146650514414346641301932645 27496971452689995244112371)
    ·
      refine ⟨41245457179034992866168557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27496971452689995244112371 41245457179034992866168557)
      ·
        refine ⟨15467046442138122324813209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41245457179034992866168557 15467046442138122324813209)
        ·
          refine ⟨11600284831603591743609907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15467046442138122324813209 11600284831603591743609907)
          ·
            refine ⟨17400427247405387615414861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600284831603591743609907 17400427247405387615414861)
            ·
              refine ⟨6525160217777020355780573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17400427247405387615414861 6525160217777020355780573)
              ·
                refine ⟨2446935081666382633417715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525160217777020355780573 2446935081666382633417715)
                ·
                  refine ⟨3670402622499573950126573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446935081666382633417715 3670402622499573950126573)
                  ·
                    refine ⟨1376400983437340231297465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670402622499573950126573 1376400983437340231297465)
                    ·
                      rfl

theorem cell22_4020797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_4020797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020797 prefixEnd_4020797 := by exact prefixLift 4020797
  have htrace : WordTrace (prefixWord ++ tailWord_4020797) baseStart_4020797 baseEnd_4020797 := by
    simpa [prefixWord, tailWord_4020797, baseEnd_4020797] using wordTrace_append hprefix tailTrace_4020797
  have hstable : (prefixWord ++ tailWord_4020797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020797).length < 2 ^ (prefixWord ++ tailWord_4020797).sum := by decide
  have hdescent : baseEnd_4020797 < baseStart_4020797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020840 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_4020840 : Nat := 118140960795 + 4020840 * 2 ^ 59
def prefixEnd_4020840 : Nat := 4983230072969 + 3 ^ 40 * 4020840 * 2
def baseEnd_4020840 : Nat := 1376415703216102452472333

theorem tailTrace_4020840 : CollatzResearch.WordTrace tailWord_4020840 prefixEnd_4020840 1376415703216102452472333 := by
  unfold tailWord_4020840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73326041376595429822873987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97768055168793906430498649 73326041376595429822873987)
  ·
    refine ⟨109989062064893144734310981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73326041376595429822873987 109989062064893144734310981)
    ·
      refine ⟨20622949137167464637683309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109989062064893144734310981 20622949137167464637683309)
      ·
        refine ⟨7733605926437799239131241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20622949137167464637683309 7733605926437799239131241)
        ·
          refine ⟨5800204444828349429348431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7733605926437799239131241 5800204444828349429348431)
          ·
            refine ⟨8700306667242524144022647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800204444828349429348431 8700306667242524144022647)
            ·
              refine ⟨13050460000863786216033971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700306667242524144022647 13050460000863786216033971)
              ·
                refine ⟨19575690001295679324050957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050460000863786216033971 19575690001295679324050957)
                ·
                  refine ⟨7340883750485879746519109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19575690001295679324050957 7340883750485879746519109)
                  ·
                    refine ⟨1376415703216102452472333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7340883750485879746519109 1376415703216102452472333)
                    ·
                      rfl

theorem cell22_4020840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_4020840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020840 prefixEnd_4020840 := by exact prefixLift 4020840
  have htrace : WordTrace (prefixWord ++ tailWord_4020840) baseStart_4020840 baseEnd_4020840 := by
    simpa [prefixWord, tailWord_4020840, baseEnd_4020840] using wordTrace_append hprefix tailTrace_4020840
  have hstable : (prefixWord ++ tailWord_4020840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020840).length < 2 ^ (prefixWord ++ tailWord_4020840).sum := by decide
  have hdescent : baseEnd_4020840 < baseStart_4020840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4020928 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_4020928 : Nat := 118140960795 + 4020928 * 2 ^ 59
def prefixEnd_4020928 : Nat := 4983230072969 + 3 ^ 40 * 4020928 * 2
def baseEnd_4020928 : Nat := 458815275804833185424021

theorem tailTrace_4020928 : CollatzResearch.WordTrace tailWord_4020928 prefixEnd_4020928 458815275804833185424021 := by
  unfold tailWord_4020928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327646188436025337475719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97770194917914700449967625 73327646188436025337475719)
  ·
    refine ⟨109991469282654038006213579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73327646188436025337475719 109991469282654038006213579)
    ·
      refine ⟨164987203923981057009320369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109991469282654038006213579 164987203923981057009320369)
      ·
        refine ⟨123740402942985792756990277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164987203923981057009320369 123740402942985792756990277)
        ·
          refine ⟨23201325551809836141935677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123740402942985792756990277 23201325551809836141935677)
          ·
            refine ⟨8700497081928688553225879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23201325551809836141935677 8700497081928688553225879)
            ·
              refine ⟨13050745622893032829838819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700497081928688553225879 13050745622893032829838819)
              ·
                refine ⟨19576118434339549244758229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050745622893032829838819 19576118434339549244758229)
                ·
                  refine ⟨458815275804833185424021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19576118434339549244758229 458815275804833185424021)
                  ·
                    rfl

theorem cell22_4020928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_4020928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4020928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4020928 prefixEnd_4020928 := by exact prefixLift 4020928
  have htrace : WordTrace (prefixWord ++ tailWord_4020928) baseStart_4020928 baseEnd_4020928 := by
    simpa [prefixWord, tailWord_4020928, baseEnd_4020928] using wordTrace_append hprefix tailTrace_4020928
  have hstable : (prefixWord ++ tailWord_4020928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4020928).length < 2 ^ (prefixWord ++ tailWord_4020928).sum := by decide
  have hdescent : baseEnd_4020928 < baseStart_4020928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4020928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
