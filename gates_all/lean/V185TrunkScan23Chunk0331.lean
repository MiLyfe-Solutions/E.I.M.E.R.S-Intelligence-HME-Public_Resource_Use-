import V185TrunkScan23Chunk0330

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1956495 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_1956495 : Nat := 118140960795 + 1956495 * 2 ^ 59
def prefixEnd_1956495 : Nat := 4983230072969 + 3 ^ 40 * 1956495 * 2
def baseEnd_1956495 : Nat := 1004622333118427938014749

theorem tailTrace_1956495 : CollatzResearch.WordTrace tailWord_1956495 prefixEnd_1956495 1004622333118427938014749 := by
  unfold tailWord_1956495
  simp only [CollatzResearch.WordTrace]
  refine ⟨71359235046960232588646939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47572823364640155059097959 71359235046960232588646939)
  ·
    refine ⟨107038852570440348882970409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71359235046960232588646939 107038852570440348882970409)
    ·
      refine ⟨80279139427830261662227807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107038852570440348882970409 80279139427830261662227807)
      ·
        refine ⟨120418709141745392493341711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80279139427830261662227807 120418709141745392493341711)
        ·
          refine ⟨180628063712618088740012567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120418709141745392493341711 180628063712618088740012567)
          ·
            refine ⟨270942095568927133110018851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180628063712618088740012567 270942095568927133110018851)
            ·
              refine ⟨406413143353390699665028277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270942095568927133110018851 406413143353390699665028277)
              ·
                refine ⟨38101232189380378093596401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406413143353390699665028277 38101232189380378093596401)
                ·
                  refine ⟨28575924142035283570197301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38101232189380378093596401 28575924142035283570197301)
                  ·
                    refine ⟨2678992888315807834705997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28575924142035283570197301 2678992888315807834705997)
                    ·
                      refine ⟨1004622333118427938014749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2678992888315807834705997 1004622333118427938014749)
                      ·
                        rfl

theorem cell23_1956495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_1956495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956495 prefixEnd_1956495 := by exact prefixLift 1956495
  have htrace : WordTrace (prefixWord ++ tailWord_1956495) baseStart_1956495 baseEnd_1956495 := by
    simpa [prefixWord, tailWord_1956495, baseEnd_1956495] using wordTrace_append hprefix tailTrace_1956495
  have hstable : (prefixWord ++ tailWord_1956495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956495).length < 2 ^ (prefixWord ++ tailWord_1956495).sum := by decide
  have hdescent : baseEnd_1956495 < baseStart_1956495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956515 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 5, 5]
def baseStart_1956515 : Nat := 118140960795 + 1956515 * 2 ^ 59
def prefixEnd_1956515 : Nat := 4983230072969 + 3 ^ 40 * 1956515 * 2
def baseEnd_1956515 : Nat := 334877534243839286588219

theorem tailTrace_1956515 : CollatzResearch.WordTrace tailWord_1956515 prefixEnd_1956515 334877534243839286588219 := by
  unfold tailWord_1956515
  simp only [CollatzResearch.WordTrace]
  refine ⟨71359964506887776004374999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47573309671258517336249999 71359964506887776004374999)
  ·
    refine ⟨107039946760331664006562499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71359964506887776004374999 107039946760331664006562499)
    ·
      refine ⟨160559920140497496009843749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107039946760331664006562499 160559920140497496009843749)
      ·
        refine ⟨30104985026343280501845703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160559920140497496009843749 30104985026343280501845703)
        ·
          refine ⟨45157477539514920752768555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30104985026343280501845703 45157477539514920752768555)
          ·
            refine ⟨67736216309272381129152833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45157477539514920752768555 67736216309272381129152833)
            ·
              refine ⟨50802162231954285846864625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67736216309272381129152833 50802162231954285846864625)
              ·
                refine ⟨38101621673965714385148469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50802162231954285846864625 38101621673965714385148469)
                ·
                  refine ⟨3572027031934285723607669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38101621673965714385148469 3572027031934285723607669)
                  ·
                    refine ⟨334877534243839286588219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3572027031934285723607669 334877534243839286588219)
                    ·
                      rfl

theorem cell23_1956515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 5].length) (baseStart_1956515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956515 prefixEnd_1956515 := by exact prefixLift 1956515
  have htrace : WordTrace (prefixWord ++ tailWord_1956515) baseStart_1956515 baseEnd_1956515 := by
    simpa [prefixWord, tailWord_1956515, baseEnd_1956515] using wordTrace_append hprefix tailTrace_1956515
  have hstable : (prefixWord ++ tailWord_1956515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956515).length < 2 ^ (prefixWord ++ tailWord_1956515).sum := by decide
  have hdescent : baseEnd_1956515 < baseStart_1956515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956519 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 8]
def baseStart_1956519 : Nat := 118140960795 + 1956519 * 2 ^ 59
def prefixEnd_1956519 : Nat := 4983230072969 + 3 ^ 40 * 1956519 * 2
def baseEnd_1956519 : Nat := 111626072961570649346071

theorem tailTrace_1956519 : CollatzResearch.WordTrace tailWord_1956519 prefixEnd_1956519 111626072961570649346071 := by
  unfold tailWord_1956519
  simp only [CollatzResearch.WordTrace]
  refine ⟨71360110398873284687520611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47573406932582189791680407 71360110398873284687520611)
  ·
    refine ⟨107040165598309927031280917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71360110398873284687520611 107040165598309927031280917)
    ·
      refine ⟨5017507762420777829591293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107040165598309927031280917 5017507762420777829591293)
      ·
        refine ⟨1881565410907791686096735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5017507762420777829591293 1881565410907791686096735)
        ·
          refine ⟨2822348116361687529145103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881565410907791686096735 2822348116361687529145103)
          ·
            refine ⟨4233522174542531293717655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822348116361687529145103 4233522174542531293717655)
            ·
              refine ⟨6350283261813796940576483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233522174542531293717655 6350283261813796940576483)
              ·
                refine ⟨9525424892720695410864725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350283261813796940576483 9525424892720695410864725)
                ·
                  refine ⟨111626072961570649346071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9525424892720695410864725 111626072961570649346071)
                  ·
                    rfl

theorem cell23_1956519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 8].length) (baseStart_1956519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956519 prefixEnd_1956519 := by exact prefixLift 1956519
  have htrace : WordTrace (prefixWord ++ tailWord_1956519) baseStart_1956519 baseEnd_1956519 := by
    simpa [prefixWord, tailWord_1956519, baseEnd_1956519] using wordTrace_append hprefix tailTrace_1956519
  have hstable : (prefixWord ++ tailWord_1956519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956519).length < 2 ^ (prefixWord ++ tailWord_1956519).sum := by decide
  have hdescent : baseEnd_1956519 < baseStart_1956519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956557 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1956557 : Nat := 118140960795 + 1956557 * 2 ^ 59
def prefixEnd_1956557 : Nat := 4983230072969 + 3 ^ 40 * 1956557 * 2
def baseEnd_1956557 : Nat := 334884722973002231813155

theorem tailTrace_1956557 : CollatzResearch.WordTrace tailWord_1956557 prefixEnd_1956557 334884722973002231813155 := by
  unfold tailWord_1956557
  simp only [CollatzResearch.WordTrace]
  refine ⟨71361496372735617177403925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47574330915157078118269283 71361496372735617177403925)
  ·
    refine ⟨3345070142471982055190809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71361496372735617177403925 3345070142471982055190809)
    ·
      refine ⟨2508802606853986541393107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3345070142471982055190809 2508802606853986541393107)
      ·
        refine ⟨3763203910280979812089661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508802606853986541393107 3763203910280979812089661)
        ·
          refine ⟨1411201466355367429533623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3763203910280979812089661 1411201466355367429533623)
          ·
            refine ⟨2116802199533051144300435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411201466355367429533623 2116802199533051144300435)
            ·
              refine ⟨3175203299299576716450653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116802199533051144300435 3175203299299576716450653)
              ·
                refine ⟨1190701237237341268668995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175203299299576716450653 1190701237237341268668995)
                ·
                  refine ⟨1786051855856011903003493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190701237237341268668995 1786051855856011903003493)
                  ·
                    refine ⟨334884722973002231813155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1786051855856011903003493 334884722973002231813155)
                    ·
                      rfl

theorem cell23_1956557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1956557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956557 prefixEnd_1956557 := by exact prefixLift 1956557
  have htrace : WordTrace (prefixWord ++ tailWord_1956557) baseStart_1956557 baseEnd_1956557 := by
    simpa [prefixWord, tailWord_1956557, baseEnd_1956557] using wordTrace_append hprefix tailTrace_1956557
  have hstable : (prefixWord ++ tailWord_1956557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956557).length < 2 ^ (prefixWord ++ tailWord_1956557).sum := by decide
  have hdescent : baseEnd_1956557 < baseStart_1956557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956575 : List Nat := [1, 1, 2, 3, 2, 3, 11]
def baseStart_1956575 : Nat := 118140960795 + 1956575 * 2 ^ 59
def prefixEnd_1956575 : Nat := 4983230072969 + 3 ^ 40 * 1956575 * 2
def baseEnd_1956575 : Nat := 12403251994701081790301

theorem tailTrace_1956575 : CollatzResearch.WordTrace tailWord_1956575 prefixEnd_1956575 12403251994701081790301 := by
  unfold tailWord_1956575
  simp only [CollatzResearch.WordTrace]
  refine ⟨71362152886670406251559179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47574768591113604167706119 71362152886670406251559179)
  ·
    refine ⟨107043229330005609377338769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71362152886670406251559179 107043229330005609377338769)
    ·
      refine ⟨80282421997504207033004077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107043229330005609377338769 80282421997504207033004077)
      ·
        refine ⟨30105908249064077637376529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80282421997504207033004077 30105908249064077637376529)
        ·
          refine ⟨22579431186798058228032397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30105908249064077637376529 22579431186798058228032397)
          ·
            refine ⟨8467286695049271835512149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22579431186798058228032397 8467286695049271835512149)
            ·
              refine ⟨12403251994701081790301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8467286695049271835512149 12403251994701081790301)
              ·
                rfl

theorem cell23_1956575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 11].length) (baseStart_1956575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956575 prefixEnd_1956575 := by exact prefixLift 1956575
  have htrace : WordTrace (prefixWord ++ tailWord_1956575) baseStart_1956575 baseEnd_1956575 := by
    simpa [prefixWord, tailWord_1956575, baseEnd_1956575] using wordTrace_append hprefix tailTrace_1956575
  have hstable : (prefixWord ++ tailWord_1956575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956575).length < 2 ^ (prefixWord ++ tailWord_1956575).sum := by decide
  have hdescent : baseEnd_1956575 < baseStart_1956575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956579 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 4, 4]
def baseStart_1956579 : Nat := 118140960795 + 1956579 * 2 ^ 59
def prefixEnd_1956579 : Nat := 4983230072969 + 3 ^ 40 * 1956579 * 2
def baseEnd_1956579 : Nat := 334888488497801869788121

theorem tailTrace_1956579 : CollatzResearch.WordTrace tailWord_1956579 prefixEnd_1956579 334888488497801869788121 := by
  unfold tailWord_1956579
  simp only [CollatzResearch.WordTrace]
  refine ⟨71362298778655914934704791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47574865852437276623136527 71362298778655914934704791)
  ·
    refine ⟨107043448167983872402057187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71362298778655914934704791 107043448167983872402057187)
    ·
      refine ⟨160565172251975808603085781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107043448167983872402057187 160565172251975808603085781)
      ·
        refine ⟨3763246224655683014134823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 160565172251975808603085781 3763246224655683014134823)
        ·
          refine ⟨5644869336983524521202235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763246224655683014134823 5644869336983524521202235)
          ·
            refine ⟨8467304005475286781803353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644869336983524521202235 8467304005475286781803353)
            ·
              refine ⟨6350478004106465086352515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8467304005475286781803353 6350478004106465086352515)
              ·
                refine ⟨9525717006159697629528773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350478004106465086352515 9525717006159697629528773)
                ·
                  refine ⟨1786071938654943305536645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9525717006159697629528773 1786071938654943305536645)
                  ·
                    refine ⟨334888488497801869788121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1786071938654943305536645 334888488497801869788121)
                    ·
                      rfl

theorem cell23_1956579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 4].length) (baseStart_1956579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956579 prefixEnd_1956579 := by exact prefixLift 1956579
  have htrace : WordTrace (prefixWord ++ tailWord_1956579) baseStart_1956579 baseEnd_1956579 := by
    simpa [prefixWord, tailWord_1956579, baseEnd_1956579] using wordTrace_append hprefix tailTrace_1956579
  have hstable : (prefixWord ++ tailWord_1956579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956579).length < 2 ^ (prefixWord ++ tailWord_1956579).sum := by decide
  have hdescent : baseEnd_1956579 < baseStart_1956579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956589 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1956589 : Nat := 118140960795 + 1956589 * 2 ^ 59
def prefixEnd_1956589 : Nat := 4983230072969 + 3 ^ 40 * 1956589 * 2
def baseEnd_1956589 : Nat := 1004670600299950570239317

theorem tailTrace_1956589 : CollatzResearch.WordTrace tailWord_1956589 prefixEnd_1956589 1004670600299950570239317 := by
  unfold tailWord_1956589
  simp only [CollatzResearch.WordTrace]
  refine ⟨71362663508619686642568821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47575109005746457761712547 71362663508619686642568821)
  ·
    refine ⟨6690249703933095622740827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71362663508619686642568821 6690249703933095622740827)
    ·
      refine ⟨10035374555899643434111241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690249703933095622740827 10035374555899643434111241)
      ·
        refine ⟨7526530916924732575583431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10035374555899643434111241 7526530916924732575583431)
        ·
          refine ⟨11289796375387098863375147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526530916924732575583431 11289796375387098863375147)
          ·
            refine ⟨16934694563080648295062721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11289796375387098863375147 16934694563080648295062721)
            ·
              refine ⟨12701020922310486221297041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16934694563080648295062721 12701020922310486221297041)
              ·
                refine ⟨9525765691732864665972781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12701020922310486221297041 9525765691732864665972781)
                ·
                  refine ⟨3572162134399824249739793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9525765691732864665972781 3572162134399824249739793)
                  ·
                    refine ⟨2679121600799868187304845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572162134399824249739793 2679121600799868187304845)
                    ·
                      refine ⟨1004670600299950570239317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679121600799868187304845 1004670600299950570239317)
                      ·
                        rfl

theorem cell23_1956589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1956589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956589 prefixEnd_1956589 := by exact prefixLift 1956589
  have htrace : WordTrace (prefixWord ++ tailWord_1956589) baseStart_1956589 baseEnd_1956589 := by
    simpa [prefixWord, tailWord_1956589, baseEnd_1956589] using wordTrace_append hprefix tailTrace_1956589
  have hstable : (prefixWord ++ tailWord_1956589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956589).length < 2 ^ (prefixWord ++ tailWord_1956589).sum := by decide
  have hdescent : baseEnd_1956589 < baseStart_1956589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956595 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_1956595 : Nat := 118140960795 + 1956595 * 2 ^ 59
def prefixEnd_1956595 : Nat := 4983230072969 + 3 ^ 40 * 1956595 * 2
def baseEnd_1956595 : Nat := 1004673681183877546764289

theorem tailTrace_1956595 : CollatzResearch.WordTrace tailWord_1956595 prefixEnd_1956595 1004673681183877546764289 := by
  unfold tailWord_1956595
  simp only [CollatzResearch.WordTrace]
  refine ⟨71362882346597949667287239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47575254897731966444858159 71362882346597949667287239)
  ·
    refine ⟨107044323519896924500930859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71362882346597949667287239 107044323519896924500930859)
    ·
      refine ⟨160566485279845386751396289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107044323519896924500930859 160566485279845386751396289)
      ·
        refine ⟨120424863959884040063547217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160566485279845386751396289 120424863959884040063547217)
        ·
          refine ⟨90318647969913030047660413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120424863959884040063547217 90318647969913030047660413)
          ·
            refine ⟨33869492988717386267872655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90318647969913030047660413 33869492988717386267872655)
            ·
              refine ⟨50804239483076079401808983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33869492988717386267872655 50804239483076079401808983)
              ·
                refine ⟨76206359224614119102713475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50804239483076079401808983 76206359224614119102713475)
                ·
                  refine ⟨114309538836921178654070213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76206359224614119102713475 114309538836921178654070213)
                  ·
                    refine ⟨21433038531922720997638165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114309538836921178654070213 21433038531922720997638165)
                    ·
                      refine ⟨1004673681183877546764289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21433038531922720997638165 1004673681183877546764289)
                      ·
                        rfl

theorem cell23_1956595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_1956595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956595 prefixEnd_1956595 := by exact prefixLift 1956595
  have htrace : WordTrace (prefixWord ++ tailWord_1956595) baseStart_1956595 baseEnd_1956595 := by
    simpa [prefixWord, tailWord_1956595, baseEnd_1956595] using wordTrace_append hprefix tailTrace_1956595
  have hstable : (prefixWord ++ tailWord_1956595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956595).length < 2 ^ (prefixWord ++ tailWord_1956595).sum := by decide
  have hdescent : baseEnd_1956595 < baseStart_1956595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956606 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1956606 : Nat := 118140960795 + 1956606 * 2 ^ 59
def prefixEnd_1956606 : Nat := 4983230072969 + 3 ^ 40 * 1956606 * 2
def baseEnd_1956606 : Nat := 1004679329471077003726739

theorem tailTrace_1956606 : CollatzResearch.WordTrace tailWord_1956606 prefixEnd_1956606 1004679329471077003726739 := by
  unfold tailWord_1956606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920410443694762318242209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47575522366372065697291781 8920410443694762318242209)
  ·
    refine ⟨6690307832771071738681657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8920410443694762318242209 6690307832771071738681657)
    ·
      refine ⟨5017730874578303804011243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6690307832771071738681657 5017730874578303804011243)
      ·
        refine ⟨7526596311867455706016865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017730874578303804011243 7526596311867455706016865)
        ·
          refine ⟨5644947233900591779512649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7526596311867455706016865 5644947233900591779512649)
          ·
            refine ⟨4233710425425443834634487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644947233900591779512649 4233710425425443834634487)
            ·
              refine ⟨6350565638138165751951731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233710425425443834634487 6350565638138165751951731)
              ·
                refine ⟨9525848457207248627927597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350565638138165751951731 9525848457207248627927597)
                ·
                  refine ⟨3572193171452718235472849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9525848457207248627927597 3572193171452718235472849)
                  ·
                    refine ⟨2679144878589538676604637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572193171452718235472849 2679144878589538676604637)
                    ·
                      refine ⟨1004679329471077003726739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679144878589538676604637 1004679329471077003726739)
                      ·
                        rfl

theorem cell23_1956606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1956606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956606 prefixEnd_1956606 := by exact prefixLift 1956606
  have htrace : WordTrace (prefixWord ++ tailWord_1956606) baseStart_1956606 baseEnd_1956606 := by
    simpa [prefixWord, tailWord_1956606, baseEnd_1956606] using wordTrace_append hprefix tailTrace_1956606
  have hstable : (prefixWord ++ tailWord_1956606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956606).length < 2 ^ (prefixWord ++ tailWord_1956606).sum := by decide
  have hdescent : baseEnd_1956606 < baseStart_1956606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956636 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1956636 : Nat := 118140960795 + 1956636 * 2 ^ 59
def prefixEnd_1956636 : Nat := 4983230072969 + 3 ^ 40 * 1956636 * 2
def baseEnd_1956636 : Nat := 1004694733890711886351601

theorem tailTrace_1956636 : CollatzResearch.WordTrace tailWord_1956636 prefixEnd_1956636 1004694733890711886351601 := by
  unfold tailWord_1956636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682188869724706834764881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47576251826299609113019841 35682188869724706834764881)
  ·
    refine ⟨26761641652293530126073661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35682188869724706834764881 26761641652293530126073661)
    ·
      refine ⟨10035615619610073797277623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26761641652293530126073661 10035615619610073797277623)
      ·
        refine ⟨15053423429415110695916435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035615619610073797277623 15053423429415110695916435)
        ·
          refine ⟨22580135144122666043874653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15053423429415110695916435 22580135144122666043874653)
          ·
            refine ⟨8467550679045999766452995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22580135144122666043874653 8467550679045999766452995)
            ·
              refine ⟨12701326018568999649679493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467550679045999766452995 12701326018568999649679493)
              ·
                refine ⟨2381498628481687434314905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12701326018568999649679493 2381498628481687434314905)
                ·
                  refine ⟨1786123971361265575736179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381498628481687434314905 1786123971361265575736179)
                  ·
                    refine ⟨2679185957041898363604269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1786123971361265575736179 2679185957041898363604269)
                    ·
                      refine ⟨1004694733890711886351601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679185957041898363604269 1004694733890711886351601)
                      ·
                        rfl

theorem cell23_1956636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1956636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956636 prefixEnd_1956636 := by exact prefixLift 1956636
  have htrace : WordTrace (prefixWord ++ tailWord_1956636) baseStart_1956636 baseEnd_1956636 := by
    simpa [prefixWord, tailWord_1956636, baseEnd_1956636] using wordTrace_append hprefix tailTrace_1956636
  have hstable : (prefixWord ++ tailWord_1956636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956636).length < 2 ^ (prefixWord ++ tailWord_1956636).sum := by decide
  have hdescent : baseEnd_1956636 < baseStart_1956636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956637 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1956637 : Nat := 118140960795 + 1956637 * 2 ^ 59
def prefixEnd_1956637 : Nat := 4983230072969 + 3 ^ 40 * 1956637 * 2
def baseEnd_1956637 : Nat := 1004695247371366382439097

theorem tailTrace_1956637 : CollatzResearch.WordTrace tailWord_1956637 prefixEnd_1956637 1004695247371366382439097 := by
  unfold tailWord_1956637
  simp only [CollatzResearch.WordTrace]
  refine ⟨71364414212445790840316165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47576276141630527226877443 71364414212445790840316165)
  ·
    refine ⟨13380827664833585782559281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71364414212445790840316165 13380827664833585782559281)
    ·
      refine ⟨10035620748625189336919461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13380827664833585782559281 10035620748625189336919461)
      ·
        refine ⟨1881678890367223000672399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10035620748625189336919461 1881678890367223000672399)
        ·
          refine ⟨2822518335550834501008599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881678890367223000672399 2822518335550834501008599)
          ·
            refine ⟨4233777503326251751512899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822518335550834501008599 4233777503326251751512899)
            ·
              refine ⟨6350666254989377627269349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233777503326251751512899 6350666254989377627269349)
              ·
                refine ⟨1190749922810508305113003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6350666254989377627269349 1190749922810508305113003)
                ·
                  refine ⟨1786124884215762457669505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190749922810508305113003 1786124884215762457669505)
                  ·
                    refine ⟨1339593663161821843252129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786124884215762457669505 1339593663161821843252129)
                    ·
                      refine ⟨1004695247371366382439097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339593663161821843252129 1004695247371366382439097)
                      ·
                        rfl

theorem cell23_1956637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1956637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956637 prefixEnd_1956637 := by exact prefixLift 1956637
  have htrace : WordTrace (prefixWord ++ tailWord_1956637) baseStart_1956637 baseEnd_1956637 := by
    simpa [prefixWord, tailWord_1956637, baseEnd_1956637] using wordTrace_append hprefix tailTrace_1956637
  have hstable : (prefixWord ++ tailWord_1956637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956637).length < 2 ^ (prefixWord ++ tailWord_1956637).sum := by decide
  have hdescent : baseEnd_1956637 < baseStart_1956637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956652 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1956652 : Nat := 118140960795 + 1956652 * 2 ^ 59
def prefixEnd_1956652 : Nat := 4983230072969 + 3 ^ 40 * 1956652 * 2
def baseEnd_1956652 : Nat := 334900983193727941250509

theorem tailTrace_1956652 : CollatzResearch.WordTrace tailWord_1956652 prefixEnd_1956652 334900983193727941250509 := by
  unfold tailWord_1956652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682480653695724201056105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47576640871594298934741473 35682480653695724201056105)
  ·
    refine ⟨26761860490271793150792079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35682480653695724201056105 26761860490271793150792079)
    ·
      refine ⟨40142790735407689726188119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26761860490271793150792079 40142790735407689726188119)
      ·
        refine ⟨60214186103111534589282179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40142790735407689726188119 60214186103111534589282179)
        ·
          refine ⟨90321279154667301883923269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60214186103111534589282179 90321279154667301883923269)
          ·
            refine ⟨16935239841500119103235613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90321279154667301883923269 16935239841500119103235613)
            ·
              refine ⟨6350714940562544663713355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16935239841500119103235613 6350714940562544663713355)
              ·
                refine ⟨9526072410843816995570033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350714940562544663713355 9526072410843816995570033)
                ·
                  refine ⟨7144554308132862746677525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526072410843816995570033 7144554308132862746677525)
                  ·
                    refine ⟨334900983193727941250509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7144554308132862746677525 334900983193727941250509)
                    ·
                      rfl

theorem cell23_1956652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1956652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956652 prefixEnd_1956652 := by exact prefixLift 1956652
  have htrace : WordTrace (prefixWord ++ tailWord_1956652) baseStart_1956652 baseEnd_1956652 := by
    simpa [prefixWord, tailWord_1956652, baseEnd_1956652] using wordTrace_append hprefix tailTrace_1956652
  have hstable : (prefixWord ++ tailWord_1956652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956652).length < 2 ^ (prefixWord ++ tailWord_1956652).sum := by decide
  have hdescent : baseEnd_1956652 < baseStart_1956652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956709 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1956709 : Nat := 118140960795 + 1956709 * 2 ^ 59
def prefixEnd_1956709 : Nat := 4983230072969 + 3 ^ 40 * 1956709 * 2
def baseEnd_1956709 : Nat := 1004732217978490100738765

theorem tailTrace_1956709 : CollatzResearch.WordTrace tailWord_1956709 prefixEnd_1956709 1004732217978490100738765 := by
  unfold tailWord_1956709
  simp only [CollatzResearch.WordTrace]
  refine ⟨71367040268184947136937181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47578026845456631424624787 71367040268184947136937181)
  ·
    refine ⟨26762640100569355176351443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71367040268184947136937181 26762640100569355176351443)
    ·
      refine ⟨40143960150854032764527165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26762640100569355176351443 40143960150854032764527165)
      ·
        refine ⟨15053985056570262286697687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40143960150854032764527165 15053985056570262286697687)
        ·
          refine ⟨22580977584855393430046531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15053985056570262286697687 22580977584855393430046531)
          ·
            refine ⟨33871466377283090145069797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22580977584855393430046531 33871466377283090145069797)
            ·
              refine ⟨6350899945740579402200587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33871466377283090145069797 6350899945740579402200587)
              ·
                refine ⟨9526349918610869103300881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350899945740579402200587 9526349918610869103300881)
                ·
                  refine ⟨7144762438958151827475661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526349918610869103300881 7144762438958151827475661)
                  ·
                    refine ⟨2679285914609306935303373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7144762438958151827475661 2679285914609306935303373)
                    ·
                      refine ⟨1004732217978490100738765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679285914609306935303373 1004732217978490100738765)
                      ·
                        rfl

theorem cell23_1956709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1956709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956709 prefixEnd_1956709 := by exact prefixLift 1956709
  have htrace : WordTrace (prefixWord ++ tailWord_1956709) baseStart_1956709 baseEnd_1956709 := by
    simpa [prefixWord, tailWord_1956709, baseEnd_1956709] using wordTrace_append hprefix tailTrace_1956709
  have hstable : (prefixWord ++ tailWord_1956709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956709).length < 2 ^ (prefixWord ++ tailWord_1956709).sum := by decide
  have hdescent : baseEnd_1956709 < baseStart_1956709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956719 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 5, 2]
def baseStart_1956719 : Nat := 118140960795 + 1956719 * 2 ^ 59
def prefixEnd_1956719 : Nat := 4983230072969 + 3 ^ 40 * 1956719 * 2
def baseEnd_1956719 : Nat := 1004737352785035061613719

theorem tailTrace_1956719 : CollatzResearch.WordTrace tailWord_1956719 prefixEnd_1956719 1004737352785035061613719 := by
  unfold tailWord_1956719
  simp only [CollatzResearch.WordTrace]
  refine ⟨71367404998148718844801211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47578269998765812563200807 71367404998148718844801211)
  ·
    refine ⟨107051107497223078267201817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71367404998148718844801211 107051107497223078267201817)
    ·
      refine ⟨80288330622917308700401363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107051107497223078267201817 80288330622917308700401363)
      ·
        refine ⟨120432495934375963050602045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80288330622917308700401363 120432495934375963050602045)
        ·
          refine ⟨45162185975390986143975767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120432495934375963050602045 45162185975390986143975767)
          ·
            refine ⟨67743278963086479215963651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45162185975390986143975767 67743278963086479215963651)
            ·
              refine ⟨101614918444629718823945477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67743278963086479215963651 101614918444629718823945477)
              ·
                refine ⟨19052797208368072279489777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101614918444629718823945477 19052797208368072279489777)
                ·
                  refine ⟨14289597906276054209617333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19052797208368072279489777 14289597906276054209617333)
                  ·
                    refine ⟨1339649803713380082151625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14289597906276054209617333 1339649803713380082151625)
                    ·
                      refine ⟨1004737352785035061613719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339649803713380082151625 1004737352785035061613719)
                      ·
                        rfl

theorem cell23_1956719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5, 2].length) (baseStart_1956719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956719 prefixEnd_1956719 := by exact prefixLift 1956719
  have htrace : WordTrace (prefixWord ++ tailWord_1956719) baseStart_1956719 baseEnd_1956719 := by
    simpa [prefixWord, tailWord_1956719, baseEnd_1956719] using wordTrace_append hprefix tailTrace_1956719
  have hstable : (prefixWord ++ tailWord_1956719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956719).length < 2 ^ (prefixWord ++ tailWord_1956719).sum := by decide
  have hdescent : baseEnd_1956719 < baseStart_1956719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956746 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1956746 : Nat := 118140960795 + 1956746 * 2 ^ 59
def prefixEnd_1956746 : Nat := 4983230072969 + 3 ^ 40 * 1956746 * 2
def baseEnd_1956746 : Nat := 334917072254235485325365

theorem tailTrace_1956746 : CollatzResearch.WordTrace tailWord_1956746 prefixEnd_1956746 334917072254235485325365 := by
  unfold tailWord_1956746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842097442262725614008523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47578926512700601637356061 17842097442262725614008523)
  ·
    refine ⟨26763146163394088421012785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17842097442262725614008523 26763146163394088421012785)
    ·
      refine ⟨20072359622545566315759589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26763146163394088421012785 20072359622545566315759589)
      ·
        refine ⟨3763567429227293684204923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20072359622545566315759589 3763567429227293684204923)
        ·
          refine ⟨5645351143840940526307385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763567429227293684204923 5645351143840940526307385)
          ·
            refine ⟨4234013357880705394730539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645351143840940526307385 4234013357880705394730539)
            ·
              refine ⟨6351020036821058092095809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234013357880705394730539 6351020036821058092095809)
              ·
                refine ⟨4763265027615793569071857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351020036821058092095809 4763265027615793569071857)
                ·
                  refine ⟨3572448770711845176803893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4763265027615793569071857 3572448770711845176803893)
                  ·
                    refine ⟨334917072254235485325365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3572448770711845176803893 334917072254235485325365)
                    ·
                      rfl

theorem cell23_1956746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1956746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956746 prefixEnd_1956746 := by exact prefixLift 1956746
  have htrace : WordTrace (prefixWord ++ tailWord_1956746) baseStart_1956746 baseEnd_1956746 := by
    simpa [prefixWord, tailWord_1956746, baseEnd_1956746] using wordTrace_append hprefix tailTrace_1956746
  have hstable : (prefixWord ++ tailWord_1956746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956746).length < 2 ^ (prefixWord ++ tailWord_1956746).sum := by decide
  have hdescent : baseEnd_1956746 < baseStart_1956746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956816 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3]
def baseStart_1956816 : Nat := 118140960795 + 1956816 * 2 ^ 59
def prefixEnd_1956816 : Nat := 4983230072969 + 3 ^ 40 * 1956816 * 2
def baseEnd_1956816 : Nat := 1004787160408521182100773

theorem tailTrace_1956816 : CollatzResearch.WordTrace tailWord_1956816 prefixEnd_1956816 1004787160408521182100773 := by
  unfold tailWord_1956816
  simp only [CollatzResearch.WordTrace]
  refine ⟨35685471439398652205541151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47580628585864869607388201 35685471439398652205541151)
  ·
    refine ⟨53528207159097978308311727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35685471439398652205541151 53528207159097978308311727)
    ·
      refine ⟨80292310738646967462467591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53528207159097978308311727 80292310738646967462467591)
      ·
        refine ⟨120438466107970451193701387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80292310738646967462467591 120438466107970451193701387)
        ·
          refine ⟨180657699161955676790552081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120438466107970451193701387 180657699161955676790552081)
          ·
            refine ⟨135493274371466757592914061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180657699161955676790552081 135493274371466757592914061)
            ·
              refine ⟨50809977889300034097342773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135493274371466757592914061 50809977889300034097342773)
              ·
                refine ⟨4763435427121878196625885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50809977889300034097342773 4763435427121878196625885)
                ·
                  refine ⟨1786288285170704323734707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4763435427121878196625885 1786288285170704323734707)
                  ·
                    refine ⟨2679432427756056485602061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1786288285170704323734707 2679432427756056485602061)
                    ·
                      refine ⟨1004787160408521182100773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679432427756056485602061 1004787160408521182100773)
                      ·
                        rfl

theorem cell23_1956816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_1956816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956816 prefixEnd_1956816 := by exact prefixLift 1956816
  have htrace : WordTrace (prefixWord ++ tailWord_1956816) baseStart_1956816 baseEnd_1956816 := by
    simpa [prefixWord, tailWord_1956816, baseEnd_1956816] using wordTrace_append hprefix tailTrace_1956816
  have hstable : (prefixWord ++ tailWord_1956816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956816).length < 2 ^ (prefixWord ++ tailWord_1956816).sum := by decide
  have hdescent : baseEnd_1956816 < baseStart_1956816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956837 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1956837 : Nat := 118140960795 + 1956837 * 2 ^ 59
def prefixEnd_1956837 : Nat := 4983230072969 + 3 ^ 40 * 1956837 * 2
def baseEnd_1956837 : Nat := 1004797943502265599938177

theorem tailTrace_1956837 : CollatzResearch.WordTrace tailWord_1956837 prefixEnd_1956837 1004797943502265599938177 := by
  unfold tailWord_1956837
  simp only [CollatzResearch.WordTrace]
  refine ⟨71371708811721224997596765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47581139207814149998397843 71371708811721224997596765)
  ·
    refine ⟨26764390804395459374098787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71371708811721224997596765 26764390804395459374098787)
    ·
      refine ⟨40146586206593189061148181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26764390804395459374098787 40146586206593189061148181)
      ·
        refine ⟨1881871228434055737241321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40146586206593189061148181 1881871228434055737241321)
        ·
          refine ⟨1411403421325541802930991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881871228434055737241321 1411403421325541802930991)
          ·
            refine ⟨2117105131988312704396487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411403421325541802930991 2117105131988312704396487)
            ·
              refine ⟨3175657697982469056594731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117105131988312704396487 3175657697982469056594731)
              ·
                refine ⟨4763486546973703584892097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175657697982469056594731 4763486546973703584892097)
                ·
                  refine ⟨3572614910230277688669073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4763486546973703584892097 3572614910230277688669073)
                  ·
                    refine ⟨2679461182672708266501805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572614910230277688669073 2679461182672708266501805)
                    ·
                      refine ⟨1004797943502265599938177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679461182672708266501805 1004797943502265599938177)
                      ·
                        rfl

theorem cell23_1956837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1956837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956837 prefixEnd_1956837 := by exact prefixLift 1956837
  have htrace : WordTrace (prefixWord ++ tailWord_1956837) baseStart_1956837 baseEnd_1956837 := by
    simpa [prefixWord, tailWord_1956837, baseEnd_1956837] using wordTrace_append hprefix tailTrace_1956837
  have hstable : (prefixWord ++ tailWord_1956837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956837).length < 2 ^ (prefixWord ++ tailWord_1956837).sum := by decide
  have hdescent : baseEnd_1956837 < baseStart_1956837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956859 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5]
def baseStart_1956859 : Nat := 118140960795 + 1956859 * 2 ^ 59
def prefixEnd_1956859 : Nat := 4983230072969 + 3 ^ 40 * 1956859 * 2
def baseEnd_1956859 : Nat := 1004809240076664513863075

theorem tailTrace_1956859 : CollatzResearch.WordTrace tailWord_1956859 prefixEnd_1956859 1004809240076664513863075 := by
  unfold tailWord_1956859
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372511217641522754897631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47581674145094348503265087 71372511217641522754897631)
  ·
    refine ⟨107058766826462284132346447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71372511217641522754897631 107058766826462284132346447)
    ·
      refine ⟨160588150239693426198519671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107058766826462284132346447 160588150239693426198519671)
      ·
        refine ⟨240882225359540139297779507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160588150239693426198519671 240882225359540139297779507)
        ·
          refine ⟨361323338039310208946669261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240882225359540139297779507 361323338039310208946669261)
          ·
            refine ⟨135496251764741328355000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361323338039310208946669261 135496251764741328355000973)
            ·
              refine ⟨50811094411777998133125365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135496251764741328355000973 50811094411777998133125365)
              ·
                refine ⟨4763540101104187324980503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50811094411777998133125365 4763540101104187324980503)
                ·
                  refine ⟨7145310151656280987470755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763540101104187324980503 7145310151656280987470755)
                  ·
                    refine ⟨10717965227484421481206133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145310151656280987470755 10717965227484421481206133)
                    ·
                      refine ⟨1004809240076664513863075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10717965227484421481206133 1004809240076664513863075)
                      ·
                        rfl

theorem cell23_1956859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_1956859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956859 prefixEnd_1956859 := by exact prefixLift 1956859
  have htrace : WordTrace (prefixWord ++ tailWord_1956859) baseStart_1956859 baseEnd_1956859 := by
    simpa [prefixWord, tailWord_1956859, baseEnd_1956859] using wordTrace_append hprefix tailTrace_1956859
  have hstable : (prefixWord ++ tailWord_1956859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956859).length < 2 ^ (prefixWord ++ tailWord_1956859).sum := by decide
  have hdescent : baseEnd_1956859 < baseStart_1956859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956869 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1956869 : Nat := 118140960795 + 1956869 * 2 ^ 59
def prefixEnd_1956869 : Nat := 4983230072969 + 3 ^ 40 * 1956869 * 2
def baseEnd_1956869 : Nat := 1004814374883209474738029

theorem tailTrace_1956869 : CollatzResearch.WordTrace tailWord_1956869 prefixEnd_1956869 1004814374883209474738029 := by
  unfold tailWord_1956869
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372875947605294462761661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47581917298403529641841107 71372875947605294462761661)
  ·
    refine ⟨26764828480351985423535623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71372875947605294462761661 26764828480351985423535623)
    ·
      refine ⟨40147242720527978135303435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26764828480351985423535623 40147242720527978135303435)
      ·
        refine ⟨60220864080791967202955153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40147242720527978135303435 60220864080791967202955153)
        ·
          refine ⟨45165648060593975402216365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60220864080791967202955153 45165648060593975402216365)
          ·
            refine ⟨16937118022722740775831137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45165648060593975402216365 16937118022722740775831137)
            ·
              refine ⟨12702838517042055581873353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16937118022722740775831137 12702838517042055581873353)
              ·
                refine ⟨9527128887781541686405015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702838517042055581873353 9527128887781541686405015)
                ·
                  refine ⟨14290693331672312529607523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527128887781541686405015 14290693331672312529607523)
                  ·
                    refine ⟨21436039997508468794411285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14290693331672312529607523 21436039997508468794411285)
                    ·
                      refine ⟨1004814374883209474738029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21436039997508468794411285 1004814374883209474738029)
                      ·
                        rfl

theorem cell23_1956869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1956869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956869 prefixEnd_1956869 := by exact prefixLift 1956869
  have htrace : WordTrace (prefixWord ++ tailWord_1956869) baseStart_1956869 baseEnd_1956869 := by
    simpa [prefixWord, tailWord_1956869, baseEnd_1956869] using wordTrace_append hprefix tailTrace_1956869
  have hstable : (prefixWord ++ tailWord_1956869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956869).length < 2 ^ (prefixWord ++ tailWord_1956869).sum := by decide
  have hdescent : baseEnd_1956869 < baseStart_1956869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956876 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1956876 : Nat := 118140960795 + 1956876 * 2 ^ 59
def prefixEnd_1956876 : Nat := 4983230072969 + 3 ^ 40 * 1956876 * 2
def baseEnd_1956876 : Nat := 1004817969247790947350497

theorem tailTrace_1956876 : CollatzResearch.WordTrace tailWord_1956876 prefixEnd_1956876 1004817969247790947350497 := by
  unfold tailWord_1956876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686565629289967329133241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47582087505719956438844321 35686565629289967329133241)
  ·
    refine ⟨26764924221967475496849931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35686565629289967329133241 26764924221967475496849931)
    ·
      refine ⟨40147386332951213245274897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26764924221967475496849931 40147386332951213245274897)
      ·
        refine ⟨30110539749713409933956173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40147386332951213245274897 30110539749713409933956173)
        ·
          refine ⟨11291452406142528725233565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30110539749713409933956173 11291452406142528725233565)
          ·
            refine ⟨4234294652303448271962587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11291452406142528725233565 4234294652303448271962587)
            ·
              refine ⟨6351441978455172407943881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234294652303448271962587 6351441978455172407943881)
              ·
                refine ⟨4763581483841379305957911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351441978455172407943881 4763581483841379305957911)
                ·
                  refine ⟨7145372225762068958936867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763581483841379305957911 7145372225762068958936867)
                  ·
                    refine ⟨10718058338643103438405301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145372225762068958936867 10718058338643103438405301)
                    ·
                      refine ⟨1004817969247790947350497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10718058338643103438405301 1004817969247790947350497)
                      ·
                        rfl

theorem cell23_1956876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1956876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956876 prefixEnd_1956876 := by exact prefixLift 1956876
  have htrace : WordTrace (prefixWord ++ tailWord_1956876) baseStart_1956876 baseEnd_1956876 := by
    simpa [prefixWord, tailWord_1956876, baseEnd_1956876] using wordTrace_append hprefix tailTrace_1956876
  have hstable : (prefixWord ++ tailWord_1956876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956876).length < 2 ^ (prefixWord ++ tailWord_1956876).sum := by decide
  have hdescent : baseEnd_1956876 < baseStart_1956876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956919 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1956919 : Nat := 118140960795 + 1956919 * 2 ^ 59
def prefixEnd_1956919 : Nat := 4983230072969 + 3 ^ 40 * 1956919 * 2
def baseEnd_1956919 : Nat := 1004840048915934279112799

theorem tailTrace_1956919 : CollatzResearch.WordTrace tailWord_1956919 prefixEnd_1956919 1004840048915934279112799 := by
  unfold tailWord_1956919
  simp only [CollatzResearch.WordTrace]
  refine ⟨71374699597424153002081811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47583133064949435334721207 71374699597424153002081811)
  ·
    refine ⟨107062049396136229503122717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71374699597424153002081811 107062049396136229503122717)
    ·
      refine ⟨40148268523551086063671019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107062049396136229503122717 40148268523551086063671019)
      ·
        refine ⟨60222402785326629095506529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40148268523551086063671019 60222402785326629095506529)
        ·
          refine ⟨45166802088994971821629897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60222402785326629095506529 45166802088994971821629897)
          ·
            refine ⟨33875101566746228866222423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45166802088994971821629897 33875101566746228866222423)
            ·
              refine ⟨50812652350119343299333635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33875101566746228866222423 50812652350119343299333635)
              ·
                refine ⟨76218978525179014949000453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50812652350119343299333635 76218978525179014949000453)
                ·
                  refine ⟨14291058473471065302937585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76218978525179014949000453 14291058473471065302937585)
                  ·
                    refine ⟨10718293855103298977203189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14291058473471065302937585 10718293855103298977203189)
                    ·
                      refine ⟨1004840048915934279112799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10718293855103298977203189 1004840048915934279112799)
                      ·
                        rfl

theorem cell23_1956919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1956919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956919 prefixEnd_1956919 := by exact prefixLift 1956919
  have htrace : WordTrace (prefixWord ++ tailWord_1956919) baseStart_1956919 baseEnd_1956919 := by
    simpa [prefixWord, tailWord_1956919, baseEnd_1956919] using wordTrace_append hprefix tailTrace_1956919
  have hstable : (prefixWord ++ tailWord_1956919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956919).length < 2 ^ (prefixWord ++ tailWord_1956919).sum := by decide
  have hdescent : baseEnd_1956919 < baseStart_1956919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956924 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_1956924 : Nat := 118140960795 + 1956924 * 2 ^ 59
def prefixEnd_1956924 : Nat := 4983230072969 + 3 ^ 40 * 1956924 * 2
def baseEnd_1956924 : Nat := 1004842616319206759550277

theorem tailTrace_1956924 : CollatzResearch.WordTrace tailWord_1956924 prefixEnd_1956924 1004842616319206759550277 := by
  unfold tailWord_1956924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687440981203019428006913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47583254641604025904009217 35687440981203019428006913)
  ·
    refine ⟨26765580735902264571005185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35687440981203019428006913 26765580735902264571005185)
    ·
      refine ⟨20074185551926698428253889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26765580735902264571005185 20074185551926698428253889)
      ·
        refine ⟨15055639163945023821190417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20074185551926698428253889 15055639163945023821190417)
        ·
          refine ⟨11291729372958767865892813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15055639163945023821190417 11291729372958767865892813)
          ·
            refine ⟨4234398514859537949709805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11291729372958767865892813 4234398514859537949709805)
            ·
              refine ⟨1587899443072326731141177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4234398514859537949709805 1587899443072326731141177)
              ·
                refine ⟨1190924582304245048355883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587899443072326731141177 1190924582304245048355883)
                ·
                  refine ⟨1786386873456367572533825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190924582304245048355883 1786386873456367572533825)
                  ·
                    refine ⟨1339790155092275679400369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786386873456367572533825 1339790155092275679400369)
                    ·
                      refine ⟨1004842616319206759550277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339790155092275679400369 1004842616319206759550277)
                      ·
                        rfl

theorem cell23_1956924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_1956924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956924 prefixEnd_1956924 := by exact prefixLift 1956924
  have htrace : WordTrace (prefixWord ++ tailWord_1956924) baseStart_1956924 baseEnd_1956924 := by
    simpa [prefixWord, tailWord_1956924, baseEnd_1956924] using wordTrace_append hprefix tailTrace_1956924
  have hstable : (prefixWord ++ tailWord_1956924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956924).length < 2 ^ (prefixWord ++ tailWord_1956924).sum := by decide
  have hdescent : baseEnd_1956924 < baseStart_1956924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956934 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1956934 : Nat := 118140960795 + 1956934 * 2 ^ 59
def prefixEnd_1956934 : Nat := 4983230072969 + 3 ^ 40 * 1956934 * 2
def baseEnd_1956934 : Nat := 334949250375250573475077

theorem tailTrace_1956934 : CollatzResearch.WordTrace tailWord_1956934 prefixEnd_1956934 334949250375250573475077 := by
  unfold tailWord_1956934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230476459136556580121183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47583497794913207042585237 2230476459136556580121183)
  ·
    refine ⟨3345714688704834870181775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230476459136556580121183 3345714688704834870181775)
    ·
      refine ⟨5018572033057252305272663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345714688704834870181775 5018572033057252305272663)
      ·
        refine ⟨7527858049585878457908995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018572033057252305272663 7527858049585878457908995)
        ·
          refine ⟨11291787074378817686863493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7527858049585878457908995 11291787074378817686863493)
          ·
            refine ⟨2117210076446028316286905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11291787074378817686863493 2117210076446028316286905)
            ·
              refine ⟨1587907557334521237215179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117210076446028316286905 1587907557334521237215179)
              ·
                refine ⟨2381861336001781855822769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587907557334521237215179 2381861336001781855822769)
                ·
                  refine ⟨1786396002001336391867077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381861336001781855822769 1786396002001336391867077)
                  ·
                    refine ⟨334949250375250573475077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1786396002001336391867077 334949250375250573475077)
                    ·
                      rfl

theorem cell23_1956934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1956934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956934 prefixEnd_1956934 := by exact prefixLift 1956934
  have htrace : WordTrace (prefixWord ++ tailWord_1956934) baseStart_1956934 baseEnd_1956934 := by
    simpa [prefixWord, tailWord_1956934, baseEnd_1956934] using wordTrace_append hprefix tailTrace_1956934
  have hstable : (prefixWord ++ tailWord_1956934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956934).length < 2 ^ (prefixWord ++ tailWord_1956934).sum := by decide
  have hdescent : baseEnd_1956934 < baseStart_1956934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956967 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_1956967 : Nat := 118140960795 + 1956967 * 2 ^ 59
def prefixEnd_1956967 : Nat := 4983230072969 + 3 ^ 40 * 1956967 * 2
def baseEnd_1956967 : Nat := 1004864695987350091312579

theorem tailTrace_1956967 : CollatzResearch.WordTrace tailWord_1956967 prefixEnd_1956967 1004864695987350091312579 := by
  unfold tailWord_1956967
  simp only [CollatzResearch.WordTrace]
  refine ⟨71376450301250257199829155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47584300200833504799886103 71376450301250257199829155)
  ·
    refine ⟨107064675451875385799743733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71376450301250257199829155 107064675451875385799743733)
    ·
      refine ⟨10037313323613317418725975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107064675451875385799743733 10037313323613317418725975)
      ·
        refine ⟨15055969985419976128088963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037313323613317418725975 15055969985419976128088963)
        ·
          refine ⟨22583954978129964192133445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055969985419976128088963 22583954978129964192133445)
          ·
            refine ⟨4234491558399368286025021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22583954978129964192133445 4234491558399368286025021)
            ·
              refine ⟨1587934334399763107259383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4234491558399368286025021 1587934334399763107259383)
              ·
                refine ⟨2381901501599644660889075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587934334399763107259383 2381901501599644660889075)
                ·
                  refine ⟨3572852252399466991333613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381901501599644660889075 3572852252399466991333613)
                  ·
                    refine ⟨1339819594649800121750105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572852252399466991333613 1339819594649800121750105)
                    ·
                      refine ⟨1004864695987350091312579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339819594649800121750105 1004864695987350091312579)
                      ·
                        rfl

theorem cell23_1956967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_1956967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956967 prefixEnd_1956967 := by exact prefixLift 1956967
  have htrace : WordTrace (prefixWord ++ tailWord_1956967) baseStart_1956967 baseEnd_1956967 := by
    simpa [prefixWord, tailWord_1956967, baseEnd_1956967] using wordTrace_append hprefix tailTrace_1956967
  have hstable : (prefixWord ++ tailWord_1956967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956967).length < 2 ^ (prefixWord ++ tailWord_1956967).sum := by decide
  have hdescent : baseEnd_1956967 < baseStart_1956967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956976 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1956976 : Nat := 118140960795 + 1956976 * 2 ^ 59
def prefixEnd_1956976 : Nat := 4983230072969 + 3 ^ 40 * 1956976 * 2
def baseEnd_1956976 : Nat := 1004869317313240556100037

theorem tailTrace_1956976 : CollatzResearch.WordTrace tailWord_1956976 prefixEnd_1956976 1004869317313240556100037 := by
  unfold tailWord_1956976
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688389279108825868453391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47584519038811767824604521 35688389279108825868453391)
  ·
    refine ⟨53532583918663238802680087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35688389279108825868453391 53532583918663238802680087)
    ·
      refine ⟨80298875877994858204020131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53532583918663238802680087 80298875877994858204020131)
      ·
        refine ⟨120448313816992287306030197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80298875877994858204020131 120448313816992287306030197)
        ·
          refine ⟨11292029420343026934940331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120448313816992287306030197 11292029420343026934940331)
          ·
            refine ⟨16938044130514540402410497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292029420343026934940331 16938044130514540402410497)
            ·
              refine ⟨12703533097885905301807873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16938044130514540402410497 12703533097885905301807873)
              ·
                refine ⟨9527649823414428976355905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703533097885905301807873 9527649823414428976355905)
                ·
                  refine ⟨7145737367560821732266929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527649823414428976355905 7145737367560821732266929)
                  ·
                    refine ⟨5359303025670616299200197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145737367560821732266929 5359303025670616299200197)
                    ·
                      refine ⟨1004869317313240556100037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5359303025670616299200197 1004869317313240556100037)
                      ·
                        rfl

theorem cell23_1956976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1956976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956976 prefixEnd_1956976 := by exact prefixLift 1956976
  have htrace : WordTrace (prefixWord ++ tailWord_1956976) baseStart_1956976 baseEnd_1956976 := by
    simpa [prefixWord, tailWord_1956976, baseEnd_1956976] using wordTrace_append hprefix tailTrace_1956976
  have hstable : (prefixWord ++ tailWord_1956976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956976).length < 2 ^ (prefixWord ++ tailWord_1956976).sum := by decide
  have hdescent : baseEnd_1956976 < baseStart_1956976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956993 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1956993 : Nat := 118140960795 + 1956993 * 2 ^ 59
def prefixEnd_1956993 : Nat := 4983230072969 + 3 ^ 40 * 1956993 * 2
def baseEnd_1956993 : Nat := 1004878046484366989587459

theorem tailTrace_1956993 : CollatzResearch.WordTrace tailWord_1956993 prefixEnd_1956993 1004878046484366989587459 := by
  unfold tailWord_1956993
  simp only [CollatzResearch.WordTrace]
  refine ⟨71377398599156063640275633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47584932399437375760183755 71377398599156063640275633)
  ·
    refine ⟨53533048949367047730206725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71377398599156063640275633 53533048949367047730206725)
    ·
      refine ⟨10037446678006321449413761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53533048949367047730206725 10037446678006321449413761)
      ·
        refine ⟨7528085008504741087060321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10037446678006321449413761 7528085008504741087060321)
        ·
          refine ⟨5646063756378555815295241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7528085008504741087060321 5646063756378555815295241)
          ·
            refine ⟨4234547817283916861471431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5646063756378555815295241 4234547817283916861471431)
            ·
              refine ⟨6351821725925875292207147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234547817283916861471431 6351821725925875292207147)
              ·
                refine ⟨9527732588888812938310721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351821725925875292207147 9527732588888812938310721)
                ·
                  refine ⟨7145799441666609703733041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527732588888812938310721 7145799441666609703733041)
                  ·
                    refine ⟨5359349581249957277799781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145799441666609703733041 5359349581249957277799781)
                    ·
                      refine ⟨1004878046484366989587459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5359349581249957277799781 1004878046484366989587459)
                      ·
                        rfl

theorem cell23_1956993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1956993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956993 prefixEnd_1956993 := by exact prefixLift 1956993
  have htrace : WordTrace (prefixWord ++ tailWord_1956993) baseStart_1956993 baseEnd_1956993 := by
    simpa [prefixWord, tailWord_1956993, baseEnd_1956993] using wordTrace_append hprefix tailTrace_1956993
  have hstable : (prefixWord ++ tailWord_1956993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956993).length < 2 ^ (prefixWord ++ tailWord_1956993).sum := by decide
  have hdescent : baseEnd_1956993 < baseStart_1956993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957020 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 5]
def baseStart_1957020 : Nat := 118140960795 + 1957020 * 2 ^ 59
def prefixEnd_1957020 : Nat := 4983230072969 + 3 ^ 40 * 1957020 * 2
def baseEnd_1957020 : Nat := 111654656718004264883315

theorem tailTrace_1957020 : CollatzResearch.WordTrace tailWord_1957020 prefixEnd_1957020 111654656718004264883315 := by
  unfold tailWord_1957020
  simp only [CollatzResearch.WordTrace]
  refine ⟨35689191685029123625754257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47585588913372164834339009 35689191685029123625754257)
  ·
    refine ⟨26766893763771842719315693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35689191685029123625754257 26766893763771842719315693)
    ·
      refine ⟨10037585161414441019743385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26766893763771842719315693 10037585161414441019743385)
      ·
        refine ⟨7528188871060830764807539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10037585161414441019743385 7528188871060830764807539)
        ·
          refine ⟨11292283306591246147211309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528188871060830764807539 11292283306591246147211309)
          ·
            refine ⟨4234606239971717305204241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11292283306591246147211309 4234606239971717305204241)
            ·
              refine ⟨3175954679978787978903181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234606239971717305204241 3175954679978787978903181)
              ·
                refine ⟨1190983004992045492088693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175954679978787978903181 1190983004992045492088693)
                ·
                  refine ⟨111654656718004264883315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190983004992045492088693 111654656718004264883315)
                  ·
                    rfl

theorem cell23_1957020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_1957020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957020 prefixEnd_1957020 := by exact prefixLift 1957020
  have htrace : WordTrace (prefixWord ++ tailWord_1957020) baseStart_1957020 baseEnd_1957020 := by
    simpa [prefixWord, tailWord_1957020, baseEnd_1957020] using wordTrace_append hprefix tailTrace_1957020
  have hstable : (prefixWord ++ tailWord_1957020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957020).length < 2 ^ (prefixWord ++ tailWord_1957020).sum := by decide
  have hdescent : baseEnd_1957020 < baseStart_1957020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957073 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_1957073 : Nat := 118140960795 + 1957073 * 2 ^ 59
def prefixEnd_1957073 : Nat := 4983230072969 + 3 ^ 40 * 1957073 * 2
def baseEnd_1957073 : Nat := 1004919124936726676587091

theorem tailTrace_1957073 : CollatzResearch.WordTrace tailWord_1957073 prefixEnd_1957073 1004919124936726676587091 := by
  unfold tailWord_1957073
  simp only [CollatzResearch.WordTrace]
  refine ⟨71380316438866237303187873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47586877625910824868791915 71380316438866237303187873)
  ·
    refine ⟨53535237329149677977390905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71380316438866237303187873 53535237329149677977390905)
    ·
      refine ⟨40151427996862258483043179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53535237329149677977390905 40151427996862258483043179)
      ·
        refine ⟨60227141995293387724564769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40151427996862258483043179 60227141995293387724564769)
        ·
          refine ⟨45170356496470040793423577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60227141995293387724564769 45170356496470040793423577)
          ·
            refine ⟨33877767372352530595067683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45170356496470040793423577 33877767372352530595067683)
            ·
              refine ⟨50816651058528795892601525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33877767372352530595067683 50816651058528795892601525)
              ·
                refine ⟨4764061036737074614931393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50816651058528795892601525 4764061036737074614931393)
                ·
                  refine ⟨3573045777552805961198545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764061036737074614931393 3573045777552805961198545)
                  ·
                    refine ⟨2679784333164604470898909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573045777552805961198545 2679784333164604470898909)
                    ·
                      refine ⟨1004919124936726676587091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679784333164604470898909 1004919124936726676587091)
                      ·
                        rfl

theorem cell23_1957073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_1957073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957073 prefixEnd_1957073 := by exact prefixLift 1957073
  have htrace : WordTrace (prefixWord ++ tailWord_1957073) baseStart_1957073 baseEnd_1957073 := by
    simpa [prefixWord, tailWord_1957073, baseEnd_1957073] using wordTrace_append hprefix tailTrace_1957073
  have hstable : (prefixWord ++ tailWord_1957073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957073).length < 2 ^ (prefixWord ++ tailWord_1957073).sum := by decide
  have hdescent : baseEnd_1957073 < baseStart_1957073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957123 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 3, 5]
def baseStart_1957123 : Nat := 118140960795 + 1957123 * 2 ^ 59
def prefixEnd_1957123 : Nat := 4983230072969 + 3 ^ 40 * 1957123 * 2
def baseEnd_1957123 : Nat := 334981599656483826987287

theorem tailTrace_1957123 : CollatzResearch.WordTrace tailWord_1957123 prefixEnd_1957123 334981599656483826987287 := by
  unfold tailWord_1957123
  simp only [CollatzResearch.WordTrace]
  refine ⟨71382140088685095842508023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47588093392456730561672015 71382140088685095842508023)
  ·
    refine ⟨107073210133027643763762035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71382140088685095842508023 107073210133027643763762035)
    ·
      refine ⟨160609815199541465645643053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107073210133027643763762035 160609815199541465645643053)
      ·
        refine ⟨60228680699828049617116145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160609815199541465645643053 60228680699828049617116145)
        ·
          refine ⟨45171510524871037212837109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60228680699828049617116145 45171510524871037212837109)
          ·
            refine ⟨4234829111706659738703479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45171510524871037212837109 4234829111706659738703479)
            ·
              refine ⟨6352243667559989608055219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234829111706659738703479 6352243667559989608055219)
              ·
                refine ⟨9528365501339984412082829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352243667559989608055219 9528365501339984412082829)
                ·
                  refine ⟨3573137063002494154531061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9528365501339984412082829 3573137063002494154531061)
                  ·
                    refine ⟨334981599656483826987287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3573137063002494154531061 334981599656483826987287)
                    ·
                      rfl

theorem cell23_1957123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 5].length) (baseStart_1957123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957123 prefixEnd_1957123 := by exact prefixLift 1957123
  have htrace : WordTrace (prefixWord ++ tailWord_1957123) baseStart_1957123 baseEnd_1957123 := by
    simpa [prefixWord, tailWord_1957123, baseEnd_1957123] using wordTrace_append hprefix tailTrace_1957123
  have hstable : (prefixWord ++ tailWord_1957123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957123).length < 2 ^ (prefixWord ++ tailWord_1957123).sum := by decide
  have hdescent : baseEnd_1957123 < baseStart_1957123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957137 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 1, 1, 3]
def baseStart_1957137 : Nat := 118140960795 + 1957137 * 2 ^ 59
def prefixEnd_1957137 : Nat := 4983230072969 + 3 ^ 40 * 1957137 * 2
def baseEnd_1957137 : Nat := 1004951987698614426186797

theorem tailTrace_1957137 : CollatzResearch.WordTrace tailWord_1957137 prefixEnd_1957137 1004951987698614426186797 := by
  unfold tailWord_1957137
  simp only [CollatzResearch.WordTrace]
  refine ⟨71382650710634376233517665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47588433807089584155678443 71382650710634376233517665)
  ·
    refine ⟨53536988032975782175138249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71382650710634376233517665 53536988032975782175138249)
    ·
      refine ⟨40152741024731836631353687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53536988032975782175138249 40152741024731836631353687)
      ·
        refine ⟨60229111537097754947030531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40152741024731836631353687 60229111537097754947030531)
        ·
          refine ⟨90343667305646632420545797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60229111537097754947030531 90343667305646632420545797)
          ·
            refine ⟨16939437619808743578852337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90343667305646632420545797 16939437619808743578852337)
            ·
              refine ⟨12704578214856557684139253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16939437619808743578852337 12704578214856557684139253)
              ·
                refine ⟨1191054207642802282888055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12704578214856557684139253 1191054207642802282888055)
                ·
                  refine ⟨1786581311464203424332083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191054207642802282888055 1786581311464203424332083)
                  ·
                    refine ⟨2679871967196305136498125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1786581311464203424332083 2679871967196305136498125)
                    ·
                      refine ⟨1004951987698614426186797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679871967196305136498125 1004951987698614426186797)
                      ·
                        rfl

theorem cell23_1957137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_1957137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957137 prefixEnd_1957137 := by exact prefixLift 1957137
  have htrace : WordTrace (prefixWord ++ tailWord_1957137) baseStart_1957137 baseEnd_1957137 := by
    simpa [prefixWord, tailWord_1957137, baseEnd_1957137] using wordTrace_append hprefix tailTrace_1957137
  have hstable : (prefixWord ++ tailWord_1957137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957137).length < 2 ^ (prefixWord ++ tailWord_1957137).sum := by decide
  have hdescent : baseEnd_1957137 < baseStart_1957137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957160 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1957160 : Nat := 118140960795 + 1957160 * 2 ^ 59
def prefixEnd_1957160 : Nat := 4983230072969 + 3 ^ 40 * 1957160 * 2
def baseEnd_1957160 : Nat := 1004963797753667836199191

theorem tailTrace_1957160 : CollatzResearch.WordTrace tailWord_1957160 prefixEnd_1957160 1004963797753667836199191 := by
  unfold tailWord_1957160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35691744794775525580802467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47588993059700700774403289 35691744794775525580802467)
  ·
    refine ⟨53537617192163288371203701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35691744794775525580802467 53537617192163288371203701)
    ·
      refine ⟨5019151611765308284800347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53537617192163288371203701 5019151611765308284800347)
      ·
        refine ⟨7528727417647962427200521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019151611765308284800347 7528727417647962427200521)
        ·
          refine ⟨5646545563235971820400391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7528727417647962427200521 5646545563235971820400391)
          ·
            refine ⟨8469818344853957730600587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646545563235971820400391 8469818344853957730600587)
            ·
              refine ⟨12704727517280936595900881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469818344853957730600587 12704727517280936595900881)
              ·
                refine ⟨9528545637960702446925661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12704727517280936595900881 9528545637960702446925661)
                ·
                  refine ⟨3573204614235263417597123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9528545637960702446925661 3573204614235263417597123)
                  ·
                    refine ⟨5359806921352895126395685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3573204614235263417597123 5359806921352895126395685)
                    ·
                      refine ⟨1004963797753667836199191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5359806921352895126395685 1004963797753667836199191)
                      ·
                        rfl

theorem cell23_1957160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1957160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957160 prefixEnd_1957160 := by exact prefixLift 1957160
  have htrace : WordTrace (prefixWord ++ tailWord_1957160) baseStart_1957160 baseEnd_1957160 := by
    simpa [prefixWord, tailWord_1957160, baseEnd_1957160] using wordTrace_append hprefix tailTrace_1957160
  have hstable : (prefixWord ++ tailWord_1957160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957160).length < 2 ^ (prefixWord ++ tailWord_1957160).sum := by decide
  have hdescent : baseEnd_1957160 < baseStart_1957160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957170 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1957170 : Nat := 118140960795 + 1957170 * 2 ^ 59
def prefixEnd_1957170 : Nat := 4983230072969 + 3 ^ 40 * 1957170 * 2
def baseEnd_1957170 : Nat := 334989644186737599024715

theorem tailTrace_1957170 : CollatzResearch.WordTrace tailWord_1957170 prefixEnd_1957170 334989644186737599024715 := by
  unfold tailWord_1957170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845963579878705717367241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47589236213009881912979309 17845963579878705717367241)
  ·
    refine ⟨13384472684909029288025431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17845963579878705717367241 13384472684909029288025431)
    ·
      refine ⟨20076709027363543932038147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384472684909029288025431 20076709027363543932038147)
      ·
        refine ⟨30115063541045315898057221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076709027363543932038147 30115063541045315898057221)
        ·
          refine ⟨5646574413945996730885729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30115063541045315898057221 5646574413945996730885729)
          ·
            refine ⟨4234930810459497548164297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5646574413945996730885729 4234930810459497548164297)
            ·
              refine ⟨3176198107844623161123223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234930810459497548164297 3176198107844623161123223)
              ·
                refine ⟨4764297161766934741684835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176198107844623161123223 4764297161766934741684835)
                ·
                  refine ⟨7146445742650402112527253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764297161766934741684835 7146445742650402112527253)
                  ·
                    refine ⟨334989644186737599024715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7146445742650402112527253 334989644186737599024715)
                    ·
                      rfl

theorem cell23_1957170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1957170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957170 prefixEnd_1957170 := by exact prefixLift 1957170
  have htrace : WordTrace (prefixWord ++ tailWord_1957170) baseStart_1957170 baseEnd_1957170 := by
    simpa [prefixWord, tailWord_1957170, baseEnd_1957170] using wordTrace_append hprefix tailTrace_1957170
  have hstable : (prefixWord ++ tailWord_1957170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957170).length < 2 ^ (prefixWord ++ tailWord_1957170).sum := by decide
  have hdescent : baseEnd_1957170 < baseStart_1957170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957180 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1957180 : Nat := 118140960795 + 1957180 * 2 ^ 59
def prefixEnd_1957180 : Nat := 4983230072969 + 3 ^ 40 * 1957180 * 2
def baseEnd_1957180 : Nat := 1004974067366757757949099

theorem tailTrace_1957180 : CollatzResearch.WordTrace tailWord_1957180 prefixEnd_1957180 1004974067366757757949099 := by
  unfold tailWord_1957180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35692109524739297288666497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47589479366319063051555329 35692109524739297288666497)
  ·
    refine ⟨26769082143554472966499873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35692109524739297288666497 26769082143554472966499873)
    ·
      refine ⟨20076811607665854724874905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26769082143554472966499873 20076811607665854724874905)
      ·
        refine ⟨15057608705749391043656179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20076811607665854724874905 15057608705749391043656179)
        ·
          refine ⟨22586413058624086565484269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15057608705749391043656179 22586413058624086565484269)
          ·
            refine ⟨8469904896984032462056601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22586413058624086565484269 8469904896984032462056601)
            ·
              refine ⟨6352428672738024346542451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8469904896984032462056601 6352428672738024346542451)
              ·
                refine ⟨9528643009107036519813677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352428672738024346542451 9528643009107036519813677)
                ·
                  refine ⟨3573241128415138694930129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9528643009107036519813677 3573241128415138694930129)
                  ·
                    refine ⟨2679930846311354021197597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573241128415138694930129 2679930846311354021197597)
                    ·
                      refine ⟨1004974067366757757949099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2679930846311354021197597 1004974067366757757949099)
                      ·
                        rfl

theorem cell23_1957180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1957180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957180 prefixEnd_1957180 := by exact prefixLift 1957180
  have htrace : WordTrace (prefixWord ++ tailWord_1957180) baseStart_1957180 baseEnd_1957180 := by
    simpa [prefixWord, tailWord_1957180, baseEnd_1957180] using wordTrace_append hprefix tailTrace_1957180
  have hstable : (prefixWord ++ tailWord_1957180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957180).length < 2 ^ (prefixWord ++ tailWord_1957180).sum := by decide
  have hdescent : baseEnd_1957180 < baseStart_1957180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957181 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1957181 : Nat := 118140960795 + 1957181 * 2 ^ 59
def prefixEnd_1957181 : Nat := 4983230072969 + 3 ^ 40 * 1957181 * 2
def baseEnd_1957181 : Nat := 1004974580847412254036595

theorem tailTrace_1957181 : CollatzResearch.WordTrace tailWord_1957181 prefixEnd_1957181 1004974580847412254036595 := by
  unfold tailWord_1957181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71384255522474971748119397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47589503681649981165412931 71384255522474971748119397)
  ·
    refine ⟨13384547910464057202772387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71384255522474971748119397 13384547910464057202772387)
    ·
      refine ⟨20076821865696085804158581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384547910464057202772387 20076821865696085804158581)
      ·
        refine ⟨1882202049909008044139867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20076821865696085804158581 1882202049909008044139867)
        ·
          refine ⟨2823303074863512066209801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882202049909008044139867 2823303074863512066209801)
          ·
            refine ⟨2117477306147634049657351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823303074863512066209801 2117477306147634049657351)
            ·
              refine ⟨3176215959221451074486027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117477306147634049657351 3176215959221451074486027)
              ·
                refine ⟨4764323938832176611729041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176215959221451074486027 4764323938832176611729041)
                ·
                  refine ⟨3573242954124132458796781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764323938832176611729041 3573242954124132458796781)
                  ·
                    refine ⟨1339966107796549672048793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573242954124132458796781 1339966107796549672048793)
                    ·
                      refine ⟨1004974580847412254036595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339966107796549672048793 1004974580847412254036595)
                      ·
                        rfl

theorem cell23_1957181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1957181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957181 prefixEnd_1957181 := by exact prefixLift 1957181
  have htrace : WordTrace (prefixWord ++ tailWord_1957181) baseStart_1957181 baseEnd_1957181 := by
    simpa [prefixWord, tailWord_1957181, baseEnd_1957181] using wordTrace_append hprefix tailTrace_1957181
  have hstable : (prefixWord ++ tailWord_1957181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957181).length < 2 ^ (prefixWord ++ tailWord_1957181).sum := by decide
  have hdescent : baseEnd_1957181 < baseStart_1957181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957224 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1957224 : Nat := 118140960795 + 1957224 * 2 ^ 59
def prefixEnd_1957224 : Nat := 4983230072969 + 3 ^ 40 * 1957224 * 2
def baseEnd_1957224 : Nat := 1004996660515555585798897

theorem tailTrace_1957224 : CollatzResearch.WordTrace tailWord_1957224 prefixEnd_1957224 1004996660515555585798897 := by
  unfold tailWord_1957224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35692911930659595045967363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47590549240879460061289817 35692911930659595045967363)
  ·
    refine ⟨53539367895989392568951045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35692911930659595045967363 53539367895989392568951045)
    ·
      refine ⟨10038631480498011106678321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53539367895989392568951045 10038631480498011106678321)
      ·
        refine ⟨7528973610373508330008741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10038631480498011106678321 7528973610373508330008741)
        ·
          refine ⟨1411682551945032811876639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7528973610373508330008741 1411682551945032811876639)
          ·
            refine ⟨2117523827917549217814959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411682551945032811876639 2117523827917549217814959)
            ·
              refine ⟨3176285741876323826722439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117523827917549217814959 3176285741876323826722439)
              ·
                refine ⟨4764428612814485740083659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176285741876323826722439 4764428612814485740083659)
                ·
                  refine ⟨7146642919221728610125489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764428612814485740083659 7146642919221728610125489)
                  ·
                    refine ⟨5359982189416296457594117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7146642919221728610125489 5359982189416296457594117)
                    ·
                      refine ⟨1004996660515555585798897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5359982189416296457594117 1004996660515555585798897)
                      ·
                        rfl

theorem cell23_1957224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1957224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957224 prefixEnd_1957224 := by exact prefixLift 1957224
  have htrace : WordTrace (prefixWord ++ tailWord_1957224) baseStart_1957224 baseEnd_1957224 := by
    simpa [prefixWord, tailWord_1957224, baseEnd_1957224] using wordTrace_append hprefix tailTrace_1957224
  have hstable : (prefixWord ++ tailWord_1957224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957224).length < 2 ^ (prefixWord ++ tailWord_1957224).sum := by decide
  have hdescent : baseEnd_1957224 < baseStart_1957224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957233 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1957233 : Nat := 118140960795 + 1957233 * 2 ^ 59
def prefixEnd_1957233 : Nat := 4983230072969 + 3 ^ 40 * 1957233 * 2
def baseEnd_1957233 : Nat := 1005001281841446050586355

theorem tailTrace_1957233 : CollatzResearch.WordTrace tailWord_1957233 prefixEnd_1957233 1005001281841446050586355 := by
  unfold tailWord_1957233
  simp only [CollatzResearch.WordTrace]
  refine ⟨71386152118286584629012353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47590768078857723086008235 71386152118286584629012353)
  ·
    refine ⟨53539614088714938471759265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71386152118286584629012353 53539614088714938471759265)
    ·
      refine ⟨40154710566536203853819449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53539614088714938471759265 40154710566536203853819449)
      ·
        refine ⟨30116032924902152890364587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40154710566536203853819449 30116032924902152890364587)
        ·
          refine ⟨45174049387353229335546881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30116032924902152890364587 45174049387353229335546881)
          ·
            refine ⟨33880537040514922001660161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45174049387353229335546881 33880537040514922001660161)
            ·
              refine ⟨25410402780386191501245121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33880537040514922001660161 25410402780386191501245121)
              ·
                refine ⟨19057802085289643625933841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25410402780386191501245121 19057802085289643625933841)
                ·
                  refine ⟨14293351563967232719450381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19057802085289643625933841 14293351563967232719450381)
                  ·
                    refine ⟨5360006836487712269793893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14293351563967232719450381 5360006836487712269793893)
                    ·
                      refine ⟨1005001281841446050586355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5360006836487712269793893 1005001281841446050586355)
                      ·
                        rfl

theorem cell23_1957233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1957233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957233 prefixEnd_1957233 := by exact prefixLift 1957233
  have htrace : WordTrace (prefixWord ++ tailWord_1957233) baseStart_1957233 baseEnd_1957233 := by
    simpa [prefixWord, tailWord_1957233, baseEnd_1957233] using wordTrace_append hprefix tailTrace_1957233
  have hstable : (prefixWord ++ tailWord_1957233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957233).length < 2 ^ (prefixWord ++ tailWord_1957233).sum := by decide
  have hdescent : baseEnd_1957233 < baseStart_1957233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957253 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1957253 : Nat := 118140960795 + 1957253 * 2 ^ 59
def prefixEnd_1957253 : Nat := 4983230072969 + 3 ^ 40 * 1957253 * 2
def baseEnd_1957253 : Nat := 1005011551454535972336263

theorem tailTrace_1957253 : CollatzResearch.WordTrace tailWord_1957253 prefixEnd_1957253 1005011551454535972336263 := by
  unfold tailWord_1957253
  simp only [CollatzResearch.WordTrace]
  refine ⟨71386881578214128044740413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47591254385476085363160275 71386881578214128044740413)
  ·
    refine ⟨26770080591830298016777655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71386881578214128044740413 26770080591830298016777655)
    ·
      refine ⟨40155120887745447025166483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26770080591830298016777655 40155120887745447025166483)
      ·
        refine ⟨60232681331618170537749725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40155120887745447025166483 60232681331618170537749725)
        ·
          refine ⟨22587255499356813951656147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60232681331618170537749725 22587255499356813951656147)
          ·
            refine ⟨33880883249035220927484221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22587255499356813951656147 33880883249035220927484221)
            ·
              refine ⟨12705331218388207847806583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33880883249035220927484221 12705331218388207847806583)
              ·
                refine ⟨19057996827582311771709875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12705331218388207847806583 19057996827582311771709875)
                ·
                  refine ⟨28586995241373467657564813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19057996827582311771709875 28586995241373467657564813)
                  ·
                    refine ⟨10720123215515050371586805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28586995241373467657564813 10720123215515050371586805)
                    ·
                      refine ⟨1005011551454535972336263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10720123215515050371586805 1005011551454535972336263)
                      ·
                        rfl

theorem cell23_1957253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1957253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957253 prefixEnd_1957253 := by exact prefixLift 1957253
  have htrace : WordTrace (prefixWord ++ tailWord_1957253) baseStart_1957253 baseEnd_1957253 := by
    simpa [prefixWord, tailWord_1957253, baseEnd_1957253] using wordTrace_append hprefix tailTrace_1957253
  have hstable : (prefixWord ++ tailWord_1957253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957253).length < 2 ^ (prefixWord ++ tailWord_1957253).sum := by decide
  have hdescent : baseEnd_1957253 < baseStart_1957253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957288 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1957288 : Nat := 118140960795 + 1957288 * 2 ^ 59
def prefixEnd_1957288 : Nat := 4983230072969 + 3 ^ 40 * 1957288 * 2
def baseEnd_1957288 : Nat := 1005029523277443335398603

theorem tailTrace_1957288 : CollatzResearch.WordTrace tailWord_1957288 prefixEnd_1957288 1005029523277443335398603 := by
  unfold tailWord_1957288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35694079066543664511132259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47592105422058219348176345 35694079066543664511132259)
  ·
    refine ⟨53541118599815496766698389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35694079066543664511132259 53541118599815496766698389)
    ·
      refine ⟨2509739934366351410938987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53541118599815496766698389 2509739934366351410938987)
      ·
        refine ⟨3764609901549527116408481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509739934366351410938987 3764609901549527116408481)
        ·
          refine ⟨2823457426162145337306361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3764609901549527116408481 2823457426162145337306361)
          ·
            refine ⟨2117593069621609002979771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823457426162145337306361 2117593069621609002979771)
            ·
              refine ⟨3176389604432413504469657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117593069621609002979771 3176389604432413504469657)
              ·
                refine ⟨2382292203324310128352243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176389604432413504469657 2382292203324310128352243)
                ·
                  refine ⟨3573438304986465192528365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382292203324310128352243 3573438304986465192528365)
                  ·
                    refine ⟨1340039364369924447198137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573438304986465192528365 1340039364369924447198137)
                    ·
                      refine ⟨1005029523277443335398603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340039364369924447198137 1005029523277443335398603)
                      ·
                        rfl

theorem cell23_1957288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1957288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957288 prefixEnd_1957288 := by exact prefixLift 1957288
  have htrace : WordTrace (prefixWord ++ tailWord_1957288) baseStart_1957288 baseEnd_1957288 := by
    simpa [prefixWord, tailWord_1957288, baseEnd_1957288] using wordTrace_append hprefix tailTrace_1957288
  have hstable : (prefixWord ++ tailWord_1957288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957288).length < 2 ^ (prefixWord ++ tailWord_1957288).sum := by decide
  have hdescent : baseEnd_1957288 < baseStart_1957288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957320 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1957320 : Nat := 118140960795 + 1957320 * 2 ^ 59
def prefixEnd_1957320 : Nat := 4983230072969 + 3 ^ 40 * 1957320 * 2
def baseEnd_1957320 : Nat := 335015318219462403399485

theorem tailTrace_1957320 : CollatzResearch.WordTrace tailWord_1957320 prefixEnd_1957320 335015318219462403399485 := by
  unfold tailWord_1957320
  simp only [CollatzResearch.WordTrace]
  refine ⟨35694662634485699243714707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47592883512647598991619609 35694662634485699243714707)
  ·
    refine ⟨53541993951728548865572061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35694662634485699243714707 53541993951728548865572061)
    ·
      refine ⟨20078247731898205824589523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53541993951728548865572061 20078247731898205824589523)
      ·
        refine ⟨30117371597847308736884285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078247731898205824589523 30117371597847308736884285)
        ·
          refine ⟨11294014349192740776331607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30117371597847308736884285 11294014349192740776331607)
          ·
            refine ⟨16941021523789111164497411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294014349192740776331607 16941021523789111164497411)
            ·
              refine ⟨25411532285683666746746117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941021523789111164497411 25411532285683666746746117)
              ·
                refine ⟨4764662303565687515014897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25411532285683666746746117 4764662303565687515014897)
                ·
                  refine ⟨3573496727674265636261173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764662303565687515014897 3573496727674265636261173)
                  ·
                    refine ⟨335015318219462403399485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3573496727674265636261173 335015318219462403399485)
                    ·
                      rfl

theorem cell23_1957320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1957320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957320 prefixEnd_1957320 := by exact prefixLift 1957320
  have htrace : WordTrace (prefixWord ++ tailWord_1957320) baseStart_1957320 baseEnd_1957320 := by
    simpa [prefixWord, tailWord_1957320, baseEnd_1957320] using wordTrace_append hprefix tailTrace_1957320
  have hstable : (prefixWord ++ tailWord_1957320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957320).length < 2 ^ (prefixWord ++ tailWord_1957320).sum := by decide
  have hdescent : baseEnd_1957320 < baseStart_1957320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957324 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 5]
def baseStart_1957324 : Nat := 118140960795 + 1957324 * 2 ^ 59
def prefixEnd_1957324 : Nat := 4983230072969 + 3 ^ 40 * 1957324 * 2
def baseEnd_1957324 : Nat := 111672000953445021616493

theorem tailTrace_1957324 : CollatzResearch.WordTrace tailWord_1957324 prefixEnd_1957324 111672000953445021616493 := by
  unfold tailWord_1957324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35694735580478453585287513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47592980773971271447050017 35694735580478453585287513)
  ·
    refine ⟨26771051685358840188965635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35694735580478453585287513 26771051685358840188965635)
    ·
      refine ⟨40156577528038260283448453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26771051685358840188965635 40156577528038260283448453)
      ·
        refine ⟨7529358286507173803146585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40156577528038260283448453 7529358286507173803146585)
        ·
          refine ⟨5647018714880380352359939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529358286507173803146585 5647018714880380352359939)
          ·
            refine ⟨8470528072320570528539909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647018714880380352359939 8470528072320570528539909)
            ·
              refine ⟨1588224013560106974101233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8470528072320570528539909 1588224013560106974101233)
              ·
                refine ⟨1191168010170080230575925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588224013560106974101233 1191168010170080230575925)
                ·
                  refine ⟨111672000953445021616493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1191168010170080230575925 111672000953445021616493)
                  ·
                    rfl

theorem cell23_1957324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_1957324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957324 prefixEnd_1957324 := by exact prefixLift 1957324
  have htrace : WordTrace (prefixWord ++ tailWord_1957324) baseStart_1957324 baseEnd_1957324 := by
    simpa [prefixWord, tailWord_1957324, baseEnd_1957324] using wordTrace_append hprefix tailTrace_1957324
  have hstable : (prefixWord ++ tailWord_1957324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957324).length < 2 ^ (prefixWord ++ tailWord_1957324).sum := by decide
  have hdescent : baseEnd_1957324 < baseStart_1957324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957334 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1957334 : Nat := 118140960795 + 1957334 * 2 ^ 59
def prefixEnd_1957334 : Nat := 4983230072969 + 3 ^ 40 * 1957334 * 2
def baseEnd_1957334 : Nat := 1005053143387550155423391

theorem tailTrace_1957334 : CollatzResearch.WordTrace tailWord_1957334 prefixEnd_1957334 1005053143387550155423391 := by
  unfold tailWord_1957334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461864743182542429902441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47593223927280452585626037 4461864743182542429902441)
  ·
    refine ⟨3346398557386906822426831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4461864743182542429902441 3346398557386906822426831)
    ·
      refine ⟨5019597836080360233640247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346398557386906822426831 5019597836080360233640247)
      ·
        refine ⟨7529396754120540350460371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019597836080360233640247 7529396754120540350460371)
        ·
          refine ⟨11294095131180810525690557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529396754120540350460371 11294095131180810525690557)
          ·
            refine ⟨4235285674192803947133959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11294095131180810525690557 4235285674192803947133959)
            ·
              refine ⟨6352928511289205920700939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235285674192803947133959 6352928511289205920700939)
              ·
                refine ⟨9529392766933808881051409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352928511289205920700939 9529392766933808881051409)
                ·
                  refine ⟨7147044575200356660788557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529392766933808881051409 7147044575200356660788557)
                  ·
                    refine ⟨2680141715700133747795709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7147044575200356660788557 2680141715700133747795709)
                    ·
                      refine ⟨1005053143387550155423391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2680141715700133747795709 1005053143387550155423391)
                      ·
                        rfl

theorem cell23_1957334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1957334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957334 prefixEnd_1957334 := by exact prefixLift 1957334
  have htrace : WordTrace (prefixWord ++ tailWord_1957334) baseStart_1957334 baseEnd_1957334 := by
    simpa [prefixWord, tailWord_1957334, baseEnd_1957334] using wordTrace_append hprefix tailTrace_1957334
  have hstable : (prefixWord ++ tailWord_1957334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957334).length < 2 ^ (prefixWord ++ tailWord_1957334).sum := by decide
  have hdescent : baseEnd_1957334 < baseStart_1957334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957354 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1957354 : Nat := 118140960795 + 1957354 * 2 ^ 59
def prefixEnd_1957354 : Nat := 4983230072969 + 3 ^ 40 * 1957354 * 2
def baseEnd_1957354 : Nat := 335021137666880025724433

theorem tailTrace_1957354 : CollatzResearch.WordTrace tailWord_1957354 prefixEnd_1957354 335021137666880025724433 := by
  unfold tailWord_1957354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847641337712055573541779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47593710233898814862778077 17847641337712055573541779)
  ·
    refine ⟨26771462006568083360312669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17847641337712055573541779 26771462006568083360312669)
    ·
      refine ⟨10039298252463031260117251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26771462006568083360312669 10039298252463031260117251)
      ·
        refine ⟨15058947378694546890175877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039298252463031260117251 15058947378694546890175877)
        ·
          refine ⟨2823552633505227541907977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15058947378694546890175877 2823552633505227541907977)
          ·
            refine ⟨2117664475128920656430983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823552633505227541907977 2117664475128920656430983)
            ·
              refine ⟨3176496712693380984646475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117664475128920656430983 3176496712693380984646475)
              ·
                refine ⟨4764745069040071476969713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176496712693380984646475 4764745069040071476969713)
                ·
                  refine ⟨3573558801780053607727285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764745069040071476969713 3573558801780053607727285)
                  ·
                    refine ⟨335021137666880025724433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3573558801780053607727285 335021137666880025724433)
                    ·
                      rfl

theorem cell23_1957354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1957354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957354 prefixEnd_1957354 := by exact prefixLift 1957354
  have htrace : WordTrace (prefixWord ++ tailWord_1957354) baseStart_1957354 baseEnd_1957354 := by
    simpa [prefixWord, tailWord_1957354, baseEnd_1957354] using wordTrace_append hprefix tailTrace_1957354
  have hstable : (prefixWord ++ tailWord_1957354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957354).length < 2 ^ (prefixWord ++ tailWord_1957354).sum := by decide
  have hdescent : baseEnd_1957354 < baseStart_1957354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957384 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1957384 : Nat := 118140960795 + 1957384 * 2 ^ 59
def prefixEnd_1957384 : Nat := 4983230072969 + 3 ^ 40 * 1957384 * 2
def baseEnd_1957384 : Nat := 335026272473424986599387

theorem tailTrace_1957384 : CollatzResearch.WordTrace tailWord_1957384 prefixEnd_1957384 335026272473424986599387 := by
  unfold tailWord_1957384
  simp only [CollatzResearch.WordTrace]
  refine ⟨35695829770369768708879603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47594439693826358278506137 35695829770369768708879603)
  ·
    refine ⟨53543744655554653063319405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35695829770369768708879603 53543744655554653063319405)
    ·
      refine ⟨20078904245832994898744777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53543744655554653063319405 20078904245832994898744777)
      ·
        refine ⟨15059178184374746174058583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20078904245832994898744777 15059178184374746174058583)
        ·
          refine ⟨22588767276562119261087875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059178184374746174058583 22588767276562119261087875)
          ·
            refine ⟨33883150914843178891631813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22588767276562119261087875 33883150914843178891631813)
            ·
              refine ⟨6353090796533096042180965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33883150914843178891631813 6353090796533096042180965)
              ·
                refine ⟨1191204524349955507908931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6353090796533096042180965 1191204524349955507908931)
                ·
                  refine ⟨1786806786524933261863397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191204524349955507908931 1786806786524933261863397)
                  ·
                    refine ⟨335026272473424986599387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1786806786524933261863397 335026272473424986599387)
                    ·
                      rfl

theorem cell23_1957384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1957384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957384 prefixEnd_1957384 := by exact prefixLift 1957384
  have htrace : WordTrace (prefixWord ++ tailWord_1957384) baseStart_1957384 baseEnd_1957384 := by
    simpa [prefixWord, tailWord_1957384, baseEnd_1957384] using wordTrace_append hprefix tailTrace_1957384
  have hstable : (prefixWord ++ tailWord_1957384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957384).length < 2 ^ (prefixWord ++ tailWord_1957384).sum := by decide
  have hdescent : baseEnd_1957384 < baseStart_1957384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957427 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 1, 5]
def baseStart_1957427 : Nat := 118140960795 + 1957427 * 2 ^ 59
def prefixEnd_1957427 : Nat := 4983230072969 + 3 ^ 40 * 1957427 * 2
def baseEnd_1957427 : Nat := 335033632362806097186821

theorem tailTrace_1957427 : CollatzResearch.WordTrace tailWord_1957427 prefixEnd_1957427 335033632362806097186821 := by
  unfold tailWord_1957427
  simp only [CollatzResearch.WordTrace]
  refine ⟨71393227879583755761574535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47595485253055837174383023 71393227879583755761574535)
  ·
    refine ⟨107089841819375633642361803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71393227879583755761574535 107089841819375633642361803)
    ·
      refine ⟨160634762729063450463542705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107089841819375633642361803 160634762729063450463542705)
      ·
        refine ⟨120476072046797587847657029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160634762729063450463542705 120476072046797587847657029)
        ·
          refine ⟨22589263508774547721435693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120476072046797587847657029 22589263508774547721435693)
          ·
            refine ⟨8470973815790455395538385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22589263508774547721435693 8470973815790455395538385)
            ·
              refine ⟨6353230361842841546653789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8470973815790455395538385 6353230361842841546653789)
              ·
                refine ⟨2382461385691065579995171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6353230361842841546653789 2382461385691065579995171)
                ·
                  refine ⟨3573692078536598369992757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382461385691065579995171 3573692078536598369992757)
                  ·
                    refine ⟨335033632362806097186821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3573692078536598369992757 335033632362806097186821)
                    ·
                      rfl

theorem cell23_1957427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 5].length) (baseStart_1957427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957427 prefixEnd_1957427 := by exact prefixLift 1957427
  have htrace : WordTrace (prefixWord ++ tailWord_1957427) baseStart_1957427 baseEnd_1957427 := by
    simpa [prefixWord, tailWord_1957427, baseEnd_1957427] using wordTrace_append hprefix tailTrace_1957427
  have hstable : (prefixWord ++ tailWord_1957427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957427).length < 2 ^ (prefixWord ++ tailWord_1957427).sum := by decide
  have hdescent : baseEnd_1957427 < baseStart_1957427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957434 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_1957434 : Nat := 118140960795 + 1957434 * 2 ^ 59
def prefixEnd_1957434 : Nat := 4983230072969 + 3 ^ 40 * 1957434 * 2
def baseEnd_1957434 : Nat := 1005104491452999764172931

theorem tailTrace_1957434 : CollatzResearch.WordTrace tailWord_1957434 prefixEnd_1957434 1005104491452999764172931 := by
  unfold tailWord_1957434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848370797639598989269839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47595655460372263971386237 17848370797639598989269839)
  ·
    refine ⟨26772556196459398483904759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17848370797639598989269839 26772556196459398483904759)
    ·
      refine ⟨40158834294689097725857139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26772556196459398483904759 40158834294689097725857139)
      ·
        refine ⟨60238251442033646588785709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40158834294689097725857139 60238251442033646588785709)
        ·
          refine ⟨22589344290762617470794641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60238251442033646588785709 22589344290762617470794641)
          ·
            refine ⟨16942008218071963103095981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22589344290762617470794641 16942008218071963103095981)
            ·
              refine ⟨6353253081776986163660993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16942008218071963103095981 6353253081776986163660993)
              ·
                refine ⟨4764939811332739622745745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353253081776986163660993 4764939811332739622745745)
                ·
                  refine ⟨3573704858499554717059309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764939811332739622745745 3573704858499554717059309)
                  ·
                    refine ⟨1340139321937333018897241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573704858499554717059309 1340139321937333018897241)
                    ·
                      refine ⟨1005104491452999764172931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340139321937333018897241 1005104491452999764172931)
                      ·
                        rfl

theorem cell23_1957434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_1957434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957434 prefixEnd_1957434 := by exact prefixLift 1957434
  have htrace : WordTrace (prefixWord ++ tailWord_1957434) baseStart_1957434 baseEnd_1957434 := by
    simpa [prefixWord, tailWord_1957434, baseEnd_1957434] using wordTrace_append hprefix tailTrace_1957434
  have hstable : (prefixWord ++ tailWord_1957434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957434).length < 2 ^ (prefixWord ++ tailWord_1957434).sum := by decide
  have hdescent : baseEnd_1957434 < baseStart_1957434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957464 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_1957464 : Nat := 118140960795 + 1957464 * 2 ^ 59
def prefixEnd_1957464 : Nat := 4983230072969 + 3 ^ 40 * 1957464 * 2
def baseEnd_1957464 : Nat := 1005119895872634646797793

theorem tailTrace_1957464 : CollatzResearch.WordTrace tailWord_1957464 prefixEnd_1957464 1005119895872634646797793 := by
  unfold tailWord_1957464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35697288690224855540335723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47596384920299807387114297 35697288690224855540335723)
  ·
    refine ⟨53545933035337283310503585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35697288690224855540335723 53545933035337283310503585)
    ·
      refine ⟨40159449776502962482877689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53545933035337283310503585 40159449776502962482877689)
      ·
        refine ⟨30119587332377221862158267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40159449776502962482877689 30119587332377221862158267)
        ·
          refine ⟨45179380998565832793237401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30119587332377221862158267 45179380998565832793237401)
          ·
            refine ⟨33884535748924374594928051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45179380998565832793237401 33884535748924374594928051)
            ·
              refine ⟨50826803623386561892392077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33884535748924374594928051 50826803623386561892392077)
              ·
                refine ⟨19060051358769960709647029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50826803623386561892392077 19060051358769960709647029)
                ·
                  refine ⟨1786879814884683816529409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19060051358769960709647029 1786879814884683816529409)
                  ·
                    refine ⟨1340159861163512862397057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786879814884683816529409 1340159861163512862397057)
                    ·
                      refine ⟨1005119895872634646797793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340159861163512862397057 1005119895872634646797793)
                      ·
                        rfl

theorem cell23_1957464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_1957464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957464 prefixEnd_1957464 := by exact prefixLift 1957464
  have htrace : WordTrace (prefixWord ++ tailWord_1957464) baseStart_1957464 baseEnd_1957464 := by
    simpa [prefixWord, tailWord_1957464, baseEnd_1957464] using wordTrace_append hprefix tailTrace_1957464
  have hstable : (prefixWord ++ tailWord_1957464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957464).length < 2 ^ (prefixWord ++ tailWord_1957464).sum := by decide
  have hdescent : baseEnd_1957464 < baseStart_1957464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957477 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1957477 : Nat := 118140960795 + 1957477 * 2 ^ 59
def prefixEnd_1957477 : Nat := 4983230072969 + 3 ^ 40 * 1957477 * 2
def baseEnd_1957477 : Nat := 1005126571121143095935233

theorem tailTrace_1957477 : CollatzResearch.WordTrace tailWord_1957477 prefixEnd_1957477 1005126571121143095935233 := by
  unfold tailWord_1957477
  simp only [CollatzResearch.WordTrace]
  refine ⟨71395051529402614300894685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47596701019601742867263123 71395051529402614300894685)
  ·
    refine ⟨26773144323525980362835507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71395051529402614300894685 26773144323525980362835507)
    ·
      refine ⟨40159716485288970544253261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26773144323525980362835507 40159716485288970544253261)
      ·
        refine ⟨15059893681983363954094973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40159716485288970544253261 15059893681983363954094973)
        ·
          refine ⟨5647460130743761482785615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15059893681983363954094973 5647460130743761482785615)
          ·
            refine ⟨8471190196115642224178423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647460130743761482785615 8471190196115642224178423)
            ·
              refine ⟨12706785294173463336267635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471190196115642224178423 12706785294173463336267635)
              ·
                refine ⟨19060177941260195004401453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12706785294173463336267635 19060177941260195004401453)
                ·
                  refine ⟨7147566727972573126650545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19060177941260195004401453 7147566727972573126650545)
                  ·
                    refine ⟨5360675045979429844987909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147566727972573126650545 5360675045979429844987909)
                    ·
                      refine ⟨1005126571121143095935233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5360675045979429844987909 1005126571121143095935233)
                      ·
                        rfl

theorem cell23_1957477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1957477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957477 prefixEnd_1957477 := by exact prefixLift 1957477
  have htrace : WordTrace (prefixWord ++ tailWord_1957477) baseStart_1957477 baseEnd_1957477 := by
    simpa [prefixWord, tailWord_1957477, baseEnd_1957477] using wordTrace_append hprefix tailTrace_1957477
  have hstable : (prefixWord ++ tailWord_1957477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957477).length < 2 ^ (prefixWord ++ tailWord_1957477).sum := by decide
  have hdescent : baseEnd_1957477 < baseStart_1957477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957497 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1957497 : Nat := 118140960795 + 1957497 * 2 ^ 59
def prefixEnd_1957497 : Nat := 4983230072969 + 3 ^ 40 * 1957497 * 2
def baseEnd_1957497 : Nat := 1005136840734233017685141

theorem tailTrace_1957497 : CollatzResearch.WordTrace tailWord_1957497 prefixEnd_1957497 1005136840734233017685141 := by
  unfold tailWord_1957497
  simp only [CollatzResearch.WordTrace]
  refine ⟨71395780989330157716622745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47597187326220105144415163 71395780989330157716622745)
  ·
    refine ⟨53546835741997618287467059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71395780989330157716622745 53546835741997618287467059)
    ·
      refine ⟨80320253612996427431200589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53546835741997618287467059 80320253612996427431200589)
      ·
        refine ⟨30120095104873660286700221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80320253612996427431200589 30120095104873660286700221)
        ·
          refine ⟨11295035664327622607512583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30120095104873660286700221 11295035664327622607512583)
          ·
            refine ⟨16942553496491433911268875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295035664327622607512583 16942553496491433911268875)
            ·
              refine ⟨25413830244737150866903313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16942553496491433911268875 25413830244737150866903313)
              ·
                refine ⟨19060372683552863150177485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25413830244737150866903313 19060372683552863150177485)
                ·
                  refine ⟨7147639756332323681316557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19060372683552863150177485 7147639756332323681316557)
                  ·
                    refine ⟨2680364908624621380493709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7147639756332323681316557 2680364908624621380493709)
                    ·
                      refine ⟨1005136840734233017685141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2680364908624621380493709 1005136840734233017685141)
                      ·
                        rfl

theorem cell23_1957497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1957497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957497 prefixEnd_1957497 := by exact prefixLift 1957497
  have htrace : WordTrace (prefixWord ++ tailWord_1957497) baseStart_1957497 baseEnd_1957497 := by
    simpa [prefixWord, tailWord_1957497, baseEnd_1957497] using wordTrace_append hprefix tailTrace_1957497
  have hstable : (prefixWord ++ tailWord_1957497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957497).length < 2 ^ (prefixWord ++ tailWord_1957497).sum := by decide
  have hdescent : baseEnd_1957497 < baseStart_1957497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957514 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1957514 : Nat := 118140960795 + 1957514 * 2 ^ 59
def prefixEnd_1957514 : Nat := 4983230072969 + 3 ^ 40 * 1957514 * 2
def baseEnd_1957514 : Nat := 1005145569905359451172563

theorem tailTrace_1957514 : CollatzResearch.WordTrace tailWord_1957514 prefixEnd_1957514 1005145569905359451172563 := by
  unfold tailWord_1957514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17849100257567142404997899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47597600686845713079994397 17849100257567142404997899)
  ·
    refine ⟨26773650386350713607496849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17849100257567142404997899 26773650386350713607496849)
    ·
      refine ⟨20080237789763035205622637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26773650386350713607496849 20080237789763035205622637)
      ·
        refine ⟨7530089171161138202108489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20080237789763035205622637 7530089171161138202108489)
        ·
          refine ⟨5647566878370853651581367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530089171161138202108489 5647566878370853651581367)
          ·
            refine ⟨8471350317556280477372051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647566878370853651581367 8471350317556280477372051)
            ·
              refine ⟨12707025476334420716058077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471350317556280477372051 12707025476334420716058077)
              ·
                refine ⟨4765134553625407768521779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12707025476334420716058077 4765134553625407768521779)
                ·
                  refine ⟨7147701830438111652782669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765134553625407768521779 7147701830438111652782669)
                  ·
                    refine ⟨2680388186414291869793501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7147701830438111652782669 2680388186414291869793501)
                    ·
                      refine ⟨1005145569905359451172563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2680388186414291869793501 1005145569905359451172563)
                      ·
                        rfl

theorem cell23_1957514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1957514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957514 prefixEnd_1957514 := by exact prefixLift 1957514
  have htrace : WordTrace (prefixWord ++ tailWord_1957514) baseStart_1957514 baseEnd_1957514 := by
    simpa [prefixWord, tailWord_1957514, baseEnd_1957514] using wordTrace_append hprefix tailTrace_1957514
  have hstable : (prefixWord ++ tailWord_1957514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957514).length < 2 ^ (prefixWord ++ tailWord_1957514).sum := by decide
  have hdescent : baseEnd_1957514 < baseStart_1957514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957535 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1957535 : Nat := 118140960795 + 1957535 * 2 ^ 59
def prefixEnd_1957535 : Nat := 4983230072969 + 3 ^ 40 * 1957535 * 2
def baseEnd_1957535 : Nat := 1005156352999103869009967

theorem tailTrace_1957535 : CollatzResearch.WordTrace tailWord_1957535 prefixEnd_1957535 1005156352999103869009967 := by
  unfold tailWord_1957535
  simp only [CollatzResearch.WordTrace]
  refine ⟨71397166963192490206506059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47598111308794993471004039 71397166963192490206506059)
  ·
    refine ⟨107095750444788735309759089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71397166963192490206506059 107095750444788735309759089)
    ·
      refine ⟨80321812833591551482319317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107095750444788735309759089 80321812833591551482319317)
      ·
        refine ⟨1882542488287301987866859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80321812833591551482319317 1882542488287301987866859)
        ·
          refine ⟨2823813732430952981800289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882542488287301987866859 2823813732430952981800289)
          ·
            refine ⟨2117860299323214736350217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823813732430952981800289 2117860299323214736350217)
            ·
              refine ⟨1588395224492411052262663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117860299323214736350217 1588395224492411052262663)
              ·
                refine ⟨2382592836738616578393995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588395224492411052262663 2382592836738616578393995)
                ·
                  refine ⟨3573889255107924867590993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382592836738616578393995 3573889255107924867590993)
                  ·
                    refine ⟨2680416941330943650693245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573889255107924867590993 2680416941330943650693245)
                    ·
                      refine ⟨1005156352999103869009967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2680416941330943650693245 1005156352999103869009967)
                      ·
                        rfl

theorem cell23_1957535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1957535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957535 prefixEnd_1957535 := by exact prefixLift 1957535
  have htrace : WordTrace (prefixWord ++ tailWord_1957535) baseStart_1957535 baseEnd_1957535 := by
    simpa [prefixWord, tailWord_1957535, baseEnd_1957535] using wordTrace_append hprefix tailTrace_1957535
  have hstable : (prefixWord ++ tailWord_1957535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957535).length < 2 ^ (prefixWord ++ tailWord_1957535).sum := by decide
  have hdescent : baseEnd_1957535 < baseStart_1957535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957554 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_1957554 : Nat := 118140960795 + 1957554 * 2 ^ 59
def prefixEnd_1957554 : Nat := 4983230072969 + 3 ^ 40 * 1957554 * 2
def baseEnd_1957554 : Nat := 1005166109131539294672379

theorem tailTrace_1957554 : CollatzResearch.WordTrace tailWord_1957554 prefixEnd_1957554 1005166109131539294672379 := by
  unfold tailWord_1957554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17849464987530914112861929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47598573300082437634298477 17849464987530914112861929)
  ·
    refine ⟨13387098740648185584646447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17849464987530914112861929 13387098740648185584646447)
    ·
      refine ⟨20080648110972278376969671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13387098740648185584646447 20080648110972278376969671)
      ·
        refine ⟨30120972166458417565454507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20080648110972278376969671 30120972166458417565454507)
        ·
          refine ⟨45181458249687626348181761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30120972166458417565454507 45181458249687626348181761)
          ·
            refine ⟨33886093687265719761136321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45181458249687626348181761 33886093687265719761136321)
            ·
              refine ⟨25414570265449289820852241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33886093687265719761136321 25414570265449289820852241)
              ·
                refine ⟨19060927699086967365639181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25414570265449289820852241 19060927699086967365639181)
                ·
                  refine ⟨7147847887157612762114693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19060927699086967365639181 7147847887157612762114693)
                  ·
                    refine ⟨1340221478842052392896505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147847887157612762114693 1340221478842052392896505)
                    ·
                      refine ⟨1005166109131539294672379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340221478842052392896505 1005166109131539294672379)
                      ·
                        rfl

theorem cell23_1957554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_1957554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957554 prefixEnd_1957554 := by exact prefixLift 1957554
  have htrace : WordTrace (prefixWord ++ tailWord_1957554) baseStart_1957554 baseEnd_1957554 := by
    simpa [prefixWord, tailWord_1957554, baseEnd_1957554] using wordTrace_append hprefix tailTrace_1957554
  have hstable : (prefixWord ++ tailWord_1957554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957554).length < 2 ^ (prefixWord ++ tailWord_1957554).sum := by decide
  have hdescent : baseEnd_1957554 < baseStart_1957554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957567 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_1957567 : Nat := 118140960795 + 1957567 * 2 ^ 59
def prefixEnd_1957567 : Nat := 4983230072969 + 3 ^ 40 * 1957567 * 2
def baseEnd_1957567 : Nat := 1005172784380047743809819

theorem tailTrace_1957567 : CollatzResearch.WordTrace tailWord_1957567 prefixEnd_1957567 1005172784380047743809819 := by
  unfold tailWord_1957567
  simp only [CollatzResearch.WordTrace]
  refine ⟨71398334099076559671670955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47598889399384373114447303 71398334099076559671670955)
  ·
    refine ⟨107097501148614839507506433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71398334099076559671670955 107097501148614839507506433)
    ·
      refine ⟨80323125861461129630629825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107097501148614839507506433 80323125861461129630629825)
      ·
        refine ⟨60242344396095847222972369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80323125861461129630629825 60242344396095847222972369)
        ·
          refine ⟨45181758297071885417229277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60242344396095847222972369 45181758297071885417229277)
          ·
            refine ⟨16943159361401957031460979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45181758297071885417229277 16943159361401957031460979)
            ·
              refine ⟨25414739042102935547191469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943159361401957031460979 25414739042102935547191469)
              ·
                refine ⟨9530527140788600830196801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25414739042102935547191469 9530527140788600830196801)
                ·
                  refine ⟨7147895355591450622647601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9530527140788600830196801 7147895355591450622647601)
                  ·
                    refine ⟨5360921516693587966985701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7147895355591450622647601 5360921516693587966985701)
                    ·
                      refine ⟨1005172784380047743809819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5360921516693587966985701 1005172784380047743809819)
                      ·
                        rfl

theorem cell23_1957567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_1957567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957567 prefixEnd_1957567 := by exact prefixLift 1957567
  have htrace : WordTrace (prefixWord ++ tailWord_1957567) baseStart_1957567 baseEnd_1957567 := by
    simpa [prefixWord, tailWord_1957567, baseEnd_1957567] using wordTrace_append hprefix tailTrace_1957567
  have hstable : (prefixWord ++ tailWord_1957567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957567).length < 2 ^ (prefixWord ++ tailWord_1957567).sum := by decide
  have hdescent : baseEnd_1957567 < baseStart_1957567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957588 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1957588 : Nat := 118140960795 + 1957588 * 2 ^ 59
def prefixEnd_1957588 : Nat := 4983230072969 + 3 ^ 40 * 1957588 * 2
def baseEnd_1957588 : Nat := 1005183567473792161647223

theorem tailTrace_1957588 : CollatzResearch.WordTrace tailWord_1957588 prefixEnd_1957588 1005183567473792161647223 := by
  unfold tailWord_1957588
  simp only [CollatzResearch.WordTrace]
  refine ⟨35699550016000240129092709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47599400021333653505456945 35699550016000240129092709)
  ·
    refine ⟨6693665628000045024204883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35699550016000240129092709 6693665628000045024204883)
    ·
      refine ⟨10040498442000067536307325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693665628000045024204883 10040498442000067536307325)
      ·
        refine ⟨3765186915750025326115247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10040498442000067536307325 3765186915750025326115247)
        ·
          refine ⟨5647780373625037989172871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765186915750025326115247 5647780373625037989172871)
          ·
            refine ⟨8471670560437556983759307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647780373625037989172871 8471670560437556983759307)
            ·
              refine ⟨12707505840656335475638961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471670560437556983759307 12707505840656335475638961)
              ·
                refine ⟨9530629380492251606729221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12707505840656335475638961 9530629380492251606729221)
                ·
                  refine ⟨1786993008842297176261729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9530629380492251606729221 1786993008842297176261729)
                  ·
                    refine ⟨1340244756631722882196297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786993008842297176261729 1340244756631722882196297)
                    ·
                      refine ⟨1005183567473792161647223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340244756631722882196297 1005183567473792161647223)
                      ·
                        rfl

theorem cell23_1957588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1957588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957588 prefixEnd_1957588 := by exact prefixLift 1957588
  have htrace : WordTrace (prefixWord ++ tailWord_1957588) baseStart_1957588 baseEnd_1957588 := by
    simpa [prefixWord, tailWord_1957588, baseEnd_1957588] using wordTrace_append hprefix tailTrace_1957588
  have hstable : (prefixWord ++ tailWord_1957588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957588).length < 2 ^ (prefixWord ++ tailWord_1957588).sum := by decide
  have hdescent : baseEnd_1957588 < baseStart_1957588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957617 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1957617 : Nat := 118140960795 + 1957617 * 2 ^ 59
def prefixEnd_1957617 : Nat := 4983230072969 + 3 ^ 40 * 1957617 * 2
def baseEnd_1957617 : Nat := 1005198458412772548184589

theorem tailTrace_1957617 : CollatzResearch.WordTrace tailWord_1957617 prefixEnd_1957617 1005198458412772548184589 := by
  unfold tailWord_1957617
  simp only [CollatzResearch.WordTrace]
  refine ⟨71400157748895418210991105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47600105165930278807327403 71400157748895418210991105)
  ·
    refine ⟨53550118311671563658243329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71400157748895418210991105 53550118311671563658243329)
    ·
      refine ⟨40162588733753672743682497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53550118311671563658243329 40162588733753672743682497)
      ·
        refine ⟨30121941550315254557761873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40162588733753672743682497 30121941550315254557761873)
        ·
          refine ⟨22591456162736440918321405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30121941550315254557761873 22591456162736440918321405)
          ·
            refine ⟨8471796061026165344370527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22591456162736440918321405 8471796061026165344370527)
            ·
              refine ⟨12707694091539248016555791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471796061026165344370527 12707694091539248016555791)
              ·
                refine ⟨19061541137308872024833687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707694091539248016555791 19061541137308872024833687)
                ·
                  refine ⟨28592311705963308037250531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19061541137308872024833687 28592311705963308037250531)
                  ·
                    refine ⟨42888467558944962055875797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28592311705963308037250531 42888467558944962055875797)
                    ·
                      refine ⟨1005198458412772548184589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42888467558944962055875797 1005198458412772548184589)
                      ·
                        rfl

theorem cell23_1957617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1957617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957617 prefixEnd_1957617 := by exact prefixLift 1957617
  have htrace : WordTrace (prefixWord ++ tailWord_1957617) baseStart_1957617 baseEnd_1957617 := by
    simpa [prefixWord, tailWord_1957617, baseEnd_1957617] using wordTrace_append hprefix tailTrace_1957617
  have hstable : (prefixWord ++ tailWord_1957617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957617).length < 2 ^ (prefixWord ++ tailWord_1957617).sum := by decide
  have hdescent : baseEnd_1957617 < baseStart_1957617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957622 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1957622 : Nat := 118140960795 + 1957622 * 2 ^ 59
def prefixEnd_1957622 : Nat := 4983230072969 + 3 ^ 40 * 1957622 * 2
def baseEnd_1957622 : Nat := 1005201025816045028622067

theorem tailTrace_1957622 : CollatzResearch.WordTrace tailWord_1957622 prefixEnd_1957622 1005201025816045028622067 := by
  unfold tailWord_1957622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462521257117331504057695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47600226742584869376615413 4462521257117331504057695)
  ·
    refine ⟨6693781885675997256086543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4462521257117331504057695 6693781885675997256086543)
    ·
      refine ⟨10040672828513995884129815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693781885675997256086543 10040672828513995884129815)
      ·
        refine ⟨15061009242770993826194723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040672828513995884129815 15061009242770993826194723)
        ·
          refine ⟨22591513864156490739292085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061009242770993826194723 22591513864156490739292085)
          ·
            refine ⟨2117954424764671006808633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22591513864156490739292085 2117954424764671006808633)
            ·
              refine ⟨1588465818573503255106475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117954424764671006808633 1588465818573503255106475)
              ·
                refine ⟨2382698727860254882659713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588465818573503255106475 2382698727860254882659713)
                ·
                  refine ⟨1787024045895191161994785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2382698727860254882659713 1787024045895191161994785)
                  ·
                    refine ⟨1340268034421393371496089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787024045895191161994785 1340268034421393371496089)
                    ·
                      refine ⟨1005201025816045028622067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340268034421393371496089 1005201025816045028622067)
                      ·
                        rfl

theorem cell23_1957622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1957622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957622 prefixEnd_1957622 := by exact prefixLift 1957622
  have htrace : WordTrace (prefixWord ++ tailWord_1957622) baseStart_1957622 baseEnd_1957622 := by
    simpa [prefixWord, tailWord_1957622, baseEnd_1957622] using wordTrace_append hprefix tailTrace_1957622
  have hstable : (prefixWord ++ tailWord_1957622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957622).length < 2 ^ (prefixWord ++ tailWord_1957622).sum := by decide
  have hdescent : baseEnd_1957622 < baseStart_1957622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957627 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_1957627 : Nat := 118140960795 + 1957627 * 2 ^ 59
def prefixEnd_1957627 : Nat := 4983230072969 + 3 ^ 40 * 1957627 * 2
def baseEnd_1957627 : Nat := 1005203593219317509059543

theorem tailTrace_1957627 : CollatzResearch.WordTrace tailWord_1957627 prefixEnd_1957627 1005203593219317509059543 := by
  unfold tailWord_1957627
  simp only [CollatzResearch.WordTrace]
  refine ⟨71400522478859189918855135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47600348319239459945903423 71400522478859189918855135)
  ·
    refine ⟨107100783718288784878282703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71400522478859189918855135 107100783718288784878282703)
    ·
      refine ⟨160651175577433177317424055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107100783718288784878282703 160651175577433177317424055)
      ·
        refine ⟨240976763366149765976136083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160651175577433177317424055 240976763366149765976136083)
        ·
          refine ⟨361465145049224648964204125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240976763366149765976136083 361465145049224648964204125)
          ·
            refine ⟨135549429393459243361576547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361465145049224648964204125 135549429393459243361576547)
            ·
              refine ⟨203324144090188865042364821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135549429393459243361576547 203324144090188865042364821)
              ·
                refine ⟨9530819254227603048860851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203324144090188865042364821 9530819254227603048860851)
                ·
                  refine ⟨14296228881341404573291277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9530819254227603048860851 14296228881341404573291277)
                  ·
                    refine ⟨5361085830503026714984229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14296228881341404573291277 5361085830503026714984229)
                    ·
                      refine ⟨1005203593219317509059543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5361085830503026714984229 1005203593219317509059543)
                      ·
                        rfl

theorem cell23_1957627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_1957627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957627 prefixEnd_1957627 := by exact prefixLift 1957627
  have htrace : WordTrace (prefixWord ++ tailWord_1957627) baseStart_1957627 baseEnd_1957627 := by
    simpa [prefixWord, tailWord_1957627, baseEnd_1957627] using wordTrace_append hprefix tailTrace_1957627
  have hstable : (prefixWord ++ tailWord_1957627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957627).length < 2 ^ (prefixWord ++ tailWord_1957627).sum := by decide
  have hdescent : baseEnd_1957627 < baseStart_1957627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957634 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1957634 : Nat := 118140960795 + 1957634 * 2 ^ 59
def prefixEnd_1957634 : Nat := 4983230072969 + 3 ^ 40 * 1957634 * 2
def baseEnd_1957634 : Nat := 1005207187583898981672011

theorem tailTrace_1957634 : CollatzResearch.WordTrace tailWord_1957634 prefixEnd_1957634 1005207187583898981672011 := by
  unfold tailWord_1957634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17850194447458457528589989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47600518526555886742906637 17850194447458457528589989)
  ·
    refine ⟨3346911458898460786610623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17850194447458457528589989 3346911458898460786610623)
    ·
      refine ⟨5020367188347691179915935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346911458898460786610623 5020367188347691179915935)
      ·
        refine ⟨7530550782521536769873903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020367188347691179915935 7530550782521536769873903)
        ·
          refine ⟨11295826173782305154810855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530550782521536769873903 11295826173782305154810855)
          ·
            refine ⟨16943739260673457732216283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295826173782305154810855 16943739260673457732216283)
            ·
              refine ⟨25415608891010186598324425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943739260673457732216283 25415608891010186598324425)
              ·
                refine ⟨19061706668257639948743319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25415608891010186598324425 19061706668257639948743319)
                ·
                  refine ⟨28592560002386459923114979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19061706668257639948743319 28592560002386459923114979)
                  ·
                    refine ⟨42888840003579689884672469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28592560002386459923114979 42888840003579689884672469)
                    ·
                      refine ⟨1005207187583898981672011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42888840003579689884672469 1005207187583898981672011)
                      ·
                        rfl

theorem cell23_1957634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1957634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957634 prefixEnd_1957634 := by exact prefixLift 1957634
  have htrace : WordTrace (prefixWord ++ tailWord_1957634) baseStart_1957634 baseEnd_1957634 := by
    simpa [prefixWord, tailWord_1957634, baseEnd_1957634] using wordTrace_append hprefix tailTrace_1957634
  have hstable : (prefixWord ++ tailWord_1957634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957634).length < 2 ^ (prefixWord ++ tailWord_1957634).sum := by decide
  have hdescent : baseEnd_1957634 < baseStart_1957634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957644 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1957644 : Nat := 118140960795 + 1957644 * 2 ^ 59
def prefixEnd_1957644 : Nat := 4983230072969 + 3 ^ 40 * 1957644 * 2
def baseEnd_1957644 : Nat := 1005212322390443942546965

theorem tailTrace_1957644 : CollatzResearch.WordTrace tailWord_1957644 prefixEnd_1957644 1005212322390443942546965 := by
  unfold tailWord_1957644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35700571259898800911111993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47600761679865067881482657 35700571259898800911111993)
  ·
    refine ⟨26775428444924100683333995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35700571259898800911111993 26775428444924100683333995)
    ·
      refine ⟨40163142667386151025000993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26775428444924100683333995 40163142667386151025000993)
      ·
        refine ⟨30122357000539613268750745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40163142667386151025000993 30122357000539613268750745)
        ·
          refine ⟨22591767750404709951563059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30122357000539613268750745 22591767750404709951563059)
          ·
            refine ⟨33887651625607064927344589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22591767750404709951563059 33887651625607064927344589)
            ·
              refine ⟨12707869359602649347754221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33887651625607064927344589 12707869359602649347754221)
              ·
                refine ⟨4765451009850993505407833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12707869359602649347754221 4765451009850993505407833)
                ·
                  refine ⟨3574088257388245129055875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765451009850993505407833 3574088257388245129055875)
                  ·
                    refine ⟨5361132386082367693583813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574088257388245129055875 5361132386082367693583813)
                    ·
                      refine ⟨1005212322390443942546965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5361132386082367693583813 1005212322390443942546965)
                      ·
                        rfl

theorem cell23_1957644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1957644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957644 prefixEnd_1957644 := by exact prefixLift 1957644
  have htrace : WordTrace (prefixWord ++ tailWord_1957644) baseStart_1957644 baseEnd_1957644 := by
    simpa [prefixWord, tailWord_1957644, baseEnd_1957644] using wordTrace_append hprefix tailTrace_1957644
  have hstable : (prefixWord ++ tailWord_1957644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957644).length < 2 ^ (prefixWord ++ tailWord_1957644).sum := by decide
  have hdescent : baseEnd_1957644 < baseStart_1957644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957657 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1957657 : Nat := 118140960795 + 1957657 * 2 ^ 59
def prefixEnd_1957657 : Nat := 4983230072969 + 3 ^ 40 * 1957657 * 2
def baseEnd_1957657 : Nat := 1005218997638952391684405

theorem tailTrace_1957657 : CollatzResearch.WordTrace tailWord_1957657 prefixEnd_1957657 1005218997638952391684405 := by
  unfold tailWord_1957657
  simp only [CollatzResearch.WordTrace]
  refine ⟨71401616668750505042447225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47601077779167003361631483 71401616668750505042447225)
  ·
    refine ⟨53551212501562878781835419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71401616668750505042447225 53551212501562878781835419)
    ·
      refine ⟨80326818752344318172753129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53551212501562878781835419 80326818752344318172753129)
      ·
        refine ⟨60245114064258238629564847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80326818752344318172753129 60245114064258238629564847)
        ·
          refine ⟨90367671096387357944347271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60245114064258238629564847 90367671096387357944347271)
          ·
            refine ⟨135551506644581036916520907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90367671096387357944347271 135551506644581036916520907)
            ·
              refine ⟨203327259966871555374781361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135551506644581036916520907 203327259966871555374781361)
              ·
                refine ⟨152495444975153666531086021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203327259966871555374781361 152495444975153666531086021)
                ·
                  refine ⟨28592895932841312474578629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152495444975153666531086021 28592895932841312474578629)
                  ·
                    refine ⟨5361167987407746088983493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28592895932841312474578629 5361167987407746088983493)
                    ·
                      refine ⟨1005218997638952391684405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5361167987407746088983493 1005218997638952391684405)
                      ·
                        rfl

theorem cell23_1957657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1957657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957657 prefixEnd_1957657 := by exact prefixLift 1957657
  have htrace : WordTrace (prefixWord ++ tailWord_1957657) baseStart_1957657 baseEnd_1957657 := by
    simpa [prefixWord, tailWord_1957657, baseEnd_1957657] using wordTrace_append hprefix tailTrace_1957657
  have hstable : (prefixWord ++ tailWord_1957657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957657).length < 2 ^ (prefixWord ++ tailWord_1957657).sum := by decide
  have hdescent : baseEnd_1957657 < baseStart_1957657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957667 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 8]
def baseStart_1957667 : Nat := 118140960795 + 1957667 * 2 ^ 59
def prefixEnd_1957667 : Nat := 4983230072969 + 3 ^ 40 * 1957667 * 2
def baseEnd_1957667 : Nat := 111691570271721928062151

theorem tailTrace_1957667 : CollatzResearch.WordTrace tailWord_1957667 prefixEnd_1957667 111691570271721928062151 := by
  unfold tailWord_1957667
  simp only [CollatzResearch.WordTrace]
  refine ⟨71401981398714276750311255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47601320932476184500207503 71401981398714276750311255)
  ·
    refine ⟨107102972098071415125466883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71401981398714276750311255 107102972098071415125466883)
    ·
      refine ⟨160654458147107122688200325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107102972098071415125466883 160654458147107122688200325)
      ·
        refine ⟨30122710902582585504037561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160654458147107122688200325 30122710902582585504037561)
        ·
          refine ⟨22592033176936939128028171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30122710902582585504037561 22592033176936939128028171)
          ·
            refine ⟨33888049765405408692042257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22592033176936939128028171 33888049765405408692042257)
            ·
              refine ⟨25416037324054056519031693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33888049765405408692042257 25416037324054056519031693)
              ·
                refine ⟨9531013996520271194636885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25416037324054056519031693 9531013996520271194636885)
                ·
                  refine ⟨111691570271721928062151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9531013996520271194636885 111691570271721928062151)
                  ·
                    rfl

theorem cell23_1957667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 8].length) (baseStart_1957667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957667 prefixEnd_1957667 := by exact prefixLift 1957667
  have htrace : WordTrace (prefixWord ++ tailWord_1957667) baseStart_1957667 baseEnd_1957667 := by
    simpa [prefixWord, tailWord_1957667, baseEnd_1957667] using wordTrace_append hprefix tailTrace_1957667
  have hstable : (prefixWord ++ tailWord_1957667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957667).length < 2 ^ (prefixWord ++ tailWord_1957667).sum := by decide
  have hdescent : baseEnd_1957667 < baseStart_1957667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1957687 : Nat := 118140960795 + 1957687 * 2 ^ 59
def prefixEnd_1957687 : Nat := 4983230072969 + 3 ^ 40 * 1957687 * 2
def baseEnd_1957687 : Nat := 1005234402058587274309267

theorem tailTrace_1957687 : CollatzResearch.WordTrace tailWord_1957687 prefixEnd_1957687 1005234402058587274309267 := by
  unfold tailWord_1957687
  simp only [CollatzResearch.WordTrace]
  refine ⟨71402710858641820166039315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47601807239094546777359543 71402710858641820166039315)
  ·
    refine ⟨107104066287962730249058973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71402710858641820166039315 107104066287962730249058973)
    ·
      refine ⟨40164024857986023843397115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107104066287962730249058973 40164024857986023843397115)
      ·
        refine ⟨60246037286979035765095673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40164024857986023843397115 60246037286979035765095673)
        ·
          refine ⟨45184527965234276823821755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60246037286979035765095673 45184527965234276823821755)
          ·
            refine ⟨67776791947851415235732633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45184527965234276823821755 67776791947851415235732633)
            ·
              refine ⟨50832593960888561426799475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67776791947851415235732633 50832593960888561426799475)
              ·
                refine ⟨76248890941332842140199213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50832593960888561426799475 76248890941332842140199213)
                ·
                  refine ⟨28593334102999815802574705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76248890941332842140199213 28593334102999815802574705)
                  ·
                    refine ⟨21445000577249861851931029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28593334102999815802574705 21445000577249861851931029)
                    ·
                      refine ⟨1005234402058587274309267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21445000577249861851931029 1005234402058587274309267)
                      ·
                        rfl

theorem cell23_1957687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1957687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957687 prefixEnd_1957687 := by exact prefixLift 1957687
  have htrace : WordTrace (prefixWord ++ tailWord_1957687) baseStart_1957687 baseEnd_1957687 := by
    simpa [prefixWord, tailWord_1957687, baseEnd_1957687] using wordTrace_append hprefix tailTrace_1957687
  have hstable : (prefixWord ++ tailWord_1957687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957687).length < 2 ^ (prefixWord ++ tailWord_1957687).sum := by decide
  have hdescent : baseEnd_1957687 < baseStart_1957687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957721 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 4, 3, 2]
def baseStart_1957721 : Nat := 118140960795 + 1957721 * 2 ^ 59
def prefixEnd_1957721 : Nat := 4983230072969 + 3 ^ 40 * 1957721 * 2
def baseEnd_1957721 : Nat := 1005251860400840141284111

theorem tailTrace_1957721 : CollatzResearch.WordTrace tailWord_1957721 prefixEnd_1957721 1005251860400840141284111 := by
  unfold tailWord_1957721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71403950940518643972777017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47602633960345762648518011 71403950940518643972777017)
  ·
    refine ⟨53552963205388982979582763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71403950940518643972777017 53552963205388982979582763)
    ·
      refine ⟨80329444808083474469374145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53552963205388982979582763 80329444808083474469374145)
      ·
        refine ⟨60247083606062605852030609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80329444808083474469374145 60247083606062605852030609)
        ·
          refine ⟨45185312704546954389022957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60247083606062605852030609 45185312704546954389022957)
          ·
            refine ⟨16944492264205107895883609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45185312704546954389022957 16944492264205107895883609)
            ·
              refine ⟨12708369198153830921912707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16944492264205107895883609 12708369198153830921912707)
              ·
                refine ⟨19062553797230746382869061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12708369198153830921912707 19062553797230746382869061)
                ·
                  refine ⟨3574228836980764946787949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19062553797230746382869061 3574228836980764946787949)
                  ·
                    refine ⟨1340335813867786855045481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574228836980764946787949 1340335813867786855045481)
                    ·
                      refine ⟨1005251860400840141284111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340335813867786855045481 1005251860400840141284111)
                      ·
                        rfl

theorem cell23_1957721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_1957721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957721 prefixEnd_1957721 := by exact prefixLift 1957721
  have htrace : WordTrace (prefixWord ++ tailWord_1957721) baseStart_1957721 baseEnd_1957721 := by
    simpa [prefixWord, tailWord_1957721, baseEnd_1957721] using wordTrace_append hprefix tailTrace_1957721
  have hstable : (prefixWord ++ tailWord_1957721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957721).length < 2 ^ (prefixWord ++ tailWord_1957721).sum := by decide
  have hdescent : baseEnd_1957721 < baseStart_1957721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957728 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3]
def baseStart_1957728 : Nat := 118140960795 + 1957728 * 2 ^ 59
def prefixEnd_1957728 : Nat := 4983230072969 + 3 ^ 40 * 1957728 * 2
def baseEnd_1957728 : Nat := 1005255454765421613896579

theorem tailTrace_1957728 : CollatzResearch.WordTrace tailWord_1957728 prefixEnd_1957728 1005255454765421613896579 := by
  unfold tailWord_1957728
  simp only [CollatzResearch.WordTrace]
  refine ⟨35702103125746642084140919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47602804167662189445521225 35702103125746642084140919)
  ·
    refine ⟨53553154688619963126211379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35702103125746642084140919 53553154688619963126211379)
    ·
      refine ⟨80329732032929944689317069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53553154688619963126211379 80329732032929944689317069)
      ·
        refine ⟨30123649512348729258493901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80329732032929944689317069 30123649512348729258493901)
        ·
          refine ⟨11296368567130773471935213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30123649512348729258493901 11296368567130773471935213)
          ·
            refine ⟨4236138212674040051975705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11296368567130773471935213 4236138212674040051975705)
            ·
              refine ⟨3177103659505530038981779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236138212674040051975705 3177103659505530038981779)
              ·
                refine ⟨4765655489258295058472669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177103659505530038981779 4765655489258295058472669)
                ·
                  refine ⟨1787120808471860646927251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4765655489258295058472669 1787120808471860646927251)
                  ·
                    refine ⟨2680681212707790970390877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787120808471860646927251 2680681212707790970390877)
                    ·
                      refine ⟨1005255454765421613896579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2680681212707790970390877 1005255454765421613896579)
                      ·
                        rfl

theorem cell23_1957728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_1957728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957728 prefixEnd_1957728 := by exact prefixLift 1957728
  have htrace : WordTrace (prefixWord ++ tailWord_1957728) baseStart_1957728 baseEnd_1957728 := by
    simpa [prefixWord, tailWord_1957728, baseEnd_1957728] using wordTrace_append hprefix tailTrace_1957728
  have hstable : (prefixWord ++ tailWord_1957728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957728).length < 2 ^ (prefixWord ++ tailWord_1957728).sum := by decide
  have hdescent : baseEnd_1957728 < baseStart_1957728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957778 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1957778 : Nat := 118140960795 + 1957778 * 2 ^ 59
def prefixEnd_1957778 : Nat := 4983230072969 + 3 ^ 40 * 1957778 * 2
def baseEnd_1957778 : Nat := 335093709599382139423783

theorem tailTrace_1957778 : CollatzResearch.WordTrace tailWord_1957778 prefixEnd_1957778 335093709599382139423783 := by
  unfold tailWord_1957778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851507475328035676900497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47604019934208095138401325 17851507475328035676900497)
  ·
    refine ⟨13388630606496026757675373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17851507475328035676900497 13388630606496026757675373)
    ·
      refine ⟨5020736477436010034128265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13388630606496026757675373 5020736477436010034128265)
      ·
        refine ⟨3765552358077007525596199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5020736477436010034128265 3765552358077007525596199)
        ·
          refine ⟨5648328537115511288394299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765552358077007525596199 5648328537115511288394299)
          ·
            refine ⟨8472492805673266932591449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648328537115511288394299 8472492805673266932591449)
            ·
              refine ⟨6354369604254950199443587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8472492805673266932591449 6354369604254950199443587)
              ·
                refine ⟨9531554406382425299165381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354369604254950199443587 9531554406382425299165381)
                ·
                  refine ⟨1787166451196704743593509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9531554406382425299165381 1787166451196704743593509)
                  ·
                    refine ⟨335093709599382139423783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787166451196704743593509 335093709599382139423783)
                    ·
                      rfl

theorem cell23_1957778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1957778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957778 prefixEnd_1957778 := by exact prefixLift 1957778
  have htrace : WordTrace (prefixWord ++ tailWord_1957778) baseStart_1957778 baseEnd_1957778 := by
    simpa [prefixWord, tailWord_1957778, baseEnd_1957778] using wordTrace_append hprefix tailTrace_1957778
  have hstable : (prefixWord ++ tailWord_1957778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957778).length < 2 ^ (prefixWord ++ tailWord_1957778).sum := by decide
  have hdescent : baseEnd_1957778 < baseStart_1957778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957785 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 1, 2, 2]
def baseStart_1957785 : Nat := 118140960795 + 1957785 * 2 ^ 59
def prefixEnd_1957785 : Nat := 4983230072969 + 3 ^ 40 * 1957785 * 2
def baseEnd_1957785 : Nat := 1005284723162727890883817

theorem tailTrace_1957785 : CollatzResearch.WordTrace tailWord_1957785 prefixEnd_1957785 1005284723162727890883817 := by
  unfold tailWord_1957785
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406285212286782903106809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47604190141524521935404539 71406285212286782903106809)
  ·
    refine ⟨53554713909215087177330107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71406285212286782903106809 53554713909215087177330107)
    ·
      refine ⟨80332070863822630765995161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53554713909215087177330107 80332070863822630765995161)
      ·
        refine ⟨60249053147866973074496371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80332070863822630765995161 60249053147866973074496371)
        ·
          refine ⟨90373579721800459611744557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60249053147866973074496371 90373579721800459611744557)
          ·
            refine ⟨33890092395675172354404209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90373579721800459611744557 33890092395675172354404209)
            ·
              refine ⟨25417569296756379265803157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33890092395675172354404209 25417569296756379265803157)
              ·
                refine ⟨1191448560785455278084523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25417569296756379265803157 1191448560785455278084523)
                ·
                  refine ⟨1787172841178182917126785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191448560785455278084523 1787172841178182917126785)
                  ·
                    refine ⟨1340379630883637187845089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787172841178182917126785 1340379630883637187845089)
                    ·
                      refine ⟨1005284723162727890883817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340379630883637187845089 1005284723162727890883817)
                      ·
                        rfl

theorem cell23_1957785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_1957785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957785 prefixEnd_1957785 := by exact prefixLift 1957785
  have htrace : WordTrace (prefixWord ++ tailWord_1957785) baseStart_1957785 baseEnd_1957785 := by
    simpa [prefixWord, tailWord_1957785, baseEnd_1957785] using wordTrace_append hprefix tailTrace_1957785
  have hstable : (prefixWord ++ tailWord_1957785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957785).length < 2 ^ (prefixWord ++ tailWord_1957785).sum := by decide
  have hdescent : baseEnd_1957785 < baseStart_1957785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957791 : List Nat := [1, 1, 2, 5, 3, 1, 2, 8]
def baseStart_1957791 : Nat := 118140960795 + 1957791 * 2 ^ 59
def prefixEnd_1957791 : Nat := 4983230072969 + 3 ^ 40 * 1957791 * 2
def baseEnd_1957791 : Nat := 37232881631357587681807

theorem tailTrace_1957791 : CollatzResearch.WordTrace tailWord_1957791 prefixEnd_1957791 37232881631357587681807 := by
  unfold tailWord_1957791
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406504050265045927825227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47604336033510030618550151 71406504050265045927825227)
  ·
    refine ⟨107109756075397568891737841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71406504050265045927825227 107109756075397568891737841)
    ·
      refine ⟨80332317056548176668803381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107109756075397568891737841 80332317056548176668803381)
      ·
        refine ⟨7531154724051391562700317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80332317056548176668803381 7531154724051391562700317)
        ·
          refine ⟨2824183021519271836012619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7531154724051391562700317 2824183021519271836012619)
          ·
            refine ⟨4236274532278907754018929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824183021519271836012619 4236274532278907754018929)
            ·
              refine ⟨3177205899209180815514197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236274532278907754018929 3177205899209180815514197)
              ·
                refine ⟨37232881631357587681807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3177205899209180815514197 37232881631357587681807)
                ·
                  rfl

theorem cell23_1957791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 8].length) (baseStart_1957791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957791 prefixEnd_1957791 := by exact prefixLift 1957791
  have htrace : WordTrace (prefixWord ++ tailWord_1957791) baseStart_1957791 baseEnd_1957791 := by
    simpa [prefixWord, tailWord_1957791, baseEnd_1957791] using wordTrace_append hprefix tailTrace_1957791
  have hstable : (prefixWord ++ tailWord_1957791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957791).length < 2 ^ (prefixWord ++ tailWord_1957791).sum := by decide
  have hdescent : baseEnd_1957791 < baseStart_1957791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957801 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 3]
def baseStart_1957801 : Nat := 118140960795 + 1957801 * 2 ^ 59
def prefixEnd_1957801 : Nat := 4983230072969 + 3 ^ 40 * 1957801 * 2
def baseEnd_1957801 : Nat := 1005292938853199828283743

theorem tailTrace_1957801 : CollatzResearch.WordTrace tailWord_1957801 prefixEnd_1957801 1005292938853199828283743 := by
  unfold tailWord_1957801
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406868780228817635689257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47604579186819211757126171 71406868780228817635689257)
  ·
    refine ⟨53555151585171613226766943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71406868780228817635689257 53555151585171613226766943)
    ·
      refine ⟨80332727377757419840150415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53555151585171613226766943 80332727377757419840150415)
      ·
        refine ⟨120499091066636129760225623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80332727377757419840150415 120499091066636129760225623)
        ·
          refine ⟨180748636599954194640338435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120499091066636129760225623 180748636599954194640338435)
          ·
            refine ⟨271122954899931291960507653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180748636599954194640338435 271122954899931291960507653)
            ·
              refine ⟨50835554043737117242595185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271122954899931291960507653 50835554043737117242595185)
              ·
                refine ⟨38126665532802837931946389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50835554043737117242595185 38126665532802837931946389)
                ·
                  refine ⟨1787187446850133028059987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38126665532802837931946389 1787187446850133028059987)
                  ·
                    refine ⟨2680781170275199542089981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787187446850133028059987 2680781170275199542089981)
                    ·
                      refine ⟨1005292938853199828283743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2680781170275199542089981 1005292938853199828283743)
                      ·
                        rfl

theorem cell23_1957801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_1957801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957801 prefixEnd_1957801 := by exact prefixLift 1957801
  have htrace : WordTrace (prefixWord ++ tailWord_1957801) baseStart_1957801 baseEnd_1957801 := by
    simpa [prefixWord, tailWord_1957801, baseEnd_1957801] using wordTrace_append hprefix tailTrace_1957801
  have hstable : (prefixWord ++ tailWord_1957801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957801).length < 2 ^ (prefixWord ++ tailWord_1957801).sum := by decide
  have hdescent : baseEnd_1957801 < baseStart_1957801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957898 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_1957898 : Nat := 118140960795 + 1957898 * 2 ^ 59
def prefixEnd_1957898 : Nat := 4983230072969 + 3 ^ 40 * 1957898 * 2
def baseEnd_1957898 : Nat := 111704749608520660974533

theorem tailTrace_1957898 : CollatzResearch.WordTrace tailWord_1957898 prefixEnd_1957898 111704749608520660974533 := by
  unfold tailWord_1957898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17852601665219350800492587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47606937773918268801313565 17852601665219350800492587)
  ·
    refine ⟨26778902497829026200738881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17852601665219350800492587 26778902497829026200738881)
    ·
      refine ⟨20084176873371769650554161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26778902497829026200738881 20084176873371769650554161)
      ·
        refine ⟨15063132655028827237915621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20084176873371769650554161 15063132655028827237915621)
        ·
          refine ⟨2824337372817905107109179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15063132655028827237915621 2824337372817905107109179)
          ·
            refine ⟨4236506059226857660663769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824337372817905107109179 4236506059226857660663769)
            ·
              refine ⟨3177379544420143245497827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236506059226857660663769 3177379544420143245497827)
              ·
                refine ⟨4766069316630214868246741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177379544420143245497827 4766069316630214868246741)
                ·
                  refine ⟨111704749608520660974533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4766069316630214868246741 111704749608520660974533)
                  ·
                    rfl

theorem cell23_1957898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_1957898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957898 prefixEnd_1957898 := by exact prefixLift 1957898
  have htrace : WordTrace (prefixWord ++ tailWord_1957898) baseStart_1957898 baseEnd_1957898 := by
    simpa [prefixWord, tailWord_1957898, baseEnd_1957898] using wordTrace_append hprefix tailTrace_1957898
  have hstable : (prefixWord ++ tailWord_1957898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957898).length < 2 ^ (prefixWord ++ tailWord_1957898).sum := by decide
  have hdescent : baseEnd_1957898 < baseStart_1957898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957909 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_1957909 : Nat := 118140960795 + 1957909 * 2 ^ 59
def prefixEnd_1957909 : Nat := 4983230072969 + 3 ^ 40 * 1957909 * 2
def baseEnd_1957909 : Nat := 1005348394763885405733247

theorem tailTrace_1957909 : CollatzResearch.WordTrace tailWord_1957909 prefixEnd_1957909 1005348394763885405733247 := by
  unfold tailWord_1957909
  simp only [CollatzResearch.WordTrace]
  refine ⟨71410807863837552080620781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47607205242558368053747187 71410807863837552080620781)
  ·
    refine ⟨26779052948939082030232793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71410807863837552080620781 26779052948939082030232793)
    ·
      refine ⟨20084289711704311522674595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26779052948939082030232793 20084289711704311522674595)
      ·
        refine ⟨30126434567556467284011893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20084289711704311522674595 30126434567556467284011893)
        ·
          refine ⟨2824353240708418807876115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30126434567556467284011893 2824353240708418807876115)
          ·
            refine ⟨4236529861062628211814173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824353240708418807876115 4236529861062628211814173)
            ·
              refine ⟨1588698697898485579430315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4236529861062628211814173 1588698697898485579430315)
              ·
                refine ⟨2383048046847728369145473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588698697898485579430315 2383048046847728369145473)
                ·
                  refine ⟨1787286035135796276859105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383048046847728369145473 1787286035135796276859105)
                  ·
                    refine ⟨1340464526351847207644329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787286035135796276859105 1340464526351847207644329)
                    ·
                      refine ⟨1005348394763885405733247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340464526351847207644329 1005348394763885405733247)
                      ·
                        rfl

theorem cell23_1957909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_1957909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957909 prefixEnd_1957909 := by exact prefixLift 1957909
  have htrace : WordTrace (prefixWord ++ tailWord_1957909) baseStart_1957909 baseEnd_1957909 := by
    simpa [prefixWord, tailWord_1957909, baseEnd_1957909] using wordTrace_append hprefix tailTrace_1957909
  have hstable : (prefixWord ++ tailWord_1957909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957909).length < 2 ^ (prefixWord ++ tailWord_1957909).sum := by decide
  have hdescent : baseEnd_1957909 < baseStart_1957909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957948 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1957948 : Nat := 118140960795 + 1957948 * 2 ^ 59
def prefixEnd_1957948 : Nat := 4983230072969 + 3 ^ 40 * 1957948 * 2
def baseEnd_1957948 : Nat := 1005368420509410753145567

theorem tailTrace_1957948 : CollatzResearch.WordTrace tailWord_1957948 prefixEnd_1957948 1005368420509410753145567 := by
  unfold tailWord_1957948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35706115155348130870645249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47608153540464174494193665 35706115155348130870645249)
  ·
    refine ⟨26779586366511098152983937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35706115155348130870645249 26779586366511098152983937)
    ·
      refine ⟨20084689774883323614737953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26779586366511098152983937 20084689774883323614737953)
      ·
        refine ⟨15063517331162492711053465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20084689774883323614737953 15063517331162492711053465)
        ·
          refine ⟨11297637998371869533290099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15063517331162492711053465 11297637998371869533290099)
          ·
            refine ⟨16946456997557804299935149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297637998371869533290099 16946456997557804299935149)
            ·
              refine ⟨6354921374084176612475681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16946456997557804299935149 6354921374084176612475681)
              ·
                refine ⟨4766191030563132459356761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6354921374084176612475681 4766191030563132459356761)
                ·
                  refine ⟨3574643272922349344517571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766191030563132459356761 3574643272922349344517571)
                  ·
                    refine ⟨5361964909383524016776357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3574643272922349344517571 5361964909383524016776357)
                    ·
                      refine ⟨1005368420509410753145567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5361964909383524016776357 1005368420509410753145567)
                      ·
                        rfl

theorem cell23_1957948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1957948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957948 prefixEnd_1957948 := by exact prefixLift 1957948
  have htrace : WordTrace (prefixWord ++ tailWord_1957948) baseStart_1957948 baseEnd_1957948 := by
    simpa [prefixWord, tailWord_1957948, baseEnd_1957948] using wordTrace_append hprefix tailTrace_1957948
  have hstable : (prefixWord ++ tailWord_1957948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957948).length < 2 ^ (prefixWord ++ tailWord_1957948).sum := by decide
  have hdescent : baseEnd_1957948 < baseStart_1957948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957965 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_1957965 : Nat := 118140960795 + 1957965 * 2 ^ 59
def prefixEnd_1957965 : Nat := 4983230072969 + 3 ^ 40 * 1957965 * 2
def baseEnd_1957965 : Nat := 1005377149680537186632989

theorem tailTrace_1957965 : CollatzResearch.WordTrace tailWord_1957965 prefixEnd_1957965 1005377149680537186632989 := by
  unfold tailWord_1957965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412850351634673644659349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47608566901089782429772899 71412850351634673644659349)
  ·
    refine ⟨3347477360232875327093407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71412850351634673644659349 3347477360232875327093407)
    ·
      refine ⟨5021216040349312990640111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347477360232875327093407 5021216040349312990640111)
      ·
        refine ⟨7531824060523969485960167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021216040349312990640111 7531824060523969485960167)
        ·
          refine ⟨11297736090785954228940251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531824060523969485960167 11297736090785954228940251)
          ·
            refine ⟨16946604136178931343410377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297736090785954228940251 16946604136178931343410377)
            ·
              refine ⟨12709953102134198507557783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16946604136178931343410377 12709953102134198507557783)
              ·
                refine ⟨19064929653201297761336675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12709953102134198507557783 19064929653201297761336675)
                ·
                  refine ⟨28597394479801946642005013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19064929653201297761336675 28597394479801946642005013)
                  ·
                    refine ⟨1340502866240716248843985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28597394479801946642005013 1340502866240716248843985)
                    ·
                      refine ⟨1005377149680537186632989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340502866240716248843985 1005377149680537186632989)
                      ·
                        rfl

theorem cell23_1957965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_1957965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1957965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1957965 prefixEnd_1957965 := by exact prefixLift 1957965
  have htrace : WordTrace (prefixWord ++ tailWord_1957965) baseStart_1957965 baseEnd_1957965 := by
    simpa [prefixWord, tailWord_1957965, baseEnd_1957965] using wordTrace_append hprefix tailTrace_1957965
  have hstable : (prefixWord ++ tailWord_1957965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957965).length < 2 ^ (prefixWord ++ tailWord_1957965).sum := by decide
  have hdescent : baseEnd_1957965 < baseStart_1957965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958008 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_1958008 : Nat := 118140960795 + 1958008 * 2 ^ 59
def prefixEnd_1958008 : Nat := 4983230072969 + 3 ^ 40 * 1958008 * 2
def baseEnd_1958008 : Nat := 1005399229348680518395291

theorem tailTrace_1958008 : CollatzResearch.WordTrace tailWord_1958008 prefixEnd_1958008 1005399229348680518395291 := by
  unfold tailWord_1958008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707209345239445994237339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47609612460319261325649785 35707209345239445994237339)
  ·
    refine ⟨53560814017859168991356009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35707209345239445994237339 53560814017859168991356009)
    ·
      refine ⟨40170610513394376743517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53560814017859168991356009 40170610513394376743517007)
      ·
        refine ⟨60255915770091565115275511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40170610513394376743517007 60255915770091565115275511)
        ·
          refine ⟨90383873655137347672913267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60255915770091565115275511 90383873655137347672913267)
          ·
            refine ⟨135575810482706021509369901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90383873655137347672913267 135575810482706021509369901)
            ·
              refine ⟨50840928931014758066013713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135575810482706021509369901 50840928931014758066013713)
              ·
                refine ⟨38130696698261068549510285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50840928931014758066013713 38130696698261068549510285)
                ·
                  refine ⟨14299011261847900706066357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38130696698261068549510285 14299011261847900706066357)
                  ·
                    refine ⟨1340532305798240691193721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14299011261847900706066357 1340532305798240691193721)
                    ·
                      refine ⟨1005399229348680518395291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340532305798240691193721 1005399229348680518395291)
                      ·
                        rfl

theorem cell23_1958008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_1958008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958008 prefixEnd_1958008 := by exact prefixLift 1958008
  have htrace : WordTrace (prefixWord ++ tailWord_1958008) baseStart_1958008 baseEnd_1958008 := by
    simpa [prefixWord, tailWord_1958008, baseEnd_1958008] using wordTrace_append hprefix tailTrace_1958008
  have hstable : (prefixWord ++ tailWord_1958008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958008).length < 2 ^ (prefixWord ++ tailWord_1958008).sum := by decide
  have hdescent : baseEnd_1958008 < baseStart_1958008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958009 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 1, 4]
def baseStart_1958009 : Nat := 118140960795 + 1958009 * 2 ^ 59
def prefixEnd_1958009 : Nat := 4983230072969 + 3 ^ 40 * 1958009 * 2
def baseEnd_1958009 : Nat := 335133247609778338160929

theorem tailTrace_1958009 : CollatzResearch.WordTrace tailWord_1958009 prefixEnd_1958009 335133247609778338160929 := by
  unfold tailWord_1958009
  simp only [CollatzResearch.WordTrace]
  refine ⟨71414455163475269159261081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47609636775650179439507387 71414455163475269159261081)
  ·
    refine ⟨53560841372606451869445811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71414455163475269159261081 53560841372606451869445811)
    ·
      refine ⟨80341262058909677804168717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53560841372606451869445811 80341262058909677804168717)
      ·
        refine ⟨30127973272091129176563269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80341262058909677804168717 30127973272091129176563269)
        ·
          refine ⟨5648994988517086720605613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30127973272091129176563269 5648994988517086720605613)
          ·
            refine ⟨2118373120693907520227105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5648994988517086720605613 2118373120693907520227105)
            ·
              refine ⟨1588779840520430640170329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118373120693907520227105 1588779840520430640170329)
              ·
                refine ⟨1191584880390322980127747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588779840520430640170329 1191584880390322980127747)
                ·
                  refine ⟨1787377320585484470191621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191584880390322980127747 1787377320585484470191621)
                  ·
                    refine ⟨335133247609778338160929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787377320585484470191621 335133247609778338160929)
                    ·
                      rfl

theorem cell23_1958009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 4].length) (baseStart_1958009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958009 prefixEnd_1958009 := by exact prefixLift 1958009
  have htrace : WordTrace (prefixWord ++ tailWord_1958009) baseStart_1958009 baseEnd_1958009 := by
    simpa [prefixWord, tailWord_1958009, baseEnd_1958009] using wordTrace_append hprefix tailTrace_1958009
  have hstable : (prefixWord ++ tailWord_1958009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958009).length < 2 ^ (prefixWord ++ tailWord_1958009).sum := by decide
  have hdescent : baseEnd_1958009 < baseStart_1958009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958036 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1958036 : Nat := 118140960795 + 1958036 * 2 ^ 59
def prefixEnd_1958036 : Nat := 4983230072969 + 3 ^ 40 * 1958036 * 2
def baseEnd_1958036 : Nat := 1005413606807006408845163

theorem tailTrace_1958036 : CollatzResearch.WordTrace tailWord_1958036 prefixEnd_1958036 1005413606807006408845163 := by
  unfold tailWord_1958036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707719967188726385246981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47610293289584968513662641 35707719967188726385246981)
  ·
    refine ⟨6695197493847886197233809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35707719967188726385246981 6695197493847886197233809)
    ·
      refine ⟨5021398120385914647925357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6695197493847886197233809 5021398120385914647925357)
      ·
        refine ⟨1883024295144717992972009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5021398120385914647925357 1883024295144717992972009)
        ·
          refine ⟨1412268221358538494729007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883024295144717992972009 1412268221358538494729007)
          ·
            refine ⟨2118402332037807742093511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412268221358538494729007 2118402332037807742093511)
            ·
              refine ⟨3177603498056711613140267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118402332037807742093511 3177603498056711613140267)
              ·
                refine ⟨4766405247085067419710401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177603498056711613140267 4766405247085067419710401)
                ·
                  refine ⟨3574803935313800564782801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766405247085067419710401 3574803935313800564782801)
                  ·
                    refine ⟨2681102951485350423587101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3574803935313800564782801 2681102951485350423587101)
                    ·
                      refine ⟨1005413606807006408845163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681102951485350423587101 1005413606807006408845163)
                      ·
                        rfl

theorem cell23_1958036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1958036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958036 prefixEnd_1958036 := by exact prefixLift 1958036
  have htrace : WordTrace (prefixWord ++ tailWord_1958036) baseStart_1958036 baseEnd_1958036 := by
    simpa [prefixWord, tailWord_1958036, baseEnd_1958036] using wordTrace_append hprefix tailTrace_1958036
  have hstable : (prefixWord ++ tailWord_1958036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958036).length < 2 ^ (prefixWord ++ tailWord_1958036).sum := by decide
  have hdescent : baseEnd_1958036 < baseStart_1958036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958042 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1958042 : Nat := 118140960795 + 1958042 * 2 ^ 59
def prefixEnd_1958042 : Nat := 4983230072969 + 3 ^ 40 * 1958042 * 2
def baseEnd_1958042 : Nat := 1005416687690933385370135

theorem tailTrace_1958042 : CollatzResearch.WordTrace tailWord_1958042 prefixEnd_1958042 1005416687690933385370135 := by
  unfold tailWord_1958042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17853914693088928948803095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47610439181570477196808253 17853914693088928948803095)
  ·
    refine ⟨26780872039633393423204643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17853914693088928948803095 26780872039633393423204643)
    ·
      refine ⟨40171308059450090134806965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26780872039633393423204643 40171308059450090134806965)
      ·
        refine ⟨3766060130573445950138153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40171308059450090134806965 3766060130573445950138153)
        ·
          refine ⟨2824545097930084462603615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766060130573445950138153 2824545097930084462603615)
          ·
            refine ⟨4236817646895126693905423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824545097930084462603615 4236817646895126693905423)
            ·
              refine ⟨6355226470342690040858135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236817646895126693905423 6355226470342690040858135)
              ·
                refine ⟨9532839705514035061287203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355226470342690040858135 9532839705514035061287203)
                ·
                  refine ⟨14299259558271052591930805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9532839705514035061287203 14299259558271052591930805)
                  ·
                    refine ⟨1340555583587911180493513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14299259558271052591930805 1340555583587911180493513)
                    ·
                      refine ⟨1005416687690933385370135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340555583587911180493513 1005416687690933385370135)
                      ·
                        rfl

theorem cell23_1958042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1958042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958042 prefixEnd_1958042 := by exact prefixLift 1958042
  have htrace : WordTrace (prefixWord ++ tailWord_1958042) baseStart_1958042 baseEnd_1958042 := by
    simpa [prefixWord, tailWord_1958042, baseEnd_1958042] using wordTrace_append hprefix tailTrace_1958042
  have hstable : (prefixWord ++ tailWord_1958042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958042).length < 2 ^ (prefixWord ++ tailWord_1958042).sum := by decide
  have hdescent : baseEnd_1958042 < baseStart_1958042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958048 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_1958048 : Nat := 118140960795 + 1958048 * 2 ^ 59
def prefixEnd_1958048 : Nat := 4983230072969 + 3 ^ 40 * 1958048 * 2
def baseEnd_1958048 : Nat := 335139922858286787298369

theorem tailTrace_1958048 : CollatzResearch.WordTrace tailWord_1958048 prefixEnd_1958048 335139922858286787298369 := by
  unfold tailWord_1958048
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707938805166989409965399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47610585073555985879953865 35707938805166989409965399)
  ·
    refine ⟨53561908207750484114948099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35707938805166989409965399 53561908207750484114948099)
    ·
      refine ⟨80342862311625726172422149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53561908207750484114948099 80342862311625726172422149)
      ·
        refine ⟨15064286683429823657329153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80342862311625726172422149 15064286683429823657329153)
        ·
          refine ⟨11298215012572367742996865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15064286683429823657329153 11298215012572367742996865)
          ·
            refine ⟨8473661259429275807247649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298215012572367742996865 8473661259429275807247649)
            ·
              refine ⟨6355245944571956855435737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473661259429275807247649 6355245944571956855435737)
              ·
                refine ⟨4766434458428967641576803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6355245944571956855435737 4766434458428967641576803)
                ·
                  refine ⟨7149651687643451462365205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766434458428967641576803 7149651687643451462365205)
                  ·
                    refine ⟨335139922858286787298369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7149651687643451462365205 335139922858286787298369)
                    ·
                      rfl

theorem cell23_1958048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_1958048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958048 prefixEnd_1958048 := by exact prefixLift 1958048
  have htrace : WordTrace (prefixWord ++ tailWord_1958048) baseStart_1958048 baseEnd_1958048 := by
    simpa [prefixWord, tailWord_1958048, baseEnd_1958048] using wordTrace_append hprefix tailTrace_1958048
  have hstable : (prefixWord ++ tailWord_1958048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958048).length < 2 ^ (prefixWord ++ tailWord_1958048).sum := by decide
  have hdescent : baseEnd_1958048 < baseStart_1958048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958049 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1958049 : Nat := 118140960795 + 1958049 * 2 ^ 59
def prefixEnd_1958049 : Nat := 4983230072969 + 3 ^ 40 * 1958049 * 2
def baseEnd_1958049 : Nat := 1005420282055514857982603

theorem tailTrace_1958049 : CollatzResearch.WordTrace tailWord_1958049 prefixEnd_1958049 1005420282055514857982603 := by
  unfold tailWord_1958049
  simp only [CollatzResearch.WordTrace]
  refine ⟨71415914083330355990717201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47610609388886903993811467 71415914083330355990717201)
  ·
    refine ⟨53561935562497766993037901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71415914083330355990717201 53561935562497766993037901)
    ·
      refine ⟨20085725835936662622389213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53561935562497766993037901 20085725835936662622389213)
      ·
        refine ⟨7532147188476248483395955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20085725835936662622389213 7532147188476248483395955)
        ·
          refine ⟨11298220782714372725093933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532147188476248483395955 11298220782714372725093933)
          ·
            refine ⟨4236832793517889771910225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11298220782714372725093933 4236832793517889771910225)
            ·
              refine ⟨3177624595138417328932669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236832793517889771910225 3177624595138417328932669)
              ·
                refine ⟨1191609223176906498349751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3177624595138417328932669 1191609223176906498349751)
                ·
                  refine ⟨1787413834765359747524627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191609223176906498349751 1787413834765359747524627)
                  ·
                    refine ⟨2681120752148039621286941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787413834765359747524627 2681120752148039621286941)
                    ·
                      refine ⟨1005420282055514857982603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681120752148039621286941 1005420282055514857982603)
                      ·
                        rfl

theorem cell23_1958049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1958049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958049 prefixEnd_1958049 := by exact prefixLift 1958049
  have htrace : WordTrace (prefixWord ++ tailWord_1958049) baseStart_1958049 baseEnd_1958049 := by
    simpa [prefixWord, tailWord_1958049, baseEnd_1958049] using wordTrace_append hprefix tailTrace_1958049
  have hstable : (prefixWord ++ tailWord_1958049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958049).length < 2 ^ (prefixWord ++ tailWord_1958049).sum := by decide
  have hdescent : baseEnd_1958049 < baseStart_1958049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958051 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1958051 : Nat := 118140960795 + 1958051 * 2 ^ 59
def prefixEnd_1958051 : Nat := 4983230072969 + 3 ^ 40 * 1958051 * 2
def baseEnd_1958051 : Nat := 1005421309016823850157593

theorem tailTrace_1958051 : CollatzResearch.WordTrace tailWord_1958051 prefixEnd_1958051 1005421309016823850157593 := by
  unfold tailWord_1958051
  simp only [CollatzResearch.WordTrace]
  refine ⟨71415987029323110332290007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47610658019548740221526671 71415987029323110332290007)
  ·
    refine ⟨107123980543984665498435011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71415987029323110332290007 107123980543984665498435011)
    ·
      refine ⟨160685970815976998247652517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107123980543984665498435011 160685970815976998247652517)
      ·
        refine ⟨30128619527995687171434847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160685970815976998247652517 30128619527995687171434847)
        ·
          refine ⟨45192929291993530757152271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30128619527995687171434847 45192929291993530757152271)
          ·
            refine ⟨67789393937990296135728407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45192929291993530757152271 67789393937990296135728407)
            ·
              refine ⟨101684090906985444203592611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67789393937990296135728407 101684090906985444203592611)
              ·
                refine ⟨152526136360478166305388917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101684090906985444203592611 152526136360478166305388917)
                ·
                  refine ⟨14299325283794828091130211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152526136360478166305388917 14299325283794828091130211)
                  ·
                    refine ⟨21448987925692242136695317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14299325283794828091130211 21448987925692242136695317)
                    ·
                      refine ⟨1005421309016823850157593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21448987925692242136695317 1005421309016823850157593)
                      ·
                        rfl

theorem cell23_1958051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1958051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958051 prefixEnd_1958051 := by exact prefixLift 1958051
  have htrace : WordTrace (prefixWord ++ tailWord_1958051) baseStart_1958051 baseEnd_1958051 := by
    simpa [prefixWord, tailWord_1958051, baseEnd_1958051] using wordTrace_append hprefix tailTrace_1958051
  have hstable : (prefixWord ++ tailWord_1958051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958051).length < 2 ^ (prefixWord ++ tailWord_1958051).sum := by decide
  have hdescent : baseEnd_1958051 < baseStart_1958051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958072 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_1958072 : Nat := 118140960795 + 1958072 * 2 ^ 59
def prefixEnd_1958072 : Nat := 4983230072969 + 3 ^ 40 * 1958072 * 2
def baseEnd_1958072 : Nat := 1005432092110568267994997

theorem tailTrace_1958072 : CollatzResearch.WordTrace tailWord_1958072 prefixEnd_1958072 1005432092110568267994997 := by
  unfold tailWord_1958072
  simp only [CollatzResearch.WordTrace]
  refine ⟨35708376481123515459402235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47611168641498020612536313 35708376481123515459402235)
  ·
    refine ⟨53562564721685273189103353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35708376481123515459402235 53562564721685273189103353)
    ·
      refine ⟨40171923541263954891827515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53562564721685273189103353 40171923541263954891827515)
      ·
        refine ⟨60257885311895932337741273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40171923541263954891827515 60257885311895932337741273)
        ·
          refine ⟨45193413983921949253305955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60257885311895932337741273 45193413983921949253305955)
          ·
            refine ⟨67790120975882923879958933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45193413983921949253305955 67790120975882923879958933)
            ·
              refine ⟨3177661920744512056873075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67790120975882923879958933 3177661920744512056873075)
              ·
                refine ⟨4766492881116768085309613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177661920744512056873075 4766492881116768085309613)
                ·
                  refine ⟨1787434830418788031991105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4766492881116768085309613 1787434830418788031991105)
                  ·
                    refine ⟨1340576122814091023993329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787434830418788031991105 1340576122814091023993329)
                    ·
                      refine ⟨1005432092110568267994997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340576122814091023993329 1005432092110568267994997)
                      ·
                        rfl

theorem cell23_1958072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_1958072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958072 prefixEnd_1958072 := by exact prefixLift 1958072
  have htrace : WordTrace (prefixWord ++ tailWord_1958072) baseStart_1958072 baseEnd_1958072 := by
    simpa [prefixWord, tailWord_1958072, baseEnd_1958072] using wordTrace_append hprefix tailTrace_1958072
  have hstable : (prefixWord ++ tailWord_1958072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958072).length < 2 ^ (prefixWord ++ tailWord_1958072).sum := by decide
  have hdescent : baseEnd_1958072 < baseStart_1958072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958105 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 3]
def baseStart_1958105 : Nat := 118140960795 + 1958105 * 2 ^ 59
def prefixEnd_1958105 : Nat := 4983230072969 + 3 ^ 40 * 1958105 * 2
def baseEnd_1958105 : Nat := 1005449036972166638882345

theorem tailTrace_1958105 : CollatzResearch.WordTrace tailWord_1958105 prefixEnd_1958105 1005449036972166638882345 := by
  unfold tailWord_1958105
  simp only [CollatzResearch.WordTrace]
  refine ⟨71417956571127477554755769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47611971047418318369837179 71417956571127477554755769)
  ·
    refine ⟨53563467428345608166066827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71417956571127477554755769 53563467428345608166066827)
    ·
      refine ⟨80345201142518412249100241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53563467428345608166066827 80345201142518412249100241)
      ·
        refine ⟨60258900856888809186825181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80345201142518412249100241 60258900856888809186825181)
        ·
          refine ⟨22597087821333303445059443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60258900856888809186825181 22597087821333303445059443)
          ·
            refine ⟨33895631731999955167589165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22597087821333303445059443 33895631731999955167589165)
            ·
              refine ⟨12710861899499983187845937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33895631731999955167589165 12710861899499983187845937)
              ·
                refine ⟨9533146424624987390884453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12710861899499983187845937 9533146424624987390884453)
                ·
                  refine ⟨1787464954617185135790835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9533146424624987390884453 1787464954617185135790835)
                  ·
                    refine ⟨2681197431925777703686253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787464954617185135790835 2681197431925777703686253)
                    ·
                      refine ⟨1005449036972166638882345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681197431925777703686253 1005449036972166638882345)
                      ·
                        rfl

theorem cell23_1958105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_1958105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958105 prefixEnd_1958105 := by exact prefixLift 1958105
  have htrace : WordTrace (prefixWord ++ tailWord_1958105) baseStart_1958105 baseEnd_1958105 := by
    simpa [prefixWord, tailWord_1958105, baseEnd_1958105] using wordTrace_append hprefix tailTrace_1958105
  have hstable : (prefixWord ++ tailWord_1958105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958105).length < 2 ^ (prefixWord ++ tailWord_1958105).sum := by decide
  have hdescent : baseEnd_1958105 < baseStart_1958105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958122 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1958122 : Nat := 118140960795 + 1958122 * 2 ^ 59
def prefixEnd_1958122 : Nat := 4983230072969 + 3 ^ 40 * 1958122 * 2
def baseEnd_1958122 : Nat := 1005457766143293072369767

theorem tailTrace_1958122 : CollatzResearch.WordTrace tailWord_1958122 prefixEnd_1958122 1005457766143293072369767 := by
  unfold tailWord_1958122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854644153016472364531155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47612384408043926305416413 17854644153016472364531155)
  ·
    refine ⟨26781966229524708546796733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17854644153016472364531155 26781966229524708546796733)
    ·
      refine ⟨10043237336071765705048775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26781966229524708546796733 10043237336071765705048775)
      ·
        refine ⟨15064856004107648557573163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043237336071765705048775 15064856004107648557573163)
        ·
          refine ⟨22597284006161472836359745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15064856004107648557573163 22597284006161472836359745)
          ·
            refine ⟨16947963004621104627269809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22597284006161472836359745 16947963004621104627269809)
            ·
              refine ⟨12710972253465828470452357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16947963004621104627269809 12710972253465828470452357)
              ·
                refine ⟨2383307297524842838209817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12710972253465828470452357 2383307297524842838209817)
                ·
                  refine ⟨1787480473143632128657363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383307297524842838209817 1787480473143632128657363)
                  ·
                    refine ⟨2681220709715448192986045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787480473143632128657363 2681220709715448192986045)
                    ·
                      refine ⟨1005457766143293072369767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681220709715448192986045 1005457766143293072369767)
                      ·
                        rfl

theorem cell23_1958122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1958122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958122 prefixEnd_1958122 := by exact prefixLift 1958122
  have htrace : WordTrace (prefixWord ++ tailWord_1958122) baseStart_1958122 baseEnd_1958122 := by
    simpa [prefixWord, tailWord_1958122, baseEnd_1958122] using wordTrace_append hprefix tailTrace_1958122
  have hstable : (prefixWord ++ tailWord_1958122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958122).length < 2 ^ (prefixWord ++ tailWord_1958122).sum := by decide
  have hdescent : baseEnd_1958122 < baseStart_1958122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958179 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 2, 2, 2]
def baseStart_1958179 : Nat := 118140960795 + 1958179 * 2 ^ 59
def prefixEnd_1958179 : Nat := 4983230072969 + 3 ^ 40 * 1958179 * 2
def baseEnd_1958179 : Nat := 1005487034540599349357005

theorem tailTrace_1958179 : CollatzResearch.WordTrace tailWord_1958179 prefixEnd_1958179 1005487034540599349357005 := by
  unfold tailWord_1958179
  simp only [CollatzResearch.WordTrace]
  refine ⟨71420655572859388192949591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47613770381906258795299727 71420655572859388192949591)
  ·
    refine ⟨107130983359289082289424387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71420655572859388192949591 107130983359289082289424387)
    ·
      refine ⟨160696475038933623434136581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107130983359289082289424387 160696475038933623434136581)
      ·
        refine ⟨30130589069800054393900609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160696475038933623434136581 30130589069800054393900609)
        ·
          refine ⟨22597941802350040795425457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30130589069800054393900609 22597941802350040795425457)
          ·
            refine ⟨16948456351762530596569093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22597941802350040795425457 16948456351762530596569093)
            ·
              refine ⟨3177835565955474486856705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16948456351762530596569093 3177835565955474486856705)
              ·
                refine ⟨2383376674466605865142529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177835565955474486856705 2383376674466605865142529)
                ·
                  refine ⟨1787532505849954398856897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383376674466605865142529 1787532505849954398856897)
                  ·
                    refine ⟨1340649379387465799142673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787532505849954398856897 1340649379387465799142673)
                    ·
                      refine ⟨1005487034540599349357005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340649379387465799142673 1005487034540599349357005)
                      ·
                        rfl

theorem cell23_1958179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_1958179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958179 prefixEnd_1958179 := by exact prefixLift 1958179
  have htrace : WordTrace (prefixWord ++ tailWord_1958179) baseStart_1958179 baseEnd_1958179 := by
    simpa [prefixWord, tailWord_1958179, baseEnd_1958179] using wordTrace_append hprefix tailTrace_1958179
  have hstable : (prefixWord ++ tailWord_1958179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958179).length < 2 ^ (prefixWord ++ tailWord_1958179).sum := by decide
  have hdescent : baseEnd_1958179 < baseStart_1958179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958195 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3]
def baseStart_1958195 : Nat := 118140960795 + 1958195 * 2 ^ 59
def prefixEnd_1958195 : Nat := 4983230072969 + 3 ^ 40 * 1958195 * 2
def baseEnd_1958195 : Nat := 1005495250231071286756931

theorem tailTrace_1958195 : CollatzResearch.WordTrace tailWord_1958195 prefixEnd_1958195 1005495250231071286756931 := by
  unfold tailWord_1958195
  simp only [CollatzResearch.WordTrace]
  refine ⟨71421239140801422925532039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47614159427200948617021359 71421239140801422925532039)
  ·
    refine ⟨107131858711202134388298059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71421239140801422925532039 107131858711202134388298059)
    ·
      refine ⟨160697788066803201582447089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107131858711202134388298059 160697788066803201582447089)
      ·
        refine ⟨120523341050102401186835317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160697788066803201582447089 120523341050102401186835317)
        ·
          refine ⟨11299063223447100111265811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120523341050102401186835317 11299063223447100111265811)
          ·
            refine ⟨16948594835170650166898717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299063223447100111265811 16948594835170650166898717)
            ·
              refine ⟨6355723063188993812587019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16948594835170650166898717 6355723063188993812587019)
              ·
                refine ⟨9533584594783490718880529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355723063188993812587019 9533584594783490718880529)
                ·
                  refine ⟨7150188446087618039160397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9533584594783490718880529 7150188446087618039160397)
                  ·
                    refine ⟨2681320667282856764685149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7150188446087618039160397 2681320667282856764685149)
                    ·
                      refine ⟨1005495250231071286756931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681320667282856764685149 1005495250231071286756931)
                      ·
                        rfl

theorem cell23_1958195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_1958195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958195 prefixEnd_1958195 := by exact prefixLift 1958195
  have htrace : WordTrace (prefixWord ++ tailWord_1958195) baseStart_1958195 baseEnd_1958195 := by
    simpa [prefixWord, tailWord_1958195, baseEnd_1958195] using wordTrace_append hprefix tailTrace_1958195
  have hstable : (prefixWord ++ tailWord_1958195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958195).length < 2 ^ (prefixWord ++ tailWord_1958195).sum := by decide
  have hdescent : baseEnd_1958195 < baseStart_1958195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958196 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_1958196 : Nat := 118140960795 + 1958196 * 2 ^ 59
def prefixEnd_1958196 : Nat := 4983230072969 + 3 ^ 40 * 1958196 * 2
def baseEnd_1958196 : Nat := 1005495763711725782844427

theorem tailTrace_1958196 : CollatzResearch.WordTrace tailWord_1958196 prefixEnd_1958196 1005495763711725782844427 := by
  unfold tailWord_1958196
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710637806898900048159221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47614183742531866730878961 35710637806898900048159221)
  ·
    refine ⟨3347872294396771879514927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35710637806898900048159221 3347872294396771879514927)
    ·
      refine ⟨5021808441595157819272391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347872294396771879514927 5021808441595157819272391)
      ·
        refine ⟨7532712662392736728908587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021808441595157819272391 7532712662392736728908587)
        ·
          refine ⟨11299068993589105093362881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532712662392736728908587 11299068993589105093362881)
          ·
            refine ⟨8474301745191828820022161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11299068993589105093362881 8474301745191828820022161)
            ·
              refine ⟨6355726308893871615016621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8474301745191828820022161 6355726308893871615016621)
              ·
                refine ⟨2383397365835201855631233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6355726308893871615016621 2383397365835201855631233)
                ·
                  refine ⟨1787548024376401391723425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383397365835201855631233 1787548024376401391723425)
                  ·
                    refine ⟨1340661018282301043792569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787548024376401391723425 1340661018282301043792569)
                    ·
                      refine ⟨1005495763711725782844427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340661018282301043792569 1005495763711725782844427)
                      ·
                        rfl

theorem cell23_1958196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_1958196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958196 prefixEnd_1958196 := by exact prefixLift 1958196
  have htrace : WordTrace (prefixWord ++ tailWord_1958196) baseStart_1958196 baseEnd_1958196 := by
    simpa [prefixWord, tailWord_1958196, baseEnd_1958196] using wordTrace_append hprefix tailTrace_1958196
  have hstable : (prefixWord ++ tailWord_1958196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958196).length < 2 ^ (prefixWord ++ tailWord_1958196).sum := by decide
  have hdescent : baseEnd_1958196 < baseStart_1958196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958208 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1958208 : Nat := 118140960795 + 1958208 * 2 ^ 59
def prefixEnd_1958208 : Nat := 4983230072969 + 3 ^ 40 * 1958208 * 2
def baseEnd_1958208 : Nat := 1005501925479579735894371

theorem tailTrace_1958208 : CollatzResearch.WordTrace tailWord_1958208 prefixEnd_1958208 1005501925479579735894371 := by
  unfold tailWord_1958208
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710856644877163072877639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47614475526502884097170185 35710856644877163072877639)
  ·
    refine ⟨53566284967315744609316459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35710856644877163072877639 53566284967315744609316459)
    ·
      refine ⟨80349427450973616913974689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53566284967315744609316459 80349427450973616913974689)
      ·
        refine ⟨60262070588230212685481017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80349427450973616913974689 60262070588230212685481017)
        ·
          refine ⟨45196552941172659514110763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60262070588230212685481017 45196552941172659514110763)
          ·
            refine ⟨67794829411758989271166145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45196552941172659514110763 67794829411758989271166145)
            ·
              refine ⟨50846122058819241953374609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67794829411758989271166145 50846122058819241953374609)
              ·
                refine ⟨38134591544114431465030957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50846122058819241953374609 38134591544114431465030957)
                ·
                  refine ⟨14300471829042911799386609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38134591544114431465030957 14300471829042911799386609)
                  ·
                    refine ⟨10725353871782183849539957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14300471829042911799386609 10725353871782183849539957)
                    ·
                      refine ⟨1005501925479579735894371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10725353871782183849539957 1005501925479579735894371)
                      ·
                        rfl

theorem cell23_1958208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1958208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958208 prefixEnd_1958208 := by exact prefixLift 1958208
  have htrace : WordTrace (prefixWord ++ tailWord_1958208) baseStart_1958208 baseEnd_1958208 := by
    simpa [prefixWord, tailWord_1958208, baseEnd_1958208] using wordTrace_append hprefix tailTrace_1958208
  have hstable : (prefixWord ++ tailWord_1958208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958208).length < 2 ^ (prefixWord ++ tailWord_1958208).sum := by decide
  have hdescent : baseEnd_1958208 < baseStart_1958208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958255 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_1958255 : Nat := 118140960795 + 1958255 * 2 ^ 59
def prefixEnd_1958255 : Nat := 4983230072969 + 3 ^ 40 * 1958255 * 2
def baseEnd_1958255 : Nat := 1005526059070341052006655

theorem tailTrace_1958255 : CollatzResearch.WordTrace tailWord_1958255 prefixEnd_1958255 1005526059070341052006655 := by
  unfold tailWord_1958255
  simp only [CollatzResearch.WordTrace]
  refine ⟨71423427520584053172716219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47615618347056035448477479 71423427520584053172716219)
  ·
    refine ⟨107135141280876079759074329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71423427520584053172716219 107135141280876079759074329)
    ·
      refine ⟨80351355960657059819305747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107135141280876079759074329 80351355960657059819305747)
      ·
        refine ⟨120527033940985589728958621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80351355960657059819305747 120527033940985589728958621)
        ·
          refine ⟨45197637727869596148359483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120527033940985589728958621 45197637727869596148359483)
          ·
            refine ⟨67796456591804394222539225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45197637727869596148359483 67796456591804394222539225)
            ·
              refine ⟨50847342443853295666904419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67796456591804394222539225 50847342443853295666904419)
              ·
                refine ⟨76271013665779943500356629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50847342443853295666904419 76271013665779943500356629)
                ·
                  refine ⟨3575203765583434851579217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76271013665779943500356629 3575203765583434851579217)
                  ·
                    refine ⟨2681402824187576138684413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575203765583434851579217 2681402824187576138684413)
                    ·
                      refine ⟨1005526059070341052006655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681402824187576138684413 1005526059070341052006655)
                      ·
                        rfl

theorem cell23_1958255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_1958255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958255 prefixEnd_1958255 := by exact prefixLift 1958255
  have htrace : WordTrace (prefixWord ++ tailWord_1958255) baseStart_1958255 baseEnd_1958255 := by
    simpa [prefixWord, tailWord_1958255, baseEnd_1958255] using wordTrace_append hprefix tailTrace_1958255
  have hstable : (prefixWord ++ tailWord_1958255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958255).length < 2 ^ (prefixWord ++ tailWord_1958255).sum := by decide
  have hdescent : baseEnd_1958255 < baseStart_1958255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958329 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 2, 3, 2]
def baseStart_1958329 : Nat := 118140960795 + 1958329 * 2 ^ 59
def prefixEnd_1958329 : Nat := 4983230072969 + 3 ^ 40 * 1958329 * 2
def baseEnd_1958329 : Nat := 1005564056638773762481315

theorem tailTrace_1958329 : CollatzResearch.WordTrace tailWord_1958329 prefixEnd_1958329 1005564056638773762481315 := by
  unfold tailWord_1958329
  simp only [CollatzResearch.WordTrace]
  refine ⟨71426126522315963810910041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47617417681543975873940027 71426126522315963810910041)
  ·
    refine ⟨53569594891736972858182531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71426126522315963810910041 53569594891736972858182531)
    ·
      refine ⟨80354392337605459287273797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53569594891736972858182531 80354392337605459287273797)
      ·
        refine ⟨15066448563301023616363837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80354392337605459287273797 15066448563301023616363837)
        ·
          refine ⟨5649918211237883856136439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15066448563301023616363837 5649918211237883856136439)
          ·
            refine ⟨8474877316856825784204659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649918211237883856136439 8474877316856825784204659)
            ·
              refine ⟨12712315975285238676306989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474877316856825784204659 12712315975285238676306989)
              ·
                refine ⟨4767118490731964503615121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12712315975285238676306989 4767118490731964503615121)
                ·
                  refine ⟨3575338868048973377711341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4767118490731964503615121 3575338868048973377711341)
                  ·
                    refine ⟨1340752075518365016641753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575338868048973377711341 1340752075518365016641753)
                    ·
                      refine ⟨1005564056638773762481315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340752075518365016641753 1005564056638773762481315)
                      ·
                        rfl

theorem cell23_1958329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_1958329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958329 prefixEnd_1958329 := by exact prefixLift 1958329
  have htrace : WordTrace (prefixWord ++ tailWord_1958329) baseStart_1958329 baseEnd_1958329 := by
    simpa [prefixWord, tailWord_1958329, baseEnd_1958329] using wordTrace_append hprefix tailTrace_1958329
  have hstable : (prefixWord ++ tailWord_1958329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958329).length < 2 ^ (prefixWord ++ tailWord_1958329).sum := by decide
  have hdescent : baseEnd_1958329 < baseStart_1958329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958362 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1958362 : Nat := 118140960795 + 1958362 * 2 ^ 59
def prefixEnd_1958362 : Nat := 4983230072969 + 3 ^ 40 * 1958362 * 2
def baseEnd_1958362 : Nat := 1005581001500372133368663

theorem tailTrace_1958362 : CollatzResearch.WordTrace tailWord_1958362 prefixEnd_1958362 1005581001500372133368663 := by
  unfold tailWord_1958362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856832532799102611715335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47618220087464273631240893 17856832532799102611715335)
  ·
    refine ⟨26785248799198653917573003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856832532799102611715335 26785248799198653917573003)
    ·
      refine ⟨40177873198797980876359505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26785248799198653917573003 40177873198797980876359505)
      ·
        refine ⟨30133404899098485657269629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40177873198797980876359505 30133404899098485657269629)
        ·
          refine ⟨11300026837161932121476111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30133404899098485657269629 11300026837161932121476111)
          ·
            refine ⟨16950040255742898182214167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11300026837161932121476111 16950040255742898182214167)
            ·
              refine ⟨25425060383614347273321251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16950040255742898182214167 25425060383614347273321251)
              ·
                refine ⟨38137590575421520909981877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25425060383614347273321251 38137590575421520909981877)
                ·
                  refine ⟨3575399116445767585310801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38137590575421520909981877 3575399116445767585310801)
                  ·
                    refine ⟨2681549337334325688983101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575399116445767585310801 2681549337334325688983101)
                    ·
                      refine ⟨1005581001500372133368663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681549337334325688983101 1005581001500372133368663)
                      ·
                        rfl

theorem cell23_1958362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1958362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958362 prefixEnd_1958362 := by exact prefixLift 1958362
  have htrace : WordTrace (prefixWord ++ tailWord_1958362) baseStart_1958362 baseEnd_1958362 := by
    simpa [prefixWord, tailWord_1958362, baseEnd_1958362] using wordTrace_append hprefix tailTrace_1958362
  have hstable : (prefixWord ++ tailWord_1958362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958362).length < 2 ^ (prefixWord ++ tailWord_1958362).sum := by decide
  have hdescent : baseEnd_1958362 < baseStart_1958362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958376 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1958376 : Nat := 118140960795 + 1958376 * 2 ^ 59
def prefixEnd_1958376 : Nat := 4983230072969 + 3 ^ 40 * 1958376 * 2
def baseEnd_1958376 : Nat := 1005588190229535078593599

theorem tailTrace_1958376 : CollatzResearch.WordTrace tailWord_1958376 prefixEnd_1958376 1005588190229535078593599 := by
  unfold tailWord_1958376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35713920376572845418935491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47618560502097127225247321 35713920376572845418935491)
  ·
    refine ⟨53570880564859268128403237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35713920376572845418935491 53570880564859268128403237)
    ·
      refine ⟨10044540105911112774075607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53570880564859268128403237 10044540105911112774075607)
      ·
        refine ⟨15066810158866669161113411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044540105911112774075607 15066810158866669161113411)
        ·
          refine ⟨22600215238300003741670117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066810158866669161113411 22600215238300003741670117)
          ·
            refine ⟨4237540357181250701563147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22600215238300003741670117 4237540357181250701563147)
            ·
              refine ⟨6356310535771876052344721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237540357181250701563147 6356310535771876052344721)
              ·
                refine ⟨4767232901828907039258541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6356310535771876052344721 4767232901828907039258541)
                ·
                  refine ⟨1787712338185840139721953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4767232901828907039258541 1787712338185840139721953)
                  ·
                    refine ⟨1340784253639380104791465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787712338185840139721953 1340784253639380104791465)
                    ·
                      refine ⟨1005588190229535078593599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340784253639380104791465 1005588190229535078593599)
                      ·
                        rfl

theorem cell23_1958376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1958376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958376 prefixEnd_1958376 := by exact prefixLift 1958376
  have htrace : WordTrace (prefixWord ++ tailWord_1958376) baseStart_1958376 baseEnd_1958376 := by
    simpa [prefixWord, tailWord_1958376, baseEnd_1958376] using wordTrace_append hprefix tailTrace_1958376
  have hstable : (prefixWord ++ tailWord_1958376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958376).length < 2 ^ (prefixWord ++ tailWord_1958376).sum := by decide
  have hdescent : baseEnd_1958376 < baseStart_1958376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958392 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1958392 : Nat := 118140960795 + 1958392 * 2 ^ 59
def prefixEnd_1958392 : Nat := 4983230072969 + 3 ^ 40 * 1958392 * 2
def baseEnd_1958392 : Nat := 1005596405920007015993525

theorem tailTrace_1958392 : CollatzResearch.WordTrace tailWord_1958392 prefixEnd_1958392 1005596405920007015993525 := by
  unfold tailWord_1958392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35714212160543862785226715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47618949547391817046968953 35714212160543862785226715)
  ·
    refine ⟨53571318240815794177840073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35714212160543862785226715 53571318240815794177840073)
    ·
      refine ⟨40178488680611845633380055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53571318240815794177840073 40178488680611845633380055)
      ·
        refine ⟨60267733020917768450070083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40178488680611845633380055 60267733020917768450070083)
        ·
          refine ⟨90401599531376652675105125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60267733020917768450070083 90401599531376652675105125)
          ·
            refine ⟨16950299912133122376582211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90401599531376652675105125 16950299912133122376582211)
            ·
              refine ⟨25425449868199683564873317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16950299912133122376582211 25425449868199683564873317)
              ·
                refine ⟨4767271850287440668413747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25425449868199683564873317 4767271850287440668413747)
                ·
                  refine ⟨7150907775431161002620621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767271850287440668413747 7150907775431161002620621)
                  ·
                    refine ⟨2681590415786685375982733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7150907775431161002620621 2681590415786685375982733)
                    ·
                      refine ⟨1005596405920007015993525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681590415786685375982733 1005596405920007015993525)
                      ·
                        rfl

theorem cell23_1958392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1958392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958392 prefixEnd_1958392 := by exact prefixLift 1958392
  have htrace : WordTrace (prefixWord ++ tailWord_1958392) baseStart_1958392 baseEnd_1958392 := by
    simpa [prefixWord, tailWord_1958392, baseEnd_1958392] using wordTrace_append hprefix tailTrace_1958392
  have hstable : (prefixWord ++ tailWord_1958392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958392).length < 2 ^ (prefixWord ++ tailWord_1958392).sum := by decide
  have hdescent : baseEnd_1958392 < baseStart_1958392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958409 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 3]
def baseStart_1958409 : Nat := 118140960795 + 1958409 * 2 ^ 59
def prefixEnd_1958409 : Nat := 4983230072969 + 3 ^ 40 * 1958409 * 2
def baseEnd_1958409 : Nat := 1005605135091133449480947

theorem tailTrace_1958409 : CollatzResearch.WordTrace tailWord_1958409 prefixEnd_1958409 1005605135091133449480947 := by
  unfold tailWord_1958409
  simp only [CollatzResearch.WordTrace]
  refine ⟨71429044362026137473822281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47619362908017424982548187 71429044362026137473822281)
  ·
    refine ⟨53571783271519603105366711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71429044362026137473822281 53571783271519603105366711)
    ·
      refine ⟨80357674907279404658050067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53571783271519603105366711 80357674907279404658050067)
      ·
        refine ⟨120536512360919106987075101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80357674907279404658050067 120536512360919106987075101)
        ·
          refine ⟨45201192135344665120153163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120536512360919106987075101 45201192135344665120153163)
          ·
            refine ⟨67801788203016997680229745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45201192135344665120153163 67801788203016997680229745)
            ·
              refine ⟨50851341152262748260172309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67801788203016997680229745 50851341152262748260172309)
              ·
                refine ⟨2383656616512316324695577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50851341152262748260172309 2383656616512316324695577)
                ·
                  refine ⟨1787742462384237243521683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383656616512316324695577 1787742462384237243521683)
                  ·
                    refine ⟨2681613693576355865282525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787742462384237243521683 2681613693576355865282525)
                    ·
                      refine ⟨1005605135091133449480947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681613693576355865282525 1005605135091133449480947)
                      ·
                        rfl

theorem cell23_1958409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_1958409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958409 prefixEnd_1958409 := by exact prefixLift 1958409
  have htrace : WordTrace (prefixWord ++ tailWord_1958409) baseStart_1958409 baseEnd_1958409 := by
    simpa [prefixWord, tailWord_1958409, baseEnd_1958409] using wordTrace_append hprefix tailTrace_1958409
  have hstable : (prefixWord ++ tailWord_1958409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958409).length < 2 ^ (prefixWord ++ tailWord_1958409).sum := by decide
  have hdescent : baseEnd_1958409 < baseStart_1958409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958423 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1958423 : Nat := 118140960795 + 1958423 * 2 ^ 59
def prefixEnd_1958423 : Nat := 4983230072969 + 3 ^ 40 * 1958423 * 2
def baseEnd_1958423 : Nat := 1005612323820296394705883

theorem tailTrace_1958423 : CollatzResearch.WordTrace tailWord_1958423 prefixEnd_1958423 1005612323820296394705883 := by
  unfold tailWord_1958423
  simp only [CollatzResearch.WordTrace]
  refine ⟨71429554983975417864831923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47619703322650278576554615 71429554983975417864831923)
  ·
    refine ⟨107144332475963126797247885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71429554983975417864831923 107144332475963126797247885)
    ·
      refine ⟨40179124678486172548967957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107144332475963126797247885 40179124678486172548967957)
      ·
        refine ⟨1883396469304039338232873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40179124678486172548967957 1883396469304039338232873)
        ·
          refine ⟨1412547351978029503674655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883396469304039338232873 1412547351978029503674655)
          ·
            refine ⟨2118821027967044255511983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412547351978029503674655 2118821027967044255511983)
            ·
              refine ⟨3178231541950566383267975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118821027967044255511983 3178231541950566383267975)
              ·
                refine ⟨4767347312925849574901963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178231541950566383267975 4767347312925849574901963)
                ·
                  refine ⟨7151020969388774362352945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767347312925849574901963 7151020969388774362352945)
                  ·
                    refine ⟨5363265727041580771764709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151020969388774362352945 5363265727041580771764709)
                    ·
                      refine ⟨1005612323820296394705883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5363265727041580771764709 1005612323820296394705883)
                      ·
                        rfl

theorem cell23_1958423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1958423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958423 prefixEnd_1958423 := by exact prefixLift 1958423
  have htrace : WordTrace (prefixWord ++ tailWord_1958423) baseStart_1958423 baseEnd_1958423 := by
    simpa [prefixWord, tailWord_1958423, baseEnd_1958423] using wordTrace_append hprefix tailTrace_1958423
  have hstable : (prefixWord ++ tailWord_1958423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958423).length < 2 ^ (prefixWord ++ tailWord_1958423).sum := by decide
  have hdescent : baseEnd_1958423 < baseStart_1958423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958449 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_1958449 : Nat := 118140960795 + 1958449 * 2 ^ 59
def prefixEnd_1958449 : Nat := 4983230072969 + 3 ^ 40 * 1958449 * 2
def baseEnd_1958449 : Nat := 1005625674317313292980763

theorem tailTrace_1958449 : CollatzResearch.WordTrace tailWord_1958449 prefixEnd_1958449 1005625674317313292980763 := by
  unfold tailWord_1958449
  simp only [CollatzResearch.WordTrace]
  refine ⟨71430503281881224305278401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47620335521254149536852267 71430503281881224305278401)
  ·
    refine ⟨53572877461410918228958801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71430503281881224305278401 53572877461410918228958801)
    ·
      refine ⟨40179658096058188671719101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53572877461410918228958801 40179658096058188671719101)
      ·
        refine ⟨15067371786021820751894663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40179658096058188671719101 15067371786021820751894663)
        ·
          refine ⟨22601057679032731127841995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067371786021820751894663 22601057679032731127841995)
          ·
            refine ⟨33901586518549096691762993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22601057679032731127841995 33901586518549096691762993)
            ·
              refine ⟨25426189888911822518822245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33901586518549096691762993 25426189888911822518822245)
              ·
                refine ⟨4767410604170966722279171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25426189888911822518822245 4767410604170966722279171)
                ·
                  refine ⟨7151115906256450083418757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767410604170966722279171 7151115906256450083418757)
                  ·
                    refine ⟨1340834232423084390641017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151115906256450083418757 1340834232423084390641017)
                    ·
                      refine ⟨1005625674317313292980763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340834232423084390641017 1005625674317313292980763)
                      ·
                        rfl

theorem cell23_1958449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_1958449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958449 prefixEnd_1958449 := by exact prefixLift 1958449
  have htrace : WordTrace (prefixWord ++ tailWord_1958449) baseStart_1958449 baseEnd_1958449 := by
    simpa [prefixWord, tailWord_1958449, baseEnd_1958449] using wordTrace_append hprefix tailTrace_1958449
  have hstable : (prefixWord ++ tailWord_1958449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958449).length < 2 ^ (prefixWord ++ tailWord_1958449).sum := by decide
  have hdescent : baseEnd_1958449 < baseStart_1958449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958530 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1958530 : Nat := 118140960795 + 1958530 * 2 ^ 59
def prefixEnd_1958530 : Nat := 4983230072969 + 3 ^ 40 * 1958530 * 2
def baseEnd_1958530 : Nat := 1005667266250327476067891

theorem tailTrace_1958530 : CollatzResearch.WordTrace tailWord_1958530 prefixEnd_1958530 1005667266250327476067891 := by
  unfold tailWord_1958530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858364398646943784744261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47622305063058516759318029 17858364398646943784744261)
  ·
    refine ⟨3348443324746301959639549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17858364398646943784744261 3348443324746301959639549)
    ·
      refine ⟨1255666246779863234864831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3348443324746301959639549 1255666246779863234864831)
      ·
        refine ⟨1883499370169794852297247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255666246779863234864831 1883499370169794852297247)
        ·
          refine ⟨2825249055254692278445871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883499370169794852297247 2825249055254692278445871)
          ·
            refine ⟨4237873582882038417668807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825249055254692278445871 4237873582882038417668807)
            ·
              refine ⟨6356810374323057626503211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237873582882038417668807 6356810374323057626503211)
              ·
                refine ⟨9535215561484586439754817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356810374323057626503211 9535215561484586439754817)
                ·
                  refine ⟨7151411671113439829816113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535215561484586439754817 7151411671113439829816113)
                  ·
                    refine ⟨5363558753335079872362085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151411671113439829816113 5363558753335079872362085)
                    ·
                      refine ⟨1005667266250327476067891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5363558753335079872362085 1005667266250327476067891)
                      ·
                        rfl

theorem cell23_1958530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1958530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958530 prefixEnd_1958530 := by exact prefixLift 1958530
  have htrace : WordTrace (prefixWord ++ tailWord_1958530) baseStart_1958530 baseEnd_1958530 := by
    simpa [prefixWord, tailWord_1958530, baseEnd_1958530] using wordTrace_append hprefix tailTrace_1958530
  have hstable : (prefixWord ++ tailWord_1958530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958530).length < 2 ^ (prefixWord ++ tailWord_1958530).sum := by decide
  have hdescent : baseEnd_1958530 < baseStart_1958530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958556 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1958556 : Nat := 118140960795 + 1958556 * 2 ^ 59
def prefixEnd_1958556 : Nat := 4983230072969 + 3 ^ 40 * 1958556 * 2
def baseEnd_1958556 : Nat := 1005680616747344374342771

theorem tailTrace_1958556 : CollatzResearch.WordTrace tailWord_1958556 prefixEnd_1958556 1005680616747344374342771 := by
  unfold tailWord_1958556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35717202946246790789711761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47622937261662387719615681 35717202946246790789711761)
  ·
    refine ⟨26787902209685093092283821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35717202946246790789711761 26787902209685093092283821)
    ·
      refine ⟨10045463328631909909606433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26787902209685093092283821 10045463328631909909606433)
      ·
        refine ⟨7534097496473932432204825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10045463328631909909606433 7534097496473932432204825)
        ·
          refine ⟨5650573122355449324153619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7534097496473932432204825 5650573122355449324153619)
          ·
            refine ⟨8475859683533173986230429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650573122355449324153619 8475859683533173986230429)
            ·
              refine ⟨3178447381324940244836411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8475859683533173986230429 3178447381324940244836411)
              ·
                refine ⟨4767671071987410367254617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178447381324940244836411 4767671071987410367254617)
                ·
                  refine ⟨3575753303990557775440963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4767671071987410367254617 3575753303990557775440963)
                  ·
                    refine ⟨5363629955985836663161445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575753303990557775440963 5363629955985836663161445)
                    ·
                      refine ⟨1005680616747344374342771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5363629955985836663161445 1005680616747344374342771)
                      ·
                        rfl

theorem cell23_1958556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1958556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958556 prefixEnd_1958556 := by exact prefixLift 1958556
  have htrace : WordTrace (prefixWord ++ tailWord_1958556) baseStart_1958556 baseEnd_1958556 := by
    simpa [prefixWord, tailWord_1958556, baseEnd_1958556] using wordTrace_append hprefix tailTrace_1958556
  have hstable : (prefixWord ++ tailWord_1958556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958556).length < 2 ^ (prefixWord ++ tailWord_1958556).sum := by decide
  have hdescent : baseEnd_1958556 < baseStart_1958556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958579 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 6]
def baseStart_1958579 : Nat := 118140960795 + 1958579 * 2 ^ 59
def prefixEnd_1958579 : Nat := 4983230072969 + 3 ^ 40 * 1958579 * 2
def baseEnd_1958579 : Nat := 111743602978044198261685

theorem tailTrace_1958579 : CollatzResearch.WordTrace tailWord_1958579 prefixEnd_1958579 111743602978044198261685 := by
  unfold tailWord_1958579
  simp only [CollatzResearch.WordTrace]
  refine ⟨71435244771410256507510791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47623496514273504338340527 71435244771410256507510791)
  ·
    refine ⟨107152867157115384761266187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71435244771410256507510791 107152867157115384761266187)
    ·
      refine ⟨160729300735673077141899281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107152867157115384761266187 160729300735673077141899281)
      ·
        refine ⟨120546975551754807856424461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160729300735673077141899281 120546975551754807856424461)
        ·
          refine ⟨45205115831908052946159173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120546975551754807856424461 45205115831908052946159173)
          ·
            refine ⟨8475959218482759927404845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45205115831908052946159173 8475959218482759927404845)
            ·
              refine ⟨3178484706931034972776817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8475959218482759927404845 3178484706931034972776817)
              ·
                refine ⟨2383863530198276229582613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178484706931034972776817 2383863530198276229582613)
                ·
                  refine ⟨111743602978044198261685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2383863530198276229582613 111743602978044198261685)
                  ·
                    rfl

theorem cell23_1958579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 6].length) (baseStart_1958579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958579 prefixEnd_1958579 := by exact prefixLift 1958579
  have htrace : WordTrace (prefixWord ++ tailWord_1958579) baseStart_1958579 baseEnd_1958579 := by
    simpa [prefixWord, tailWord_1958579, baseEnd_1958579] using wordTrace_append hprefix tailTrace_1958579
  have hstable : (prefixWord ++ tailWord_1958579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958579).length < 2 ^ (prefixWord ++ tailWord_1958579).sum := by decide
  have hdescent : baseEnd_1958579 < baseStart_1958579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958616 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_1958616 : Nat := 118140960795 + 1958616 * 2 ^ 59
def prefixEnd_1958616 : Nat := 4983230072969 + 3 ^ 40 * 1958616 * 2
def baseEnd_1958616 : Nat := 1005711425586614139592495

theorem tailTrace_1958616 : CollatzResearch.WordTrace tailWord_1958616 prefixEnd_1958616 1005711425586614139592495 := by
  unfold tailWord_1958616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35718297136138105913303851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47624396181517474551071801 35718297136138105913303851)
  ·
    refine ⟨53577445704207158869955777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35718297136138105913303851 53577445704207158869955777)
    ·
      refine ⟨40183084278155369152466833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53577445704207158869955777 40183084278155369152466833)
      ·
        refine ⟨30137313208616526864350125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40183084278155369152466833 30137313208616526864350125)
        ·
          refine ⟨11301492453231197574131297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30137313208616526864350125 11301492453231197574131297)
          ·
            refine ⟨8476119339923398180598473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11301492453231197574131297 8476119339923398180598473)
            ·
              refine ⟨6357089504942548635448855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476119339923398180598473 6357089504942548635448855)
              ·
                refine ⟨9535634257413822953173283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357089504942548635448855 9535634257413822953173283)
                ·
                  refine ⟨14303451386120734429759925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9535634257413822953173283 14303451386120734429759925)
                  ·
                    refine ⟨1340948567448818852789993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14303451386120734429759925 1340948567448818852789993)
                    ·
                      refine ⟨1005711425586614139592495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340948567448818852789993 1005711425586614139592495)
                      ·
                        rfl

theorem cell23_1958616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_1958616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958616 prefixEnd_1958616 := by exact prefixLift 1958616
  have htrace : WordTrace (prefixWord ++ tailWord_1958616) baseStart_1958616 baseEnd_1958616 := by
    simpa [prefixWord, tailWord_1958616, baseEnd_1958616] using wordTrace_append hprefix tailTrace_1958616
  have hstable : (prefixWord ++ tailWord_1958616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958616).length < 2 ^ (prefixWord ++ tailWord_1958616).sum := by decide
  have hdescent : baseEnd_1958616 < baseStart_1958616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958640 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 1, 1, 3]
def baseStart_1958640 : Nat := 118140960795 + 1958640 * 2 ^ 59
def prefixEnd_1958640 : Nat := 4983230072969 + 3 ^ 40 * 1958640 * 2
def baseEnd_1958640 : Nat := 1005723749122322045692385

theorem tailTrace_1958640 : CollatzResearch.WordTrace tailWord_1958640 prefixEnd_1958640 1005723749122322045692385 := by
  unfold tailWord_1958640
  simp only [CollatzResearch.WordTrace]
  refine ⟨35718734812094631962740687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47624979749459509283654249 35718734812094631962740687)
  ·
    refine ⟨53578102218141947944111031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35718734812094631962740687 53578102218141947944111031)
    ·
      refine ⟨80367153327212921916166547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53578102218141947944111031 80367153327212921916166547)
      ·
        refine ⟨120550729990819382874249821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80367153327212921916166547 120550729990819382874249821)
        ·
          refine ⟨45206523746557268577843683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120550729990819382874249821 45206523746557268577843683)
          ·
            refine ⟨67809785619835902866765525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45206523746557268577843683 67809785619835902866765525)
            ·
              refine ⟨1589291850464903973439817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67809785619835902866765525 1589291850464903973439817)
              ·
                refine ⟨1191968887848677980079863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589291850464903973439817 1191968887848677980079863)
                ·
                  refine ⟨1787953331773016970119795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191968887848677980079863 1787953331773016970119795)
                  ·
                    refine ⟨2681929997659525455179693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1787953331773016970119795 2681929997659525455179693)
                    ·
                      refine ⟨1005723749122322045692385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681929997659525455179693 1005723749122322045692385)
                      ·
                        rfl

theorem cell23_1958640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 1, 3].length) (baseStart_1958640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958640 prefixEnd_1958640 := by exact prefixLift 1958640
  have htrace : WordTrace (prefixWord ++ tailWord_1958640) baseStart_1958640 baseEnd_1958640 := by
    simpa [prefixWord, tailWord_1958640, baseEnd_1958640] using wordTrace_append hprefix tailTrace_1958640
  have hstable : (prefixWord ++ tailWord_1958640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958640).length < 2 ^ (prefixWord ++ tailWord_1958640).sum := by decide
  have hdescent : baseEnd_1958640 < baseStart_1958640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958646 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1958646 : Nat := 118140960795 + 1958646 * 2 ^ 59
def prefixEnd_1958646 : Nat := 4983230072969 + 3 ^ 40 * 1958646 * 2
def baseEnd_1958646 : Nat := 1005726830006249022217357

theorem tailTrace_1958646 : CollatzResearch.WordTrace tailWord_1958646 prefixEnd_1958646 1005726830006249022217357 := by
  unfold tailWord_1958646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464855528885470434387487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47625125641445017966799861 4464855528885470434387487)
  ·
    refine ⟨6697283293328205651581231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464855528885470434387487 6697283293328205651581231)
    ·
      refine ⟨10045924939992308477371847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6697283293328205651581231 10045924939992308477371847)
      ·
        refine ⟨15068887409988462716057771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10045924939992308477371847 15068887409988462716057771)
        ·
          refine ⟨22603331114982694074086657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15068887409988462716057771 22603331114982694074086657)
          ·
            refine ⟨16952498336237020555564993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22603331114982694074086657 16952498336237020555564993)
            ·
              refine ⟨12714373752177765416673745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16952498336237020555564993 12714373752177765416673745)
              ·
                refine ⟨9535780314133324062505309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12714373752177765416673745 9535780314133324062505309)
                ·
                  refine ⟨3575917617799996523439491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9535780314133324062505309 3575917617799996523439491)
                  ·
                    refine ⟨5363876426699994785159237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575917617799996523439491 5363876426699994785159237)
                    ·
                      refine ⟨1005726830006249022217357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5363876426699994785159237 1005726830006249022217357)
                      ·
                        rfl

theorem cell23_1958646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1958646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958646 prefixEnd_1958646 := by exact prefixLift 1958646
  have htrace : WordTrace (prefixWord ++ tailWord_1958646) baseStart_1958646 baseEnd_1958646 := by
    simpa [prefixWord, tailWord_1958646, baseEnd_1958646] using wordTrace_append hprefix tailTrace_1958646
  have hstable : (prefixWord ++ tailWord_1958646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958646).length < 2 ^ (prefixWord ++ tailWord_1958646).sum := by decide
  have hdescent : baseEnd_1958646 < baseStart_1958646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958659 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4]
def baseStart_1958659 : Nat := 118140960795 + 1958659 * 2 ^ 59
def prefixEnd_1958659 : Nat := 4983230072969 + 3 ^ 40 * 1958659 * 2
def baseEnd_1958659 : Nat := 1005733505254757471354797

theorem tailTrace_1958659 : CollatzResearch.WordTrace tailWord_1958659 prefixEnd_1958659 1005733505254757471354797 := by
  unfold tailWord_1958659
  simp only [CollatzResearch.WordTrace]
  refine ⟨71438162611120430170423031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47625441740746953446948687 71438162611120430170423031)
  ·
    refine ⟨107157243916680645255634547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71438162611120430170423031 107157243916680645255634547)
    ·
      refine ⟨160735865875020967883451821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107157243916680645255634547 160735865875020967883451821)
      ·
        refine ⟨60275949703132862956294433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160735865875020967883451821 60275949703132862956294433)
        ·
          refine ⟨45206962277349647217220825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60275949703132862956294433 45206962277349647217220825)
          ·
            refine ⟨33905221708012235412915619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45206962277349647217220825 33905221708012235412915619)
            ·
              refine ⟨50857832562018353119373429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33905221708012235412915619 50857832562018353119373429)
              ·
                refine ⟨4767921802689220604941259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50857832562018353119373429 4767921802689220604941259)
                ·
                  refine ⟨7151882704033830907411889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767921802689220604941259 7151882704033830907411889)
                  ·
                    refine ⟨5363912028025373180558917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151882704033830907411889 5363912028025373180558917)
                    ·
                      refine ⟨1005733505254757471354797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5363912028025373180558917 1005733505254757471354797)
                      ·
                        rfl

theorem cell23_1958659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_1958659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958659 prefixEnd_1958659 := by exact prefixLift 1958659
  have htrace : WordTrace (prefixWord ++ tailWord_1958659) baseStart_1958659 baseEnd_1958659 := by
    simpa [prefixWord, tailWord_1958659, baseEnd_1958659] using wordTrace_append hprefix tailTrace_1958659
  have hstable : (prefixWord ++ tailWord_1958659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958659).length < 2 ^ (prefixWord ++ tailWord_1958659).sum := by decide
  have hdescent : baseEnd_1958659 < baseStart_1958659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958663 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1958663 : Nat := 118140960795 + 1958663 * 2 ^ 59
def prefixEnd_1958663 : Nat := 4983230072969 + 3 ^ 40 * 1958663 * 2
def baseEnd_1958663 : Nat := 1005735559177375455704779

theorem tailTrace_1958663 : CollatzResearch.WordTrace tailWord_1958663 prefixEnd_1958663 1005735559177375455704779 := by
  unfold tailWord_1958663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71438308503105938853568643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47625539002070625902379095 71438308503105938853568643)
  ·
    refine ⟨107157462754658908280352965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71438308503105938853568643 107157462754658908280352965)
    ·
      refine ⟨20092024266498545302566181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107157462754658908280352965 20092024266498545302566181)
      ·
        refine ⟨3767254549968477244231159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20092024266498545302566181 3767254549968477244231159)
        ·
          refine ⟨5650881824952715866346739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767254549968477244231159 5650881824952715866346739)
          ·
            refine ⟨8476322737429073799520109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650881824952715866346739 8476322737429073799520109)
            ·
              refine ⟨3178621026535902674820041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8476322737429073799520109 3178621026535902674820041)
              ·
                refine ⟨2383965769901927006115031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178621026535902674820041 2383965769901927006115031)
                ·
                  refine ⟨3575948654852890509172547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383965769901927006115031 3575948654852890509172547)
                  ·
                    refine ⟨5363922982279335763758821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575948654852890509172547 5363922982279335763758821)
                    ·
                      refine ⟨1005735559177375455704779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5363922982279335763758821 1005735559177375455704779)
                      ·
                        rfl

theorem cell23_1958663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1958663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958663 prefixEnd_1958663 := by exact prefixLift 1958663
  have htrace : WordTrace (prefixWord ++ tailWord_1958663) baseStart_1958663 baseEnd_1958663 := by
    simpa [prefixWord, tailWord_1958663, baseEnd_1958663] using wordTrace_append hprefix tailTrace_1958663
  have hstable : (prefixWord ++ tailWord_1958663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958663).length < 2 ^ (prefixWord ++ tailWord_1958663).sum := by decide
  have hdescent : baseEnd_1958663 < baseStart_1958663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958666 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1958666 : Nat := 118140960795 + 1958666 * 2 ^ 59
def prefixEnd_1958666 : Nat := 4983230072969 + 3 ^ 40 * 1958666 * 2
def baseEnd_1958666 : Nat := 1005737099619338943967265

theorem tailTrace_1958666 : CollatzResearch.WordTrace tailWord_1958666 prefixEnd_1958666 1005737099619338943967265 := by
  unfold tailWord_1958666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859604480523767591481963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47625611948063380243951901 17859604480523767591481963)
  ·
    refine ⟨26789406720785651387222945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17859604480523767591481963 26789406720785651387222945)
    ·
      refine ⟨20092055040589238540417209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26789406720785651387222945 20092055040589238540417209)
      ·
        refine ⟨15069041280441928905312907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20092055040589238540417209 15069041280441928905312907)
        ·
          refine ⟨22603561920662893357969361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069041280441928905312907 22603561920662893357969361)
          ·
            refine ⟨16952671440497170018477021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22603561920662893357969361 16952671440497170018477021)
            ·
              refine ⟨6357251790186438756928883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16952671440497170018477021 6357251790186438756928883)
              ·
                refine ⟨9535877685279658135393325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357251790186438756928883 9535877685279658135393325)
                ·
                  refine ⟨3575954131979871800772497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9535877685279658135393325 3575954131979871800772497)
                  ·
                    refine ⟨2681965598984903850579373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3575954131979871800772497 2681965598984903850579373)
                    ·
                      refine ⟨1005737099619338943967265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2681965598984903850579373 1005737099619338943967265)
                      ·
                        rfl

theorem cell23_1958666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1958666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958666 prefixEnd_1958666 := by exact prefixLift 1958666
  have htrace : WordTrace (prefixWord ++ tailWord_1958666) baseStart_1958666 baseEnd_1958666 := by
    simpa [prefixWord, tailWord_1958666, baseEnd_1958666] using wordTrace_append hprefix tailTrace_1958666
  have hstable : (prefixWord ++ tailWord_1958666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958666).length < 2 ^ (prefixWord ++ tailWord_1958666).sum := by decide
  have hdescent : baseEnd_1958666 < baseStart_1958666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958680 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 1, 2, 2]
def baseStart_1958680 : Nat := 118140960795 + 1958680 * 2 ^ 59
def prefixEnd_1958680 : Nat := 4983230072969 + 3 ^ 40 * 1958680 * 2
def baseEnd_1958680 : Nat := 1005744288348501889192201

theorem tailTrace_1958680 : CollatzResearch.WordTrace tailWord_1958680 prefixEnd_1958680 1005744288348501889192201 := by
  unfold tailWord_1958680
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719464272022175378468747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47625952362696233837958329 35719464272022175378468747)
  ·
    refine ⟨53579196408033263067703121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35719464272022175378468747 53579196408033263067703121)
    ·
      refine ⟨40184397306024947300777341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53579196408033263067703121 40184397306024947300777341)
      ·
        refine ⟨15069148989759355237791503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40184397306024947300777341 15069148989759355237791503)
        ·
          refine ⟨22603723484639032856687255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069148989759355237791503 22603723484639032856687255)
          ·
            refine ⟨33905585226958549285030883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603723484639032856687255 33905585226958549285030883)
            ·
              refine ⟨50858377840437823927546325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33905585226958549285030883 50858377840437823927546325)
              ·
                refine ⟨1191993230635261498301867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50858377840437823927546325 1191993230635261498301867)
                ·
                  refine ⟨1787989845952892247452801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191993230635261498301867 1787989845952892247452801)
                  ·
                    refine ⟨1340992384464669185589601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787989845952892247452801 1340992384464669185589601)
                    ·
                      refine ⟨1005744288348501889192201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1340992384464669185589601 1005744288348501889192201)
                      ·
                        rfl

theorem cell23_1958680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_1958680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958680 prefixEnd_1958680 := by exact prefixLift 1958680
  have htrace : WordTrace (prefixWord ++ tailWord_1958680) baseStart_1958680 baseEnd_1958680 := by
    simpa [prefixWord, tailWord_1958680, baseEnd_1958680] using wordTrace_append hprefix tailTrace_1958680
  have hstable : (prefixWord ++ tailWord_1958680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958680).length < 2 ^ (prefixWord ++ tailWord_1958680).sum := by decide
  have hdescent : baseEnd_1958680 < baseStart_1958680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958696 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1958696 : Nat := 118140960795 + 1958696 * 2 ^ 59
def prefixEnd_1958696 : Nat := 4983230072969 + 3 ^ 40 * 1958696 * 2
def baseEnd_1958696 : Nat := 1005752504038973826592127

theorem tailTrace_1958696 : CollatzResearch.WordTrace tailWord_1958696 prefixEnd_1958696 1005752504038973826592127 := by
  unfold tailWord_1958696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719756055993192744759971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47626341407990923659679961 35719756055993192744759971)
  ·
    refine ⟨53579634083989789117139957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35719756055993192744759971 53579634083989789117139957)
    ·
      refine ⟨5023090695374042729731871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53579634083989789117139957 5023090695374042729731871)
      ·
        refine ⟨7534636043061064094597807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5023090695374042729731871 7534636043061064094597807)
        ·
          refine ⟨11301954064591596141896711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534636043061064094597807 11301954064591596141896711)
          ·
            refine ⟨16952931096887394212845067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301954064591596141896711 16952931096887394212845067)
            ·
              refine ⟨25429396645331091319267601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16952931096887394212845067 25429396645331091319267601)
              ·
                refine ⟨19072047483998318489450701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25429396645331091319267601 19072047483998318489450701)
                ·
                  refine ⟨7152017806499369433544013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19072047483998318489450701 7152017806499369433544013)
                  ·
                    refine ⟨2682006677437263537579005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7152017806499369433544013 2682006677437263537579005)
                    ·
                      refine ⟨1005752504038973826592127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2682006677437263537579005 1005752504038973826592127)
                      ·
                        rfl

theorem cell23_1958696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1958696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958696 prefixEnd_1958696 := by exact prefixLift 1958696
  have htrace : WordTrace (prefixWord ++ tailWord_1958696) baseStart_1958696 baseEnd_1958696 := by
    simpa [prefixWord, tailWord_1958696, baseEnd_1958696] using wordTrace_append hprefix tailTrace_1958696
  have hstable : (prefixWord ++ tailWord_1958696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958696).length < 2 ^ (prefixWord ++ tailWord_1958696).sum := by decide
  have hdescent : baseEnd_1958696 < baseStart_1958696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958710 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1958710 : Nat := 118140960795 + 1958710 * 2 ^ 59
def prefixEnd_1958710 : Nat := 4983230072969 + 3 ^ 40 * 1958710 * 2
def baseEnd_1958710 : Nat := 1005759692768136771817063

theorem tailTrace_1958710 : CollatzResearch.WordTrace tailWord_1958710 prefixEnd_1958710 1005759692768136771817063 := by
  unfold tailWord_1958710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465001420870979117533099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47626681822623777253686389 4465001420870979117533099)
  ·
    refine ⟨6697502131306468676299649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465001420870979117533099 6697502131306468676299649)
    ·
      refine ⟨5023126598479851507224737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6697502131306468676299649 5023126598479851507224737)
      ·
        refine ⟨3767344948859888630418553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5023126598479851507224737 3767344948859888630418553)
        ·
          refine ⟨2825508711644916472813915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767344948859888630418553 2825508711644916472813915)
          ·
            refine ⟨4238263067467374709220873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825508711644916472813915 4238263067467374709220873)
            ·
              refine ⟨3178697300600531031915655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238263067467374709220873 3178697300600531031915655)
              ·
                refine ⟨4768045950900796547873483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178697300600531031915655 4768045950900796547873483)
                ·
                  refine ⟨7152068926351194821810225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768045950900796547873483 7152068926351194821810225)
                  ·
                    refine ⟨5364051694763396116357669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152068926351194821810225 5364051694763396116357669)
                    ·
                      refine ⟨1005759692768136771817063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5364051694763396116357669 1005759692768136771817063)
                      ·
                        rfl

theorem cell23_1958710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1958710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958710 prefixEnd_1958710 := by exact prefixLift 1958710
  have htrace : WordTrace (prefixWord ++ tailWord_1958710) baseStart_1958710 baseEnd_1958710 := by
    simpa [prefixWord, tailWord_1958710, baseEnd_1958710] using wordTrace_append hprefix tailTrace_1958710
  have hstable : (prefixWord ++ tailWord_1958710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958710).length < 2 ^ (prefixWord ++ tailWord_1958710).sum := by decide
  have hdescent : baseEnd_1958710 < baseStart_1958710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958723 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 1, 3, 2]
def baseStart_1958723 : Nat := 118140960795 + 1958723 * 2 ^ 59
def prefixEnd_1958723 : Nat := 4983230072969 + 3 ^ 40 * 1958723 * 2
def baseEnd_1958723 : Nat := 1005766368016645220954503

theorem tailTrace_1958723 : CollatzResearch.WordTrace tailWord_1958723 prefixEnd_1958723 1005766368016645220954503 := by
  unfold tailWord_1958723
  simp only [CollatzResearch.WordTrace]
  refine ⟨71440496882888569100752823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47626997921925712733835215 71440496882888569100752823)
  ·
    refine ⟨107160745324332853651129235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71440496882888569100752823 107160745324332853651129235)
    ·
      refine ⟨160741117986499280476693853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107160745324332853651129235 160741117986499280476693853)
      ·
        refine ⟨60277919244937230178760195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160741117986499280476693853 60277919244937230178760195)
        ·
          refine ⟨90416878867405845268140293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60277919244937230178760195 90416878867405845268140293)
          ·
            refine ⟨16953164787638595987776305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90416878867405845268140293 16953164787638595987776305)
            ·
              refine ⟨12714873590728946990832229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16953164787638595987776305 12714873590728946990832229)
              ·
                refine ⟨2384038798261677560781043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12714873590728946990832229 2384038798261677560781043)
                ·
                  refine ⟨3576058197392516341171565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384038798261677560781043 3576058197392516341171565)
                  ·
                    refine ⟨1341021824022193627939337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576058197392516341171565 1341021824022193627939337)
                    ·
                      refine ⟨1005766368016645220954503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341021824022193627939337 1005766368016645220954503)
                      ·
                        rfl

theorem cell23_1958723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_1958723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958723 prefixEnd_1958723 := by exact prefixLift 1958723
  have htrace : WordTrace (prefixWord ++ tailWord_1958723) baseStart_1958723 baseEnd_1958723 := by
    simpa [prefixWord, tailWord_1958723, baseEnd_1958723] using wordTrace_append hprefix tailTrace_1958723
  have hstable : (prefixWord ++ tailWord_1958723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958723).length < 2 ^ (prefixWord ++ tailWord_1958723).sum := by decide
  have hdescent : baseEnd_1958723 < baseStart_1958723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958739 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_1958739 : Nat := 118140960795 + 1958739 * 2 ^ 59
def prefixEnd_1958739 : Nat := 4983230072969 + 3 ^ 40 * 1958739 * 2
def baseEnd_1958739 : Nat := 1005774583707117158354429

theorem tailTrace_1958739 : CollatzResearch.WordTrace tailWord_1958739 prefixEnd_1958739 1005774583707117158354429 := by
  unfold tailWord_1958739
  simp only [CollatzResearch.WordTrace]
  refine ⟨71441080450830603833335271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47627386967220402555556847 71441080450830603833335271)
  ·
    refine ⟨107161620676245905750002907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71441080450830603833335271 107161620676245905750002907)
    ·
      refine ⟨160742431014368858625004361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107161620676245905750002907 160742431014368858625004361)
      ·
        refine ⟨120556823260776643968753271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160742431014368858625004361 120556823260776643968753271)
        ·
          refine ⟨180835234891164965953129907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120556823260776643968753271 180835234891164965953129907)
          ·
            refine ⟨271252852336747448929694861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180835234891164965953129907 271252852336747448929694861)
            ·
              refine ⟨101719819626280293348635573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271252852336747448929694861 101719819626280293348635573)
              ·
                refine ⟨9536233089963777501434585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101719819626280293348635573 9536233089963777501434585)
                ·
                  refine ⟨7152174817472833126075939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9536233089963777501434585 7152174817472833126075939)
                  ·
                    refine ⟨10728262226209249689113909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152174817472833126075939 10728262226209249689113909)
                    ·
                      refine ⟨1005774583707117158354429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10728262226209249689113909 1005774583707117158354429)
                      ·
                        rfl

theorem cell23_1958739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_1958739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958739 prefixEnd_1958739 := by exact prefixLift 1958739
  have htrace : WordTrace (prefixWord ++ tailWord_1958739) baseStart_1958739 baseEnd_1958739 := by
    simpa [prefixWord, tailWord_1958739, baseEnd_1958739] using wordTrace_append hprefix tailTrace_1958739
  have hstable : (prefixWord ++ tailWord_1958739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958739).length < 2 ^ (prefixWord ++ tailWord_1958739).sum := by decide
  have hdescent : baseEnd_1958739 < baseStart_1958739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958770 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_1958770 : Nat := 118140960795 + 1958770 * 2 ^ 59
def prefixEnd_1958770 : Nat := 4983230072969 + 3 ^ 40 * 1958770 * 2
def baseEnd_1958770 : Nat := 1005790501607406537066787

theorem tailTrace_1958770 : CollatzResearch.WordTrace tailWord_1958770 prefixEnd_1958770 1005790501607406537066787 := by
  unfold tailWord_1958770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860552778429574031928441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47628140742478864085142509 17860552778429574031928441)
  ·
    refine ⟨13395414583822180523946331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17860552778429574031928441 13395414583822180523946331)
    ·
      refine ⟨20093121875733270785919497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13395414583822180523946331 20093121875733270785919497)
      ·
        refine ⟨15069841406799953089439623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20093121875733270785919497 15069841406799953089439623)
        ·
          refine ⟨22604762110199929634159435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069841406799953089439623 22604762110199929634159435)
          ·
            refine ⟨33907143165299894451239153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22604762110199929634159435 33907143165299894451239153)
            ·
              refine ⟨25430357373974920838429365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33907143165299894451239153 25430357373974920838429365)
              ·
                refine ⟨2384096003810148828602753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25430357373974920838429365 2384096003810148828602753)
                ·
                  refine ⟨1788072002857611621452065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384096003810148828602753 1788072002857611621452065)
                  ·
                    refine ⟨1341054002143208716089049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788072002857611621452065 1341054002143208716089049)
                    ·
                      refine ⟨1005790501607406537066787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341054002143208716089049 1005790501607406537066787)
                      ·
                        rfl

theorem cell23_1958770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_1958770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958770 prefixEnd_1958770 := by exact prefixLift 1958770
  have htrace : WordTrace (prefixWord ++ tailWord_1958770) baseStart_1958770 baseEnd_1958770 := by
    simpa [prefixWord, tailWord_1958770, baseEnd_1958770] using wordTrace_append hprefix tailTrace_1958770
  have hstable : (prefixWord ++ tailWord_1958770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958770).length < 2 ^ (prefixWord ++ tailWord_1958770).sum := by decide
  have hdescent : baseEnd_1958770 < baseStart_1958770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958793 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 5]
def baseStart_1958793 : Nat := 118140960795 + 1958793 * 2 ^ 59
def prefixEnd_1958793 : Nat := 4983230072969 + 3 ^ 40 * 1958793 * 2
def baseEnd_1958793 : Nat := 111755812406939994119909

theorem tailTrace_1958793 : CollatzResearch.WordTrace tailWord_1958793 prefixEnd_1958793 111755812406939994119909 := by
  unfold tailWord_1958793
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443049992634971055801033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47628699995089980703867355 71443049992634971055801033)
  ·
    refine ⟨53582287494476228291850775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71443049992634971055801033 53582287494476228291850775)
    ·
      refine ⟨80373431241714342437776163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53582287494476228291850775 80373431241714342437776163)
      ·
        refine ⟨120560146862571513656664245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80373431241714342437776163 120560146862571513656664245)
        ·
          refine ⟨11302513768366079405312273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120560146862571513656664245 11302513768366079405312273)
          ·
            refine ⟨8476885326274559553984205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11302513768366079405312273 8476885326274559553984205)
            ·
              refine ⟨3178831997352959832744077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8476885326274559553984205 3178831997352959832744077)
              ·
                refine ⟨1192061999007359937279029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3178831997352959832744077 1192061999007359937279029)
                ·
                  refine ⟨111755812406939994119909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192061999007359937279029 111755812406939994119909)
                  ·
                    rfl

theorem cell23_1958793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 5].length) (baseStart_1958793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958793 prefixEnd_1958793 := by exact prefixLift 1958793
  have htrace : WordTrace (prefixWord ++ tailWord_1958793) baseStart_1958793 baseEnd_1958793 := by
    simpa [prefixWord, tailWord_1958793, baseEnd_1958793] using wordTrace_append hprefix tailTrace_1958793
  have hstable : (prefixWord ++ tailWord_1958793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958793).length < 2 ^ (prefixWord ++ tailWord_1958793).sum := by decide
  have hdescent : baseEnd_1958793 < baseStart_1958793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958810 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_1958810 : Nat := 118140960795 + 1958810 * 2 ^ 59
def prefixEnd_1958810 : Nat := 4983230072969 + 3 ^ 40 * 1958810 * 2
def baseEnd_1958810 : Nat := 111756782314842931174067

theorem tailTrace_1958810 : CollatzResearch.WordTrace tailWord_1958810 prefixEnd_1958810 111756782314842931174067 := by
  unfold tailWord_1958810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860917508393345739792471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47629113355715588639446589 17860917508393345739792471)
  ·
    refine ⟨26791376262590018609688707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17860917508393345739792471 26791376262590018609688707)
    ·
      refine ⟨40187064393885027914533061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791376262590018609688707 40187064393885027914533061)
      ·
        refine ⟨7535074573853442733974949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40187064393885027914533061 7535074573853442733974949)
        ·
          refine ⟨1412826482597520512620303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7535074573853442733974949 1412826482597520512620303)
          ·
            refine ⟨2119239723896280768930455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412826482597520512620303 2119239723896280768930455)
            ·
              refine ⟨3178859585844421153395683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119239723896280768930455 3178859585844421153395683)
              ·
                refine ⟨4768289378766631730093525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178859585844421153395683 4768289378766631730093525)
                ·
                  refine ⟨111756782314842931174067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4768289378766631730093525 111756782314842931174067)
                  ·
                    rfl

theorem cell23_1958810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_1958810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958810 prefixEnd_1958810 := by exact prefixLift 1958810
  have htrace : WordTrace (prefixWord ++ tailWord_1958810) baseStart_1958810 baseEnd_1958810 := by
    simpa [prefixWord, tailWord_1958810, baseEnd_1958810] using wordTrace_append hprefix tailTrace_1958810
  have hstable : (prefixWord ++ tailWord_1958810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958810).length < 2 ^ (prefixWord ++ tailWord_1958810).sum := by decide
  have hdescent : baseEnd_1958810 < baseStart_1958810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958813 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_1958813 : Nat := 118140960795 + 1958813 * 2 ^ 59
def prefixEnd_1958813 : Nat := 4983230072969 + 3 ^ 40 * 1958813 * 2
def baseEnd_1958813 : Nat := 1005812581275549868829089

theorem tailTrace_1958813 : CollatzResearch.WordTrace tailWord_1958813 prefixEnd_1958813 1005812581275549868829089 := by
  unfold tailWord_1958813
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443779452562514471529093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47629186301708342981019395 71443779452562514471529093)
  ·
    refine ⟨13395708647355471463411705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71443779452562514471529093 13395708647355471463411705)
    ·
      refine ⟨10046781485516603597558779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13395708647355471463411705 10046781485516603597558779)
      ·
        refine ⟨15070172228274905396338169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046781485516603597558779 15070172228274905396338169)
        ·
          refine ⟨11302629171206179047253627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15070172228274905396338169 11302629171206179047253627)
          ·
            refine ⟨16953943756809268570880441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302629171206179047253627 16953943756809268570880441)
            ·
              refine ⟨12715457817606951428160331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16953943756809268570880441 12715457817606951428160331)
              ·
                refine ⟨19073186726410427142240497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715457817606951428160331 19073186726410427142240497)
                ·
                  refine ⟨14304890044807820356680373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19073186726410427142240497 14304890044807820356680373)
                  ·
                    refine ⟨1341083441700733158438785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14304890044807820356680373 1341083441700733158438785)
                    ·
                      refine ⟨1005812581275549868829089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341083441700733158438785 1005812581275549868829089)
                      ·
                        rfl

theorem cell23_1958813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_1958813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958813 prefixEnd_1958813 := by exact prefixLift 1958813
  have htrace : WordTrace (prefixWord ++ tailWord_1958813) baseStart_1958813 baseEnd_1958813 := by
    simpa [prefixWord, tailWord_1958813, baseEnd_1958813] using wordTrace_append hprefix tailTrace_1958813
  have hstable : (prefixWord ++ tailWord_1958813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958813).length < 2 ^ (prefixWord ++ tailWord_1958813).sum := by decide
  have hdescent : baseEnd_1958813 < baseStart_1958813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958863 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_1958863 : Nat := 118140960795 + 1958863 * 2 ^ 59
def prefixEnd_1958863 : Nat := 4983230072969 + 3 ^ 40 * 1958863 * 2
def baseEnd_1958863 : Nat := 1005838255308274673203859

theorem tailTrace_1958863 : CollatzResearch.WordTrace tailWord_1958863 prefixEnd_1958863 1005838255308274673203859 := by
  unfold tailWord_1958863
  simp only [CollatzResearch.WordTrace]
  refine ⟨71445603102381373010849243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47630402068254248673899495 71445603102381373010849243)
  ·
    refine ⟨107168404653572059516273865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71445603102381373010849243 107168404653572059516273865)
    ·
      refine ⟨80376303490179044637205399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107168404653572059516273865 80376303490179044637205399)
      ·
        refine ⟨120564455235268566955808099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80376303490179044637205399 120564455235268566955808099)
        ·
          refine ⟨180846682852902850433712149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120564455235268566955808099 180846682852902850433712149)
          ·
            refine ⟨8477188258729821114080257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180846682852902850433712149 8477188258729821114080257)
            ·
              refine ⟨6357891194047365835560193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477188258729821114080257 6357891194047365835560193)
              ·
                refine ⟨4768418395535524376670145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357891194047365835560193 4768418395535524376670145)
                ·
                  refine ⟨3576313796651643282502609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768418395535524376670145 3576313796651643282502609)
                  ·
                    refine ⟨2682235347488732461876957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3576313796651643282502609 2682235347488732461876957)
                    ·
                      refine ⟨1005838255308274673203859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2682235347488732461876957 1005838255308274673203859)
                      ·
                        rfl

theorem cell23_1958863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_1958863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958863 prefixEnd_1958863 := by exact prefixLift 1958863
  have htrace : WordTrace (prefixWord ++ tailWord_1958863) baseStart_1958863 baseEnd_1958863 := by
    simpa [prefixWord, tailWord_1958863, baseEnd_1958863] using wordTrace_append hprefix tailTrace_1958863
  have hstable : (prefixWord ++ tailWord_1958863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958863).length < 2 ^ (prefixWord ++ tailWord_1958863).sum := by decide
  have hdescent : baseEnd_1958863 < baseStart_1958863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958943 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 1, 6]
def baseStart_1958943 : Nat := 118140960795 + 1958943 * 2 ^ 59
def prefixEnd_1958943 : Nat := 4983230072969 + 3 ^ 40 * 1958943 * 2
def baseEnd_1958943 : Nat := 335293111253544786734497

theorem tailTrace_1958943 : CollatzResearch.WordTrace tailWord_1958943 prefixEnd_1958943 335293111253544786734497 := by
  unfold tailWord_1958943
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448520942091546673761483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47632347294727697782507655 71448520942091546673761483)
  ·
    refine ⟨107172781413137320010642225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71448520942091546673761483 107172781413137320010642225)
    ·
      refine ⟨80379586059852990007981669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107172781413137320010642225 80379586059852990007981669)
      ·
        refine ⟨15071172386222435626496563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80379586059852990007981669 15071172386222435626496563)
        ·
          refine ⟨22606758579333653439744845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071172386222435626496563 22606758579333653439744845)
          ·
            refine ⟨8477534467250120039904317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22606758579333653439744845 8477534467250120039904317)
            ·
              refine ⟨3179075425218795014964119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8477534467250120039904317 3179075425218795014964119)
              ·
                refine ⟨4768613137828192522446179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179075425218795014964119 4768613137828192522446179)
                ·
                  refine ⟨7152919706742288783669269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768613137828192522446179 7152919706742288783669269)
                  ·
                    refine ⟨335293111253544786734497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7152919706742288783669269 335293111253544786734497)
                    ·
                      rfl

theorem cell23_1958943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_1958943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958943 prefixEnd_1958943 := by exact prefixLift 1958943
  have htrace : WordTrace (prefixWord ++ tailWord_1958943) baseStart_1958943 baseEnd_1958943 := by
    simpa [prefixWord, tailWord_1958943, baseEnd_1958943] using wordTrace_append hprefix tailTrace_1958943
  have hstable : (prefixWord ++ tailWord_1958943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958943).length < 2 ^ (prefixWord ++ tailWord_1958943).sum := by decide
  have hdescent : baseEnd_1958943 < baseStart_1958943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958956 : List Nat := [2, 2, 1, 1, 1, 2, 5, 9]
def baseStart_1958956 : Nat := 118140960795 + 1958956 * 2 ^ 59
def prefixEnd_1958956 : Nat := 4983230072969 + 3 ^ 40 * 1958956 * 2
def baseEnd_1958956 : Nat := 37255037370708992938553

theorem tailTrace_1958956 : CollatzResearch.WordTrace tailWord_1958956 prefixEnd_1958956 37255037370708992938553 := by
  unfold tailWord_1958956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35724497545522224946992361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47632663394029633262656481 35724497545522224946992361)
  ·
    refine ⟨26793373159141668710244271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35724497545522224946992361 26793373159141668710244271)
    ·
      refine ⟨40190059738712503065366407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793373159141668710244271 40190059738712503065366407)
      ·
        refine ⟨60285089608068754598049611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40190059738712503065366407 60285089608068754598049611)
        ·
          refine ⟨90427634412103131897074417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60285089608068754598049611 90427634412103131897074417)
          ·
            refine ⟨67820725809077348922805813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90427634412103131897074417 67820725809077348922805813)
            ·
              refine ⟨6358193044601001461513045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67820725809077348922805813 6358193044601001461513045)
              ·
                refine ⟨37255037370708992938553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6358193044601001461513045 37255037370708992938553)
                ·
                  rfl

theorem cell23_1958956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 9].length) (baseStart_1958956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958956 prefixEnd_1958956 := by exact prefixLift 1958956
  have htrace : WordTrace (prefixWord ++ tailWord_1958956) baseStart_1958956 baseEnd_1958956 := by
    simpa [prefixWord, tailWord_1958956, baseEnd_1958956] using wordTrace_append hprefix tailTrace_1958956
  have hstable : (prefixWord ++ tailWord_1958956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958956).length < 2 ^ (prefixWord ++ tailWord_1958956).sum := by decide
  have hdescent : baseEnd_1958956 < baseStart_1958956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958970 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_1958970 : Nat := 118140960795 + 1958970 * 2 ^ 59
def prefixEnd_1958970 : Nat := 4983230072969 + 3 ^ 40 * 1958970 * 2
def baseEnd_1958970 : Nat := 1005893197738305754565867

theorem tailTrace_1958970 : CollatzResearch.WordTrace tailWord_1958970 prefixEnd_1958970 1005893197738305754565867 := by
  unfold tailWord_1958970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862376428248432571248591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47633003808662486856662909 17862376428248432571248591)
  ·
    refine ⟨26793564642372648856872887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17862376428248432571248591 26793564642372648856872887)
    ·
      refine ⟨40190346963558973285309331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793564642372648856872887 40190346963558973285309331)
      ·
        refine ⟨60285520445338459927963997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40190346963558973285309331 60285520445338459927963997)
        ·
          refine ⟨22607070167001922472986499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60285520445338459927963997 22607070167001922472986499)
          ·
            refine ⟨33910605250502883709479749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22607070167001922472986499 33910605250502883709479749)
            ·
              refine ⟨6358238484469290695527453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33910605250502883709479749 6358238484469290695527453)
              ·
                refine ⟨2384339431675984010822795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6358238484469290695527453 2384339431675984010822795)
                ·
                  refine ⟨3576509147513976016234193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384339431675984010822795 3576509147513976016234193)
                  ·
                    refine ⟨2682381860635482012175645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3576509147513976016234193 2682381860635482012175645)
                    ·
                      refine ⟨1005893197738305754565867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2682381860635482012175645 1005893197738305754565867)
                      ·
                        rfl

theorem cell23_1958970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_1958970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958970 prefixEnd_1958970 := by exact prefixLift 1958970
  have htrace : WordTrace (prefixWord ++ tailWord_1958970) baseStart_1958970 baseEnd_1958970 := by
    simpa [prefixWord, tailWord_1958970, baseEnd_1958970] using wordTrace_append hprefix tailTrace_1958970
  have hstable : (prefixWord ++ tailWord_1958970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958970).length < 2 ^ (prefixWord ++ tailWord_1958970).sum := by decide
  have hdescent : baseEnd_1958970 < baseStart_1958970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958973 : List Nat := [1, 4, 1, 3, 1, 4, 9]
def baseStart_1958973 : Nat := 118140960795 + 1958973 * 2 ^ 59
def prefixEnd_1958973 : Nat := 4983230072969 + 3 ^ 40 * 1958973 * 2
def baseEnd_1958973 : Nat := 12418453557781101763313

theorem tailTrace_1958973 : CollatzResearch.WordTrace tailWord_1958973 prefixEnd_1958973 12418453557781101763313 := by
  unfold tailWord_1958973
  simp only [CollatzResearch.WordTrace]
  refine ⟨71449615131982861797353573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47633076754655241198235715 71449615131982861797353573)
  ·
    refine ⟨13396802837246786587003795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71449615131982861797353573 13396802837246786587003795)
    ·
      refine ⟨20095204255870179880505693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13396802837246786587003795 20095204255870179880505693)
      ·
        refine ⟨7535701595951317455189635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20095204255870179880505693 7535701595951317455189635)
        ·
          refine ⟨11303552393926976182784453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535701595951317455189635 11303552393926976182784453)
          ·
            refine ⟨2119416073861308034272085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11303552393926976182784453 2119416073861308034272085)
            ·
              refine ⟨12418453557781101763313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2119416073861308034272085 12418453557781101763313)
              ·
                rfl

theorem cell23_1958973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 9].length) (baseStart_1958973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958973 prefixEnd_1958973 := by exact prefixLift 1958973
  have htrace : WordTrace (prefixWord ++ tailWord_1958973) baseStart_1958973 baseEnd_1958973 := by
    simpa [prefixWord, tailWord_1958973, baseEnd_1958973] using wordTrace_append hprefix tailTrace_1958973
  have hstable : (prefixWord ++ tailWord_1958973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958973).length < 2 ^ (prefixWord ++ tailWord_1958973).sum := by decide
  have hdescent : baseEnd_1958973 < baseStart_1958973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958994 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1958994 : Nat := 118140960795 + 1958994 * 2 ^ 59
def prefixEnd_1958994 : Nat := 4983230072969 + 3 ^ 40 * 1958994 * 2
def baseEnd_1958994 : Nat := 335301840424671220221919

theorem tailTrace_1958994 : CollatzResearch.WordTrace tailWord_1958994 prefixEnd_1958994 335301840424671220221919 := by
  unfold tailWord_1958994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862595266226695595967009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47633587376604521589245357 17862595266226695595967009)
  ·
    refine ⟨13396946449670021696975257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17862595266226695595967009 13396946449670021696975257)
    ·
      refine ⟨10047709837252516272731443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13396946449670021696975257 10047709837252516272731443)
      ·
        refine ⟨15071564755878774409097165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047709837252516272731443 15071564755878774409097165)
        ·
          refine ⟨5651836783454540403411437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15071564755878774409097165 5651836783454540403411437)
          ·
            refine ⟨2119438793795452651279289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5651836783454540403411437 2119438793795452651279289)
            ·
              refine ⟨1589579095346589488459467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2119438793795452651279289 1589579095346589488459467)
              ·
                refine ⟨2384368643019884232689201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589579095346589488459467 2384368643019884232689201)
                ·
                  refine ⟨1788276482264913174516901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384368643019884232689201 1788276482264913174516901)
                  ·
                    refine ⟨335301840424671220221919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788276482264913174516901 335301840424671220221919)
                    ·
                      rfl

theorem cell23_1958994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1958994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1958994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1958994 prefixEnd_1958994 := by exact prefixLift 1958994
  have htrace : WordTrace (prefixWord ++ tailWord_1958994) baseStart_1958994 baseEnd_1958994 := by
    simpa [prefixWord, tailWord_1958994, baseEnd_1958994] using wordTrace_append hprefix tailTrace_1958994
  have hstable : (prefixWord ++ tailWord_1958994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958994).length < 2 ^ (prefixWord ++ tailWord_1958994).sum := by decide
  have hdescent : baseEnd_1958994 < baseStart_1958994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959043 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3]
def baseStart_1959043 : Nat := 118140960795 + 1959043 * 2 ^ 59
def prefixEnd_1959043 : Nat := 4983230072969 + 3 ^ 40 * 1959043 * 2
def baseEnd_1959043 : Nat := 1005930681826083968953031

theorem tailTrace_1959043 : CollatzResearch.WordTrace tailWord_1959043 prefixEnd_1959043 1005930681826083968953031 := by
  unfold tailWord_1959043
  simp only [CollatzResearch.WordTrace]
  refine ⟨71452168241729263752401783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47634778827819509168267855 71452168241729263752401783)
  ·
    refine ⟨107178252362593895628602675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71452168241729263752401783 107178252362593895628602675)
    ·
      refine ⟨160767378543890843442904013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107178252362593895628602675 160767378543890843442904013)
      ·
        refine ⟨60287766953959066291089005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160767378543890843442904013 60287766953959066291089005)
        ·
          refine ⟨22607912607734649859158377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60287766953959066291089005 22607912607734649859158377)
          ·
            refine ⟨16955934455800987394368783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22607912607734649859158377 16955934455800987394368783)
            ·
              refine ⟨25433901683701481091553175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955934455800987394368783 25433901683701481091553175)
              ·
                refine ⟨38150852525552221637329763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433901683701481091553175 38150852525552221637329763)
                ·
                  refine ⟨57226278788328332455994645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38150852525552221637329763 57226278788328332455994645)
                  ·
                    refine ⟨2682481818202890583874749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57226278788328332455994645 2682481818202890583874749)
                    ·
                      refine ⟨1005930681826083968953031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2682481818202890583874749 1005930681826083968953031)
                      ·
                        rfl

theorem cell23_1959043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_1959043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959043 prefixEnd_1959043 := by exact prefixLift 1959043
  have htrace : WordTrace (prefixWord ++ tailWord_1959043) baseStart_1959043 baseEnd_1959043 := by
    simpa [prefixWord, tailWord_1959043, baseEnd_1959043] using wordTrace_append hprefix tailTrace_1959043
  have hstable : (prefixWord ++ tailWord_1959043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959043).length < 2 ^ (prefixWord ++ tailWord_1959043).sum := by decide
  have hdescent : baseEnd_1959043 < baseStart_1959043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959063 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 9]
def baseStart_1959063 : Nat := 118140960795 + 1959063 * 2 ^ 59
def prefixEnd_1959063 : Nat := 4983230072969 + 3 ^ 40 * 1959063 * 2
def baseEnd_1959063 : Nat := 111771216826574876744771

theorem tailTrace_1959063 : CollatzResearch.WordTrace tailWord_1959063 prefixEnd_1959063 111771216826574876744771 := by
  unfold tailWord_1959063
  simp only [CollatzResearch.WordTrace]
  refine ⟨71452897701656807168129843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47635265134437871445419895 71452897701656807168129843)
  ·
    refine ⟨107179346552485210752194765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71452897701656807168129843 107179346552485210752194765)
    ·
      refine ⟨40192254957181954032073037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107179346552485210752194765 40192254957181954032073037)
      ·
        refine ⟨15072095608943232762027389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40192254957181954032073037 15072095608943232762027389)
        ·
          refine ⟨5652035853353712285760271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15072095608943232762027389 5652035853353712285760271)
          ·
            refine ⟨8478053780030568428640407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652035853353712285760271 8478053780030568428640407)
            ·
              refine ⟨12717080670045852642960611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478053780030568428640407 12717080670045852642960611)
              ·
                refine ⟨19075621005068778964440917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717080670045852642960611 19075621005068778964440917)
                ·
                  refine ⟨111771216826574876744771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19075621005068778964440917 111771216826574876744771)
                  ·
                    rfl

theorem cell23_1959063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 9].length) (baseStart_1959063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959063 prefixEnd_1959063 := by exact prefixLift 1959063
  have htrace : WordTrace (prefixWord ++ tailWord_1959063) baseStart_1959063 baseEnd_1959063 := by
    simpa [prefixWord, tailWord_1959063, baseEnd_1959063] using wordTrace_append hprefix tailTrace_1959063
  have hstable : (prefixWord ++ tailWord_1959063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959063).length < 2 ^ (prefixWord ++ tailWord_1959063).sum := by decide
  have hdescent : baseEnd_1959063 < baseStart_1959063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959090 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1959090 : Nat := 118140960795 + 1959090 * 2 ^ 59
def prefixEnd_1959090 : Nat := 4983230072969 + 3 ^ 40 * 1959090 * 2
def baseEnd_1959090 : Nat := 1005954815416845285065315

theorem tailTrace_1959090 : CollatzResearch.WordTrace tailWord_1959090 prefixEnd_1959090 1005954815416845285065315 := by
  unfold tailWord_1959090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17863470618139747694840681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47635921648372660519575149 17863470618139747694840681)
  ·
    refine ⟨13397602963604810771130511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17863470618139747694840681 13397602963604810771130511)
    ·
      refine ⟨20096404445407216156695767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397602963604810771130511 20096404445407216156695767)
      ·
        refine ⟨30144606668110824235043651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20096404445407216156695767 30144606668110824235043651)
        ·
          refine ⟨45216910002166236352565477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30144606668110824235043651 45216910002166236352565477)
          ·
            refine ⟨8478170625406169316106027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45216910002166236352565477 8478170625406169316106027)
            ·
              refine ⟨12717255938109253974159041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478170625406169316106027 12717255938109253974159041)
              ·
                refine ⟨9537941953581940480619281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12717255938109253974159041 9537941953581940480619281)
                ·
                  refine ⟨7153456465186455360464461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537941953581940480619281 7153456465186455360464461)
                  ·
                    refine ⟨2682546174444920760174173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7153456465186455360464461 2682546174444920760174173)
                    ·
                      refine ⟨1005954815416845285065315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2682546174444920760174173 1005954815416845285065315)
                      ·
                        rfl

theorem cell23_1959090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1959090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959090 prefixEnd_1959090 := by exact prefixLift 1959090
  have htrace : WordTrace (prefixWord ++ tailWord_1959090) baseStart_1959090 baseEnd_1959090 := by
    simpa [prefixWord, tailWord_1959090, baseEnd_1959090] using wordTrace_append hprefix tailTrace_1959090
  have hstable : (prefixWord ++ tailWord_1959090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959090).length < 2 ^ (prefixWord ++ tailWord_1959090).sum := by decide
  have hdescent : baseEnd_1959090 < baseStart_1959090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959103 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_1959103 : Nat := 118140960795 + 1959103 * 2 ^ 59
def prefixEnd_1959103 : Nat := 4983230072969 + 3 ^ 40 * 1959103 * 2
def baseEnd_1959103 : Nat := 1005961490665353734202755

theorem tailTrace_1959103 : CollatzResearch.WordTrace tailWord_1959103 prefixEnd_1959103 1005961490665353734202755 := by
  unfold tailWord_1959103
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454356621511893999585963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47636237747674595999723975 71454356621511893999585963)
  ·
    refine ⟨107181534932267840999378945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71454356621511893999585963 107181534932267840999378945)
    ·
      refine ⟨80386151199200880749534209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107181534932267840999378945 80386151199200880749534209)
      ·
        refine ⟨60289613399400660562150657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80386151199200880749534209 60289613399400660562150657)
        ·
          refine ⟨45217210049550495421612993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60289613399400660562150657 45217210049550495421612993)
          ·
            refine ⟨33912907537162871566209745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45217210049550495421612993 33912907537162871566209745)
            ·
              refine ⟨25434680652872153674657309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33912907537162871566209745 25434680652872153674657309)
              ·
                refine ⟨9538005244827057627996491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25434680652872153674657309 9538005244827057627996491)
                ·
                  refine ⟨14307007867240586441994737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538005244827057627996491 14307007867240586441994737)
                  ·
                    refine ⟨10730255900430439831496053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14307007867240586441994737 10730255900430439831496053)
                    ·
                      refine ⟨1005961490665353734202755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10730255900430439831496053 1005961490665353734202755)
                      ·
                        rfl

theorem cell23_1959103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_1959103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959103 prefixEnd_1959103 := by exact prefixLift 1959103
  have htrace : WordTrace (prefixWord ++ tailWord_1959103) baseStart_1959103 baseEnd_1959103 := by
    simpa [prefixWord, tailWord_1959103, baseEnd_1959103] using wordTrace_append hprefix tailTrace_1959103
  have hstable : (prefixWord ++ tailWord_1959103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959103).length < 2 ^ (prefixWord ++ tailWord_1959103).sum := by decide
  have hdescent : baseEnd_1959103 < baseStart_1959103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959108 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_1959108 : Nat := 118140960795 + 1959108 * 2 ^ 59
def prefixEnd_1959108 : Nat := 4983230072969 + 3 ^ 40 * 1959108 * 2
def baseEnd_1959108 : Nat := 1005964058068626214640233

theorem tailTrace_1959108 : CollatzResearch.WordTrace tailWord_1959108 prefixEnd_1959108 1005964058068626214640233 := by
  unfold tailWord_1959108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35727269493246889926758989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47636359324329186569011985 35727269493246889926758989)
  ·
    refine ⟨13397726059967583722534621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35727269493246889926758989 13397726059967583722534621)
    ·
      refine ⟨5024147272487843895950483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13397726059967583722534621 5024147272487843895950483)
      ·
        refine ⟨7536220908731765843925725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024147272487843895950483 7536220908731765843925725)
        ·
          refine ⟨2826082840774412191472147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7536220908731765843925725 2826082840774412191472147)
          ·
            refine ⟨4239124261161618287208221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826082840774412191472147 4239124261161618287208221)
            ·
              refine ⟨1589671597935606857703083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239124261161618287208221 1589671597935606857703083)
              ·
                refine ⟨2384507396903410286554625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589671597935606857703083 2384507396903410286554625)
                ·
                  refine ⟨1788380547677557714915969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384507396903410286554625 1788380547677557714915969)
                  ·
                    refine ⟨1341285410758168286186977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788380547677557714915969 1341285410758168286186977)
                    ·
                      refine ⟨1005964058068626214640233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341285410758168286186977 1005964058068626214640233)
                      ·
                        rfl

theorem cell23_1959108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_1959108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959108 prefixEnd_1959108 := by exact prefixLift 1959108
  have htrace : WordTrace (prefixWord ++ tailWord_1959108) baseStart_1959108 baseEnd_1959108 := by
    simpa [prefixWord, tailWord_1959108, baseEnd_1959108] using wordTrace_append hprefix tailTrace_1959108
  have hstable : (prefixWord ++ tailWord_1959108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959108).length < 2 ^ (prefixWord ++ tailWord_1959108).sum := by decide
  have hdescent : baseEnd_1959108 < baseStart_1959108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959130 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1959130 : Nat := 118140960795 + 1959130 * 2 ^ 59
def prefixEnd_1959130 : Nat := 4983230072969 + 3 ^ 40 * 1959130 * 2
def baseEnd_1959130 : Nat := 1005975354643025128565131

theorem tailTrace_1959130 : CollatzResearch.WordTrace tailWord_1959130 prefixEnd_1959130 1005975354643025128565131 := by
  unfold tailWord_1959130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17863835348103519402704711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47636894261609385073879229 17863835348103519402704711)
  ·
    refine ⟨26795753022155279104057067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17863835348103519402704711 26795753022155279104057067)
    ·
      refine ⟨40193629533232918656085601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26795753022155279104057067 40193629533232918656085601)
      ·
        refine ⟨30145222149924688992064201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40193629533232918656085601 30145222149924688992064201)
        ·
          refine ⟨22608916612443516744048151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30145222149924688992064201 22608916612443516744048151)
          ·
            refine ⟨33913374918665275116072227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22608916612443516744048151 33913374918665275116072227)
            ·
              refine ⟨50870062377997912674108341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33913374918665275116072227 50870062377997912674108341)
              ·
                refine ⟨4769068347937304313197657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50870062377997912674108341 4769068347937304313197657)
                ·
                  refine ⟨3576801260952978234898243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4769068347937304313197657 3576801260952978234898243)
                  ·
                    refine ⟨5365201891429467352347365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3576801260952978234898243 5365201891429467352347365)
                    ·
                      refine ⟨1005975354643025128565131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5365201891429467352347365 1005975354643025128565131)
                      ·
                        rfl

theorem cell23_1959130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1959130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959130 prefixEnd_1959130 := by exact prefixLift 1959130
  have htrace : WordTrace (prefixWord ++ tailWord_1959130) baseStart_1959130 baseEnd_1959130 := by
    simpa [prefixWord, tailWord_1959130, baseEnd_1959130] using wordTrace_append hprefix tailTrace_1959130
  have hstable : (prefixWord ++ tailWord_1959130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959130).length < 2 ^ (prefixWord ++ tailWord_1959130).sum := by decide
  have hdescent : baseEnd_1959130 < baseStart_1959130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959140 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1959140 : Nat := 118140960795 + 1959140 * 2 ^ 59
def prefixEnd_1959140 : Nat := 4983230072969 + 3 ^ 40 * 1959140 * 2
def baseEnd_1959140 : Nat := 335326829816523363146695

theorem tailTrace_1959140 : CollatzResearch.WordTrace tailWord_1959140 prefixEnd_1959140 335326829816523363146695 := by
  unfold tailWord_1959140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35727853061188924659341437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47637137414918566212455249 35727853061188924659341437)
  ·
    refine ⟨13397944897945846747253039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35727853061188924659341437 13397944897945846747253039)
    ·
      refine ⟨20096917346918770120879559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397944897945846747253039 20096917346918770120879559)
      ·
        refine ⟨30145376020378155181319339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20096917346918770120879559 30145376020378155181319339)
        ·
          refine ⟨45218064030567232771979009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30145376020378155181319339 45218064030567232771979009)
          ·
            refine ⟨33913548022925424578984257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45218064030567232771979009 33913548022925424578984257)
            ·
              refine ⟨25435161017194068434238193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33913548022925424578984257 25435161017194068434238193)
              ·
                refine ⟨19076370762895551325678645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25435161017194068434238193 19076370762895551325678645)
                ·
                  refine ⟨1788409759021457936782373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19076370762895551325678645 1788409759021457936782373)
                  ·
                    refine ⟨335326829816523363146695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788409759021457936782373 335326829816523363146695)
                    ·
                      rfl

theorem cell23_1959140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1959140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959140 prefixEnd_1959140 := by exact prefixLift 1959140
  have htrace : WordTrace (prefixWord ++ tailWord_1959140) baseStart_1959140 baseEnd_1959140 := by
    simpa [prefixWord, tailWord_1959140, baseEnd_1959140] using wordTrace_append hprefix tailTrace_1959140
  have hstable : (prefixWord ++ tailWord_1959140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959140).length < 2 ^ (prefixWord ++ tailWord_1959140).sum := by decide
  have hdescent : baseEnd_1959140 < baseStart_1959140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959193 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1959193 : Nat := 118140960795 + 1959193 * 2 ^ 59
def prefixEnd_1959193 : Nat := 4983230072969 + 3 ^ 40 * 1959193 * 2
def baseEnd_1959193 : Nat := 1006007703924258382077341

theorem tailTrace_1959193 : CollatzResearch.WordTrace tailWord_1959193 prefixEnd_1959193 1006007703924258382077341 := by
  unfold tailWord_1959193
  simp only [CollatzResearch.WordTrace]
  refine ⟨71457639191185839370362233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47638426127457226246908155 71457639191185839370362233)
  ·
    refine ⟨53593229393389379527771675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71457639191185839370362233 53593229393389379527771675)
    ·
      refine ⟨80389844090084069291657513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53593229393389379527771675 80389844090084069291657513)
      ·
        refine ⟨60292383067563051968743135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80389844090084069291657513 60292383067563051968743135)
        ·
          refine ⟨90438574601344577953114703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60292383067563051968743135 90438574601344577953114703)
          ·
            refine ⟨135657861902016866929672055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90438574601344577953114703 135657861902016866929672055)
            ·
              refine ⟨203486792853025300394508083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135657861902016866929672055 203486792853025300394508083)
              ·
                refine ⟨305230189279537950591762125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203486792853025300394508083 305230189279537950591762125)
                ·
                  refine ⟨114461320979826731471910797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305230189279537950591762125 114461320979826731471910797)
                  ·
                    refine ⟨42922995367435024301966549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114461320979826731471910797 42922995367435024301966549)
                    ·
                      refine ⟨1006007703924258382077341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42922995367435024301966549 1006007703924258382077341)
                      ·
                        rfl

theorem cell23_1959193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1959193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959193 prefixEnd_1959193 := by exact prefixLift 1959193
  have htrace : WordTrace (prefixWord ++ tailWord_1959193) baseStart_1959193 baseEnd_1959193 := by
    simpa [prefixWord, tailWord_1959193, baseEnd_1959193] using wordTrace_append hprefix tailTrace_1959193
  have hstable : (prefixWord ++ tailWord_1959193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959193).length < 2 ^ (prefixWord ++ tailWord_1959193).sum := by decide
  have hdescent : baseEnd_1959193 < baseStart_1959193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959208 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1959208 : Nat := 118140960795 + 1959208 * 2 ^ 59
def prefixEnd_1959208 : Nat := 4983230072969 + 3 ^ 40 * 1959208 * 2
def baseEnd_1959208 : Nat := 335338468711358607796591

theorem tailTrace_1959208 : CollatzResearch.WordTrace tailWord_1959208 prefixEnd_1959208 335338468711358607796591 := by
  unfold tailWord_1959208
  simp only [CollatzResearch.WordTrace]
  refine ⟨35729093143065748466079139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47638790857420997954772185 35729093143065748466079139)
  ·
    refine ⟨53593639714598622699118709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35729093143065748466079139 53593639714598622699118709)
    ·
      refine ⟨5024403723243620878042379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53593639714598622699118709 5024403723243620878042379)
      ·
        refine ⟨7536605584865431317063569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024403723243620878042379 7536605584865431317063569)
        ·
          refine ⟨5652454188649073487797677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7536605584865431317063569 5652454188649073487797677)
          ·
            refine ⟨2119670320743402557924129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5652454188649073487797677 2119670320743402557924129)
            ·
              refine ⟨1589752740557551918443097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2119670320743402557924129 1589752740557551918443097)
              ·
                refine ⟨1192314555418163938832323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589752740557551918443097 1192314555418163938832323)
                ·
                  refine ⟨1788471833127245908248485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192314555418163938832323 1788471833127245908248485)
                  ·
                    refine ⟨335338468711358607796591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788471833127245908248485 335338468711358607796591)
                    ·
                      rfl

theorem cell23_1959208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1959208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959208 prefixEnd_1959208 := by exact prefixLift 1959208
  have htrace : WordTrace (prefixWord ++ tailWord_1959208) baseStart_1959208 baseEnd_1959208 := by
    simpa [prefixWord, tailWord_1959208, baseEnd_1959208] using wordTrace_append hprefix tailTrace_1959208
  have hstable : (prefixWord ++ tailWord_1959208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959208).length < 2 ^ (prefixWord ++ tailWord_1959208).sum := by decide
  have hdescent : baseEnd_1959208 < baseStart_1959208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959250 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1959250 : Nat := 118140960795 + 1959250 * 2 ^ 59
def prefixEnd_1959250 : Nat := 4983230072969 + 3 ^ 40 * 1959250 * 2
def baseEnd_1959250 : Nat := 1006036972321564659064579

theorem tailTrace_1959250 : CollatzResearch.WordTrace tailWord_1959250 prefixEnd_1959250 1006036972321564659064579 := by
  unfold tailWord_1959250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17864929537994834526296801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47639812101319558736791469 17864929537994834526296801)
  ·
    refine ⟨13398697153496125894722601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17864929537994834526296801 13398697153496125894722601)
    ·
      refine ⟨10049022865122094421041951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13398697153496125894722601 10049022865122094421041951)
      ·
        refine ⟨15073534297683141631562927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10049022865122094421041951 15073534297683141631562927)
        ·
          refine ⟨22610301446524712447344391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15073534297683141631562927 22610301446524712447344391)
          ·
            refine ⟨33915452169787068671016587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22610301446524712447344391 33915452169787068671016587)
            ·
              refine ⟨50873178254680603006524881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33915452169787068671016587 50873178254680603006524881)
              ·
                refine ⟨38154883691010452254893661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50873178254680603006524881 38154883691010452254893661)
                ·
                  refine ⟨14308081384128919595585123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38154883691010452254893661 14308081384128919595585123)
                  ·
                    refine ⟨21462122076193379393377685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14308081384128919595585123 21462122076193379393377685)
                    ·
                      refine ⟨1006036972321564659064579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21462122076193379393377685 1006036972321564659064579)
                      ·
                        rfl

theorem cell23_1959250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1959250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959250 prefixEnd_1959250 := by exact prefixLift 1959250
  have htrace : WordTrace (prefixWord ++ tailWord_1959250) baseStart_1959250 baseEnd_1959250 := by
    simpa [prefixWord, tailWord_1959250, baseEnd_1959250] using wordTrace_append hprefix tailTrace_1959250
  have hstable : (prefixWord ++ tailWord_1959250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959250).length < 2 ^ (prefixWord ++ tailWord_1959250).sum := by decide
  have hdescent : baseEnd_1959250 < baseStart_1959250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959264 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_1959264 : Nat := 118140960795 + 1959264 * 2 ^ 59
def prefixEnd_1959264 : Nat := 4983230072969 + 3 ^ 40 * 1959264 * 2
def baseEnd_1959264 : Nat := 335348053683575868096505

theorem tailTrace_1959264 : CollatzResearch.WordTrace tailWord_1959264 prefixEnd_1959264 335348053683575868096505 := by
  unfold tailWord_1959264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35730114386964309248098423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47640152515952412330797897 35730114386964309248098423)
  ·
    refine ⟨53595171580446463872147635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35730114386964309248098423 53595171580446463872147635)
    ·
      refine ⟨80392757370669695808221453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53595171580446463872147635 80392757370669695808221453)
      ·
        refine ⟨30147284014001135928083045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80392757370669695808221453 30147284014001135928083045)
        ·
          refine ⟨5652615752625212986515571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30147284014001135928083045 5652615752625212986515571)
          ·
            refine ⟨8478923628937819479773357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652615752625212986515571 8478923628937819479773357)
            ·
              refine ⟨3179596360851682304915009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8478923628937819479773357 3179596360851682304915009)
              ·
                refine ⟨2384697270638761728686257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3179596360851682304915009 2384697270638761728686257)
                ·
                  refine ⟨1788522952979071296514693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384697270638761728686257 1788522952979071296514693)
                  ·
                    refine ⟨335348053683575868096505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788522952979071296514693 335348053683575868096505)
                    ·
                      rfl

theorem cell23_1959264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_1959264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959264 prefixEnd_1959264 := by exact prefixLift 1959264
  have htrace : WordTrace (prefixWord ++ tailWord_1959264) baseStart_1959264 baseEnd_1959264 := by
    simpa [prefixWord, tailWord_1959264, baseEnd_1959264] using wordTrace_append hprefix tailTrace_1959264
  have hstable : (prefixWord ++ tailWord_1959264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959264).length < 2 ^ (prefixWord ++ tailWord_1959264).sum := by decide
  have hdescent : baseEnd_1959264 < baseStart_1959264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959274 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1959274 : Nat := 118140960795 + 1959274 * 2 ^ 59
def prefixEnd_1959274 : Nat := 4983230072969 + 3 ^ 40 * 1959274 * 2
def baseEnd_1959274 : Nat := 1006049295857272565164469

theorem tailTrace_1959274 : CollatzResearch.WordTrace tailWord_1959274 prefixEnd_1959274 1006049295857272565164469 := by
  unfold tailWord_1959274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17865148375973097551015219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47640395669261593469373917 17865148375973097551015219)
  ·
    refine ⟨26797722563959646326522829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17865148375973097551015219 26797722563959646326522829)
    ·
      refine ⟨10049145961484867372446061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26797722563959646326522829 10049145961484867372446061)
      ·
        refine ⟨3768429735556825264667273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10049145961484867372446061 3768429735556825264667273)
        ·
          refine ⟨2826322301667618948500455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3768429735556825264667273 2826322301667618948500455)
          ·
            refine ⟨4239483452501428422750683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826322301667618948500455 4239483452501428422750683)
            ·
              refine ⟨6359225178752142634126025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4239483452501428422750683 6359225178752142634126025)
              ·
                refine ⟨4769418884064106975594519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6359225178752142634126025 4769418884064106975594519)
                ·
                  refine ⟨7154128326096160463391779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4769418884064106975594519 7154128326096160463391779)
                  ·
                    refine ⟨10731192489144240695087669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7154128326096160463391779 10731192489144240695087669)
                    ·
                      refine ⟨1006049295857272565164469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10731192489144240695087669 1006049295857272565164469)
                      ·
                        rfl

theorem cell23_1959274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1959274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959274 prefixEnd_1959274 := by exact prefixLift 1959274
  have htrace : WordTrace (prefixWord ++ tailWord_1959274) baseStart_1959274 baseEnd_1959274 := by
    simpa [prefixWord, tailWord_1959274, baseEnd_1959274] using wordTrace_append hprefix tailTrace_1959274
  have hstable : (prefixWord ++ tailWord_1959274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959274).length < 2 ^ (prefixWord ++ tailWord_1959274).sum := by decide
  have hdescent : baseEnd_1959274 < baseStart_1959274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959304 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1959304 : Nat := 118140960795 + 1959304 * 2 ^ 59
def prefixEnd_1959304 : Nat := 4983230072969 + 3 ^ 40 * 1959304 * 2
def baseEnd_1959304 : Nat := 1006064700276907447789331

theorem tailTrace_1959304 : CollatzResearch.WordTrace tailWord_1959304 prefixEnd_1959304 1006064700276907447789331 := by
  unfold tailWord_1959304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35730843846891852663826483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47641125129189136885101977 35730843846891852663826483)
  ·
    refine ⟨53596265770337778995739725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35730843846891852663826483 53596265770337778995739725)
    ·
      refine ⟨20098599663876667123402397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53596265770337778995739725 20098599663876667123402397)
      ·
        refine ⟨7536974873953750171275899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20098599663876667123402397 7536974873953750171275899)
        ·
          refine ⟨11305462310930625256913849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536974873953750171275899 11305462310930625256913849)
          ·
            refine ⟨8479096733197968942685387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305462310930625256913849 8479096733197968942685387)
            ·
              refine ⟨12718645099796953414028081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479096733197968942685387 12718645099796953414028081)
              ·
                refine ⟨9538983824847715060521061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12718645099796953414028081 9538983824847715060521061)
                ·
                  refine ⟨1788559467158946573847699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9538983824847715060521061 1788559467158946573847699)
                  ·
                    refine ⟨2682839200738419860771549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1788559467158946573847699 2682839200738419860771549)
                    ·
                      refine ⟨1006064700276907447789331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2682839200738419860771549 1006064700276907447789331)
                      ·
                        rfl

theorem cell23_1959304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1959304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959304 prefixEnd_1959304 := by exact prefixLift 1959304
  have htrace : WordTrace (prefixWord ++ tailWord_1959304) baseStart_1959304 baseEnd_1959304 := by
    simpa [prefixWord, tailWord_1959304, baseEnd_1959304] using wordTrace_append hprefix tailTrace_1959304
  have hstable : (prefixWord ++ tailWord_1959304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959304).length < 2 ^ (prefixWord ++ tailWord_1959304).sum := by decide
  have hdescent : baseEnd_1959304 < baseStart_1959304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959305 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 1, 2, 2]
def baseStart_1959305 : Nat := 118140960795 + 1959305 * 2 ^ 59
def prefixEnd_1959305 : Nat := 4983230072969 + 3 ^ 40 * 1959305 * 2
def baseEnd_1959305 : Nat := 1006065213757561943876827

theorem tailTrace_1959305 : CollatzResearch.WordTrace tailWord_1959305 prefixEnd_1959305 1006065213757561943876827 := by
  unfold tailWord_1959305
  simp only [CollatzResearch.WordTrace]
  refine ⟨71461724166780082498439369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47641149444520054998959579 71461724166780082498439369)
  ·
    refine ⟨53596293125085061873829527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71461724166780082498439369 53596293125085061873829527)
    ·
      refine ⟨80394439687627592810744291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53596293125085061873829527 80394439687627592810744291)
      ·
        refine ⟨120591659531441389216116437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80394439687627592810744291 120591659531441389216116437)
        ·
          refine ⟨2826367020268157559752729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 120591659531441389216116437 2826367020268157559752729)
          ·
            refine ⟨2119775265201118169814547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826367020268157559752729 2119775265201118169814547)
            ·
              refine ⟨3179662897801677254721821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119775265201118169814547 3179662897801677254721821)
              ·
                refine ⟨1192373586675628970520683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179662897801677254721821 1192373586675628970520683)
                ·
                  refine ⟨1788560380013443455781025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192373586675628970520683 1788560380013443455781025)
                  ·
                    refine ⟨1341420285010082591835769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788560380013443455781025 1341420285010082591835769)
                    ·
                      refine ⟨1006065213757561943876827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341420285010082591835769 1006065213757561943876827)
                      ·
                        rfl

theorem cell23_1959305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 2, 2].length) (baseStart_1959305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959305 prefixEnd_1959305 := by exact prefixLift 1959305
  have htrace : WordTrace (prefixWord ++ tailWord_1959305) baseStart_1959305 baseEnd_1959305 := by
    simpa [prefixWord, tailWord_1959305, baseEnd_1959305] using wordTrace_append hprefix tailTrace_1959305
  have hstable : (prefixWord ++ tailWord_1959305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959305).length < 2 ^ (prefixWord ++ tailWord_1959305).sum := by decide
  have hdescent : baseEnd_1959305 < baseStart_1959305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959344 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2]
def baseStart_1959344 : Nat := 118140960795 + 1959344 * 2 ^ 59
def prefixEnd_1959344 : Nat := 4983230072969 + 3 ^ 40 * 1959344 * 2
def baseEnd_1959344 : Nat := 1006085239503087291289147

theorem tailTrace_1959344 : CollatzResearch.WordTrace tailWord_1959344 prefixEnd_1959344 1006085239503087291289147 := by
  unfold tailWord_1959344
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731573306819396079554543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47642097742425861439406057 35731573306819396079554543)
  ·
    refine ⟨53597359960229094119331815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35731573306819396079554543 53597359960229094119331815)
    ·
      refine ⟨80396039940343641178997723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53597359960229094119331815 80396039940343641178997723)
      ·
        refine ⟨120594059910515461768496585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80396039940343641178997723 120594059910515461768496585)
        ·
          refine ⟨90445544932886596326372439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120594059910515461768496585 90445544932886596326372439)
          ·
            refine ⟨135668317399329894489558659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90445544932886596326372439 135668317399329894489558659)
            ·
              refine ⟨203502476098994841734337989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135668317399329894489558659 203502476098994841734337989)
              ·
                refine ⟨38156714268561532825188373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203502476098994841734337989 38156714268561532825188373)
                ·
                  refine ⟨1788595981338821851180705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38156714268561532825188373 1788595981338821851180705)
                  ·
                    refine ⟨1341446986004116388385529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788595981338821851180705 1341446986004116388385529)
                    ·
                      refine ⟨1006085239503087291289147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341446986004116388385529 1006085239503087291289147)
                      ·
                        rfl

theorem cell23_1959344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2].length) (baseStart_1959344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959344 prefixEnd_1959344 := by exact prefixLift 1959344
  have htrace : WordTrace (prefixWord ++ tailWord_1959344) baseStart_1959344 baseEnd_1959344 := by
    simpa [prefixWord, tailWord_1959344, baseEnd_1959344] using wordTrace_append hprefix tailTrace_1959344
  have hstable : (prefixWord ++ tailWord_1959344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959344).length < 2 ^ (prefixWord ++ tailWord_1959344).sum := by decide
  have hdescent : baseEnd_1959344 < baseStart_1959344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959364 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1959364 : Nat := 118140960795 + 1959364 * 2 ^ 59
def prefixEnd_1959364 : Nat := 4983230072969 + 3 ^ 40 * 1959364 * 2
def baseEnd_1959364 : Nat := 1006095509116177213039055

theorem tailTrace_1959364 : CollatzResearch.WordTrace tailWord_1959364 prefixEnd_1959364 1006095509116177213039055 := by
  unfold tailWord_1959364
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731938036783167787418573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47642584049044223716558097 35731938036783167787418573)
  ·
    refine ⟨13399476763793687920281965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35731938036783167787418573 13399476763793687920281965)
    ·
      refine ⟨5024803786422632970105737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13399476763793687920281965 5024803786422632970105737)
      ·
        refine ⟨3768602839816974727579303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5024803786422632970105737 3768602839816974727579303)
        ·
          refine ⟨5652904259725462091368955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768602839816974727579303 5652904259725462091368955)
          ·
            refine ⟨8479356389588193137053433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652904259725462091368955 8479356389588193137053433)
            ·
              refine ⟨6359517292191144852790075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8479356389588193137053433 6359517292191144852790075)
              ·
                refine ⟨9539275938286717279185113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359517292191144852790075 9539275938286717279185113)
                ·
                  refine ⟨7154456953715037959388835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9539275938286717279185113 7154456953715037959388835)
                  ·
                    refine ⟨10731685430572556939083253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7154456953715037959388835 10731685430572556939083253)
                    ·
                      refine ⟨1006095509116177213039055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10731685430572556939083253 1006095509116177213039055)
                      ·
                        rfl

theorem cell23_1959364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1959364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959364 prefixEnd_1959364 := by exact prefixLift 1959364
  have htrace : WordTrace (prefixWord ++ tailWord_1959364) baseStart_1959364 baseEnd_1959364 := by
    simpa [prefixWord, tailWord_1959364, baseEnd_1959364] using wordTrace_append hprefix tailTrace_1959364
  have hstable : (prefixWord ++ tailWord_1959364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959364).length < 2 ^ (prefixWord ++ tailWord_1959364).sum := by decide
  have hdescent : baseEnd_1959364 < baseStart_1959364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959414 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1959414 : Nat := 118140960795 + 1959414 * 2 ^ 59
def prefixEnd_1959414 : Nat := 4983230072969 + 3 ^ 40 * 1959414 * 2
def baseEnd_1959414 : Nat := 335373727716300672471275

theorem tailTrace_1959414 : CollatzResearch.WordTrace tailWord_1959414 prefixEnd_1959414 335373727716300672471275 := by
  unfold tailWord_1959414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466606232711574632134831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47643799815590129409438197 4466606232711574632134831)
  ·
    refine ⟨6699909349067361948202247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4466606232711574632134831 6699909349067361948202247)
    ·
      refine ⟨10049864023601042922303371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6699909349067361948202247 10049864023601042922303371)
      ·
        refine ⟨15074796035401564383455057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10049864023601042922303371 15074796035401564383455057)
        ·
          refine ⟨11306097026551173287591293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15074796035401564383455057 11306097026551173287591293)
          ·
            refine ⟨4239786384956689982846735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11306097026551173287591293 4239786384956689982846735)
            ·
              refine ⟨6359679577435034974270103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4239786384956689982846735 6359679577435034974270103)
              ·
                refine ⟨9539519366152552461405155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359679577435034974270103 9539519366152552461405155)
                ·
                  refine ⟨14309279049228828692107733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539519366152552461405155 14309279049228828692107733)
                  ·
                    refine ⟨335373727716300672471275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14309279049228828692107733 335373727716300672471275)
                    ·
                      rfl

theorem cell23_1959414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1959414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959414 prefixEnd_1959414 := by exact prefixLift 1959414
  have htrace : WordTrace (prefixWord ++ tailWord_1959414) baseStart_1959414 baseEnd_1959414 := by
    simpa [prefixWord, tailWord_1959414, baseEnd_1959414] using wordTrace_append hprefix tailTrace_1959414
  have hstable : (prefixWord ++ tailWord_1959414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959414).length < 2 ^ (prefixWord ++ tailWord_1959414).sum := by decide
  have hdescent : baseEnd_1959414 < baseStart_1959414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959495 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 1, 4]
def baseStart_1959495 : Nat := 118140960795 + 1959495 * 2 ^ 59
def prefixEnd_1959495 : Nat := 4983230072969 + 3 ^ 40 * 1959495 * 2
def baseEnd_1959495 : Nat := 335387591693972066833651

theorem tailTrace_1959495 : CollatzResearch.WordTrace tailWord_1959495 prefixEnd_1959495 335387591693972066833651 := by
  unfold tailWord_1959495
  simp only [CollatzResearch.WordTrace]
  refine ⟨71468654036091744947855939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47645769357394496631903959 71468654036091744947855939)
  ·
    refine ⟨107202981054137617421783909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71468654036091744947855939 107202981054137617421783909)
    ·
      refine ⟨20100558947650803266584483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107202981054137617421783909 20100558947650803266584483)
      ·
        refine ⟨30150838421476204899876725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20100558947650803266584483 30150838421476204899876725)
        ·
          refine ⟨2826641102013394209363443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30150838421476204899876725 2826641102013394209363443)
          ·
            refine ⟨4239961653020091314045165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826641102013394209363443 4239961653020091314045165)
            ·
              refine ⟨1589985619882534242766937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239961653020091314045165 1589985619882534242766937)
              ·
                refine ⟨1192489214911900682075203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589985619882534242766937 1192489214911900682075203)
                ·
                  refine ⟨1788733822367851023112805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192489214911900682075203 1788733822367851023112805)
                  ·
                    refine ⟨335387591693972066833651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788733822367851023112805 335387591693972066833651)
                    ·
                      rfl

theorem cell23_1959495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_1959495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959495 prefixEnd_1959495 := by exact prefixLift 1959495
  have htrace : WordTrace (prefixWord ++ tailWord_1959495) baseStart_1959495 baseEnd_1959495 := by
    simpa [prefixWord, tailWord_1959495, baseEnd_1959495] using wordTrace_append hprefix tailTrace_1959495
  have hstable : (prefixWord ++ tailWord_1959495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959495).length < 2 ^ (prefixWord ++ tailWord_1959495).sum := by decide
  have hdescent : baseEnd_1959495 < baseStart_1959495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959528 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1959528 : Nat := 118140960795 + 1959528 * 2 ^ 59
def prefixEnd_1959528 : Nat := 4983230072969 + 3 ^ 40 * 1959528 * 2
def baseEnd_1959528 : Nat := 1006179719943514571388301

theorem tailTrace_1959528 : CollatzResearch.WordTrace tailWord_1959528 prefixEnd_1959528 1006179719943514571388301 := by
  unfold tailWord_1959528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35734928822486095791903619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47646571763314794389204825 35734928822486095791903619)
  ·
    refine ⟨53602393233729143687855429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35734928822486095791903619 53602393233729143687855429)
    ·
      refine ⟨10050448731324214441472893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53602393233729143687855429 10050448731324214441472893)
      ·
        refine ⟨3768918274246580415552335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10050448731324214441472893 3768918274246580415552335)
        ·
          refine ⟨5653377411369870623328503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768918274246580415552335 5653377411369870623328503)
          ·
            refine ⟨8480066117054805934992755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653377411369870623328503 8480066117054805934992755)
            ·
              refine ⟨12720099175582208902489133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480066117054805934992755 12720099175582208902489133)
              ·
                refine ⟨4770037190843328338433425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12720099175582208902489133 4770037190843328338433425)
                ·
                  refine ⟨3577527893132496253825069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4770037190843328338433425 3577527893132496253825069)
                  ·
                    refine ⟨1341572959924686095184401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577527893132496253825069 1341572959924686095184401)
                    ·
                      refine ⟨1006179719943514571388301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341572959924686095184401 1006179719943514571388301)
                      ·
                        rfl

theorem cell23_1959528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1959528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959528 prefixEnd_1959528 := by exact prefixLift 1959528
  have htrace : WordTrace (prefixWord ++ tailWord_1959528) baseStart_1959528 baseEnd_1959528 := by
    simpa [prefixWord, tailWord_1959528, baseEnd_1959528] using wordTrace_append hprefix tailTrace_1959528
  have hstable : (prefixWord ++ tailWord_1959528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959528).length < 2 ^ (prefixWord ++ tailWord_1959528).sum := by decide
  have hdescent : baseEnd_1959528 < baseStart_1959528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959538 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1959538 : Nat := 118140960795 + 1959538 * 2 ^ 59
def prefixEnd_1959538 : Nat := 4983230072969 + 3 ^ 40 * 1959538 * 2
def baseEnd_1959538 : Nat := 335394951583353177421085

theorem tailTrace_1959538 : CollatzResearch.WordTrace tailWord_1959538 prefixEnd_1959538 335394951583353177421085 := by
  unfold tailWord_1959538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867555593733990822917817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47646814916623975527780845 17867555593733990822917817)
  ·
    refine ⟨13400666695300493117188363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17867555593733990822917817 13400666695300493117188363)
    ·
      refine ⟨20101000042950739675782545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13400666695300493117188363 20101000042950739675782545)
      ·
        refine ⟨15075750032213054756836909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20101000042950739675782545 15075750032213054756836909)
        ·
          refine ⟨5653406262079895533813841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15075750032213054756836909 5653406262079895533813841)
          ·
            refine ⟨4240054696559921650360381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653406262079895533813841 4240054696559921650360381)
            ·
              refine ⟨1590020511209970618885143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4240054696559921650360381 1590020511209970618885143)
              ·
                refine ⟨2385030766814955928327715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590020511209970618885143 2385030766814955928327715)
                ·
                  refine ⟨3577546150222433892491573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385030766814955928327715 3577546150222433892491573)
                  ·
                    refine ⟨335394951583353177421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3577546150222433892491573 335394951583353177421085)
                    ·
                      rfl

theorem cell23_1959538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1959538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959538 prefixEnd_1959538 := by exact prefixLift 1959538
  have htrace : WordTrace (prefixWord ++ tailWord_1959538) baseStart_1959538 baseEnd_1959538 := by
    simpa [prefixWord, tailWord_1959538, baseEnd_1959538] using wordTrace_append hprefix tailTrace_1959538
  have hstable : (prefixWord ++ tailWord_1959538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959538).length < 2 ^ (prefixWord ++ tailWord_1959538).sum := by decide
  have hdescent : baseEnd_1959538 < baseStart_1959538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959544 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1959544 : Nat := 118140960795 + 1959544 * 2 ^ 59
def prefixEnd_1959544 : Nat := 4983230072969 + 3 ^ 40 * 1959544 * 2
def baseEnd_1959544 : Nat := 1006187935633986508788227

theorem tailTrace_1959544 : CollatzResearch.WordTrace tailWord_1959544 prefixEnd_1959544 1006187935633986508788227 := by
  unfold tailWord_1959544
  simp only [CollatzResearch.WordTrace]
  refine ⟨35735220606457113158194843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47646960808609484210926457 35735220606457113158194843)
  ·
    refine ⟨53602830909685669737292265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35735220606457113158194843 53602830909685669737292265)
    ·
      refine ⟨40202123182264252302969199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53602830909685669737292265 40202123182264252302969199)
      ·
        refine ⟨60303184773396378454453799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40202123182264252302969199 60303184773396378454453799)
        ·
          refine ⟨90454777160094567681680699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60303184773396378454453799 90454777160094567681680699)
          ·
            refine ⟨135682165740141851522521049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90454777160094567681680699 135682165740141851522521049)
            ·
              refine ⟨101761624305106388641890787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135682165740141851522521049 101761624305106388641890787)
              ·
                refine ⟨152642436457659582962836181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101761624305106388641890787 152642436457659582962836181)
                ·
                  refine ⟨3577557104476396475691473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152642436457659582962836181 3577557104476396475691473)
                  ·
                    refine ⟨2683167828357297356768605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3577557104476396475691473 2683167828357297356768605)
                    ·
                      refine ⟨1006187935633986508788227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2683167828357297356768605 1006187935633986508788227)
                      ·
                        rfl

theorem cell23_1959544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1959544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959544 prefixEnd_1959544 := by exact prefixLift 1959544
  have htrace : WordTrace (prefixWord ++ tailWord_1959544) baseStart_1959544 baseEnd_1959544 := by
    simpa [prefixWord, tailWord_1959544, baseEnd_1959544] using wordTrace_append hprefix tailTrace_1959544
  have hstable : (prefixWord ++ tailWord_1959544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959544).length < 2 ^ (prefixWord ++ tailWord_1959544).sum := by decide
  have hdescent : baseEnd_1959544 < baseStart_1959544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959592 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1959592 : Nat := 118140960795 + 1959592 * 2 ^ 59
def prefixEnd_1959592 : Nat := 4983230072969 + 3 ^ 40 * 1959592 * 2
def baseEnd_1959592 : Nat := 1006212582705402320988007

theorem tailTrace_1959592 : CollatzResearch.WordTrace tailWord_1959592 prefixEnd_1959592 1006212582705402320988007 := by
  unfold tailWord_1959592
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736095958370165257068515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47648127944493553676091353 35736095958370165257068515)
  ·
    refine ⟨53604143937555247885602773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736095958370165257068515 53604143937555247885602773)
    ·
      refine ⟨1256347123536451122318815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53604143937555247885602773 1256347123536451122318815)
      ·
        refine ⟨1884520685304676683478223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256347123536451122318815 1884520685304676683478223)
        ·
          refine ⟨2826781027957015025217335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884520685304676683478223 2826781027957015025217335)
          ·
            refine ⟨4240171541935522537826003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826781027957015025217335 4240171541935522537826003)
            ·
              refine ⟨6360257312903283806739005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240171541935522537826003 6360257312903283806739005)
              ·
                refine ⟨2385096492338731427527127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360257312903283806739005 2385096492338731427527127)
                ·
                  refine ⟨3577644738508097141290691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385096492338731427527127 3577644738508097141290691)
                  ·
                    refine ⟨5366467107762145711936037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3577644738508097141290691 5366467107762145711936037)
                    ·
                      refine ⟨1006212582705402320988007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5366467107762145711936037 1006212582705402320988007)
                      ·
                        rfl

theorem cell23_1959592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1959592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959592 prefixEnd_1959592 := by exact prefixLift 1959592
  have htrace : WordTrace (prefixWord ++ tailWord_1959592) baseStart_1959592 baseEnd_1959592 := by
    simpa [prefixWord, tailWord_1959592, baseEnd_1959592] using wordTrace_append hprefix tailTrace_1959592
  have hstable : (prefixWord ++ tailWord_1959592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959592).length < 2 ^ (prefixWord ++ tailWord_1959592).sum := by decide
  have hdescent : baseEnd_1959592 < baseStart_1959592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959622 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1959622 : Nat := 118140960795 + 1959622 * 2 ^ 59
def prefixEnd_1959622 : Nat := 4983230072969 + 3 ^ 40 * 1959622 * 2
def baseEnd_1959622 : Nat := 1006227987125037203612869

theorem tailTrace_1959622 : CollatzResearch.WordTrace tailWord_1959622 prefixEnd_1959622 1006227987125037203612869 := by
  unfold tailWord_1959622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233540190832238926179035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47648857404421097091819413 2233540190832238926179035)
  ·
    refine ⟨3350310286248358389268553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233540190832238926179035 3350310286248358389268553)
    ·
      refine ⟨2512732714686268791951415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3350310286248358389268553 2512732714686268791951415)
      ·
        refine ⟨3769099072029403187927123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512732714686268791951415 3769099072029403187927123)
        ·
          refine ⟨5653648608044104781890685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769099072029403187927123 5653648608044104781890685)
          ·
            refine ⟨2120118228016539293209007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5653648608044104781890685 2120118228016539293209007)
            ·
              refine ⟨3180177342024808939813511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120118228016539293209007 3180177342024808939813511)
              ·
                refine ⟨4770266013037213409720267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180177342024808939813511 4770266013037213409720267)
                ·
                  refine ⟨7155399019555820114580401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770266013037213409720267 7155399019555820114580401)
                  ·
                    refine ⟨5366549264666865085935301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7155399019555820114580401 5366549264666865085935301)
                    ·
                      refine ⟨1006227987125037203612869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5366549264666865085935301 1006227987125037203612869)
                      ·
                        rfl

theorem cell23_1959622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1959622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959622 prefixEnd_1959622 := by exact prefixLift 1959622
  have htrace : WordTrace (prefixWord ++ tailWord_1959622) baseStart_1959622 baseEnd_1959622 := by
    simpa [prefixWord, tailWord_1959622, baseEnd_1959622] using wordTrace_append hprefix tailTrace_1959622
  have hstable : (prefixWord ++ tailWord_1959622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959622).length < 2 ^ (prefixWord ++ tailWord_1959622).sum := by decide
  have hdescent : baseEnd_1959622 < baseStart_1959622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959624 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1959624 : Nat := 118140960795 + 1959624 * 2 ^ 59
def prefixEnd_1959624 : Nat := 4983230072969 + 3 ^ 40 * 1959624 * 2
def baseEnd_1959624 : Nat := 335409671362115398595953

theorem tailTrace_1959624 : CollatzResearch.WordTrace tailWord_1959624 prefixEnd_1959624 335409671362115398595953 := by
  unfold tailWord_1959624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736679526312199989650963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47648906035082933319534617 35736679526312199989650963)
  ·
    refine ⟨53605019289468299984476445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736679526312199989650963 53605019289468299984476445)
    ·
      refine ⟨20101882233550612494178667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53605019289468299984476445 20101882233550612494178667)
      ·
        refine ⟨30152823350325918741268001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101882233550612494178667 30152823350325918741268001)
        ·
          refine ⟨22614617512744439055951001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30152823350325918741268001 22614617512744439055951001)
          ·
            refine ⟨16960963134558329291963251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22614617512744439055951001 16960963134558329291963251)
            ·
              refine ⟨25441444701837493937944877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16960963134558329291963251 25441444701837493937944877)
              ·
                refine ⟨9540541763189060226729329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25441444701837493937944877 9540541763189060226729329)
                ·
                  refine ⟨7155406322391795170046997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540541763189060226729329 7155406322391795170046997)
                  ·
                    refine ⟨335409671362115398595953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7155406322391795170046997 335409671362115398595953)
                    ·
                      rfl

theorem cell23_1959624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1959624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959624 prefixEnd_1959624 := by exact prefixLift 1959624
  have htrace : WordTrace (prefixWord ++ tailWord_1959624) baseStart_1959624 baseEnd_1959624 := by
    simpa [prefixWord, tailWord_1959624, baseEnd_1959624] using wordTrace_append hprefix tailTrace_1959624
  have hstable : (prefixWord ++ tailWord_1959624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959624).length < 2 ^ (prefixWord ++ tailWord_1959624).sum := by decide
  have hdescent : baseEnd_1959624 < baseStart_1959624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959648 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2]
def baseStart_1959648 : Nat := 118140960795 + 1959648 * 2 ^ 59
def prefixEnd_1959648 : Nat := 4983230072969 + 3 ^ 40 * 1959648 * 2
def baseEnd_1959648 : Nat := 1006241337622054101887749

theorem tailTrace_1959648 : CollatzResearch.WordTrace tailWord_1959648 prefixEnd_1959648 1006241337622054101887749 := by
  unfold tailWord_1959648
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737117202268726039087799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47649489603024968052117065 35737117202268726039087799)
  ·
    refine ⟨53605675803403089058631699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35737117202268726039087799 53605675803403089058631699)
    ·
      refine ⟨80408513705104633587947549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53605675803403089058631699 80408513705104633587947549)
      ·
        refine ⟨30153192639414237595480331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80408513705104633587947549 30153192639414237595480331)
        ·
          refine ⟨45229788959121356393220497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30153192639414237595480331 45229788959121356393220497)
          ·
            refine ⟨33922341719341017294915373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45229788959121356393220497 33922341719341017294915373)
            ·
              refine ⟨12720878144752881485593265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33922341719341017294915373 12720878144752881485593265)
              ·
                refine ⟨9540658608564661114194949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12720878144752881485593265 9540658608564661114194949)
                ·
                  refine ⟨1788873489105873958911553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9540658608564661114194949 1788873489105873958911553)
                  ·
                    refine ⟨1341655116829405469183665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788873489105873958911553 1341655116829405469183665)
                    ·
                      refine ⟨1006241337622054101887749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341655116829405469183665 1006241337622054101887749)
                      ·
                        rfl

theorem cell23_1959648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_1959648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959648 prefixEnd_1959648 := by exact prefixLift 1959648
  have htrace : WordTrace (prefixWord ++ tailWord_1959648) baseStart_1959648 baseEnd_1959648 := by
    simpa [prefixWord, tailWord_1959648, baseEnd_1959648] using wordTrace_append hprefix tailTrace_1959648
  have hstable : (prefixWord ++ tailWord_1959648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959648).length < 2 ^ (prefixWord ++ tailWord_1959648).sum := by decide
  have hdescent : baseEnd_1959648 < baseStart_1959648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959671 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 5]
def baseStart_1959671 : Nat := 118140960795 + 1959671 * 2 ^ 59
def prefixEnd_1959671 : Nat := 4983230072969 + 3 ^ 40 * 1959671 * 2
def baseEnd_1959671 : Nat := 111805905297456390211127

theorem tailTrace_1959671 : CollatzResearch.WordTrace tailWord_1959671 prefixEnd_1959671 111805905297456390211127 := by
  unfold tailWord_1959671
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475073283454127006262867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47650048855636084670841911 71475073283454127006262867)
  ·
    refine ⟨107212609925181190509394301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71475073283454127006262867 107212609925181190509394301)
    ·
      refine ⟨40204728721942946441022863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107212609925181190509394301 40204728721942946441022863)
      ·
        refine ⟨60307093082914419661534295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40204728721942946441022863 60307093082914419661534295)
        ·
          refine ⟨90460639624371629492301443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60307093082914419661534295 90460639624371629492301443)
          ·
            refine ⟨135690959436557444238452165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90460639624371629492301443 135690959436557444238452165)
            ·
              refine ⟨25442054894354520794709781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135690959436557444238452165 25442054894354520794709781)
              ·
                refine ⟨1192596323172868162252021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25442054894354520794709781 1192596323172868162252021)
                ·
                  refine ⟨111805905297456390211127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192596323172868162252021 111805905297456390211127)
                  ·
                    rfl

theorem cell23_1959671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 5].length) (baseStart_1959671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959671 prefixEnd_1959671 := by exact prefixLift 1959671
  have htrace : WordTrace (prefixWord ++ tailWord_1959671) baseStart_1959671 baseEnd_1959671 := by
    simpa [prefixWord, tailWord_1959671, baseEnd_1959671] using wordTrace_append hprefix tailTrace_1959671
  have hstable : (prefixWord ++ tailWord_1959671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959671).length < 2 ^ (prefixWord ++ tailWord_1959671).sum := by decide
  have hdescent : baseEnd_1959671 < baseStart_1959671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959681 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1959681 : Nat := 118140960795 + 1959681 * 2 ^ 59
def prefixEnd_1959681 : Nat := 4983230072969 + 3 ^ 40 * 1959681 * 2
def baseEnd_1959681 : Nat := 1006258282483652472775097

theorem tailTrace_1959681 : CollatzResearch.WordTrace tailWord_1959681 prefixEnd_1959681 1006258282483652472775097 := by
  unfold tailWord_1959681
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475438013417898714126897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47650292008945265809417931 71475438013417898714126897)
  ·
    refine ⟨53606578510063424035595173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71475438013417898714126897 53606578510063424035595173)
    ·
      refine ⟨10051233470636892006674095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53606578510063424035595173 10051233470636892006674095)
      ·
        refine ⟨15076850205955338010011143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051233470636892006674095 15076850205955338010011143)
        ·
          refine ⟨22615275308933007015016715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076850205955338010011143 22615275308933007015016715)
          ·
            refine ⟨33922912963399510522525073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615275308933007015016715 33922912963399510522525073)
            ·
              refine ⟨25442184722549632891893805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33922912963399510522525073 25442184722549632891893805)
              ·
                refine ⟨9540819270956112334460177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25442184722549632891893805 9540819270956112334460177)
                ·
                  refine ⟨7155614453217084250845133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540819270956112334460177 7155614453217084250845133)
                  ·
                    refine ⟨2683355419956406594066925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7155614453217084250845133 2683355419956406594066925)
                    ·
                      refine ⟨1006258282483652472775097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2683355419956406594066925 1006258282483652472775097)
                      ·
                        rfl

theorem cell23_1959681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1959681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959681 prefixEnd_1959681 := by exact prefixLift 1959681
  have htrace : WordTrace (prefixWord ++ tailWord_1959681) baseStart_1959681 baseEnd_1959681 := by
    simpa [prefixWord, tailWord_1959681, baseEnd_1959681] using wordTrace_append hprefix tailTrace_1959681
  have hstable : (prefixWord ++ tailWord_1959681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959681).length < 2 ^ (prefixWord ++ tailWord_1959681).sum := by decide
  have hdescent : baseEnd_1959681 < baseStart_1959681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959682 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_1959682 : Nat := 118140960795 + 1959682 * 2 ^ 59
def prefixEnd_1959682 : Nat := 4983230072969 + 3 ^ 40 * 1959682 * 2
def baseEnd_1959682 : Nat := 1006258795964306968862593

theorem tailTrace_1959682 : CollatzResearch.WordTrace tailWord_1959682 prefixEnd_1959682 1006258795964306968862593 := by
  unfold tailWord_1959682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868868621603568971228325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47650316324276183923275533 17868868621603568971228325)
  ·
    refine ⟨3350412866550669182105311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17868868621603568971228325 3350412866550669182105311)
    ·
      refine ⟨5025619299826003773157967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350412866550669182105311 5025619299826003773157967)
      ·
        refine ⟨7538428949739005659736951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025619299826003773157967 7538428949739005659736951)
        ·
          refine ⟨11307643424608508489605427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538428949739005659736951 11307643424608508489605427)
          ·
            refine ⟨16961465136912762734408141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307643424608508489605427 16961465136912762734408141)
            ·
              refine ⟨6360549426342286025403053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16961465136912762734408141 6360549426342286025403053)
              ·
                refine ⟨2385206034878357259526145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360549426342286025403053 2385206034878357259526145)
                ·
                  refine ⟨1788904526158767944644609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385206034878357259526145 1788904526158767944644609)
                  ·
                    refine ⟨1341678394619075958483457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788904526158767944644609 1341678394619075958483457)
                    ·
                      refine ⟨1006258795964306968862593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341678394619075958483457 1006258795964306968862593)
                      ·
                        rfl

theorem cell23_1959682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_1959682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959682 prefixEnd_1959682 := by exact prefixLift 1959682
  have htrace : WordTrace (prefixWord ++ tailWord_1959682) baseStart_1959682 baseEnd_1959682 := by
    simpa [prefixWord, tailWord_1959682, baseEnd_1959682] using wordTrace_append hprefix tailTrace_1959682
  have hstable : (prefixWord ++ tailWord_1959682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959682).length < 2 ^ (prefixWord ++ tailWord_1959682).sum := by decide
  have hdescent : baseEnd_1959682 < baseStart_1959682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959701 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1959701 : Nat := 118140960795 + 1959701 * 2 ^ 59
def prefixEnd_1959701 : Nat := 4983230072969 + 3 ^ 40 * 1959701 * 2
def baseEnd_1959701 : Nat := 335422850698914131508335

theorem tailTrace_1959701 : CollatzResearch.WordTrace tailWord_1959701 prefixEnd_1959701 335422850698914131508335 := by
  unfold tailWord_1959701
  simp only [CollatzResearch.WordTrace]
  refine ⟨71476167473345442129854957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47650778315563628086569971 71476167473345442129854957)
  ·
    refine ⟨26803562802504540798695609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71476167473345442129854957 26803562802504540798695609)
    ·
      refine ⟨20102672101878405599021707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26803562802504540798695609 20102672101878405599021707)
      ·
        refine ⟨30154008152817608398532561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20102672101878405599021707 30154008152817608398532561)
        ·
          refine ⟨22615506114613206298899421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30154008152817608398532561 22615506114613206298899421)
          ·
            refine ⟨8480814792979952362087283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22615506114613206298899421 8480814792979952362087283)
            ·
              refine ⟨12721222189469928543130925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480814792979952362087283 12721222189469928543130925)
              ·
                refine ⟨4770458321051223203674097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12721222189469928543130925 4770458321051223203674097)
                ·
                  refine ⟨3577843740788417402755573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4770458321051223203674097 3577843740788417402755573)
                  ·
                    refine ⟨335422850698914131508335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3577843740788417402755573 335422850698914131508335)
                    ·
                      rfl

theorem cell23_1959701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1959701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959701 prefixEnd_1959701 := by exact prefixLift 1959701
  have htrace : WordTrace (prefixWord ++ tailWord_1959701) baseStart_1959701 baseEnd_1959701 := by
    simpa [prefixWord, tailWord_1959701, baseEnd_1959701] using wordTrace_append hprefix tailTrace_1959701
  have hstable : (prefixWord ++ tailWord_1959701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959701).length < 2 ^ (prefixWord ++ tailWord_1959701).sum := by decide
  have hdescent : baseEnd_1959701 < baseStart_1959701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959738 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_1959738 : Nat := 118140960795 + 1959738 * 2 ^ 59
def prefixEnd_1959738 : Nat := 4983230072969 + 3 ^ 40 * 1959738 * 2
def baseEnd_1959738 : Nat := 1006287550880958749762335

theorem tailTrace_1959738 : CollatzResearch.WordTrace tailWord_1959738 prefixEnd_1959738 1006287550880958749762335 := by
  unfold tailWord_1959738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869379243552849362237967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47651677982807598299301245 17869379243552849362237967)
  ·
    refine ⟨26804068865329274043356951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17869379243552849362237967 26804068865329274043356951)
    ·
      refine ⟨40206103297993911065035427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26804068865329274043356951 40206103297993911065035427)
      ·
        refine ⟨60309154946990866597553141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40206103297993911065035427 60309154946990866597553141)
        ·
          refine ⟨5653983276280393743520607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60309154946990866597553141 5653983276280393743520607)
          ·
            refine ⟨8480974914420590615280911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653983276280393743520607 8480974914420590615280911)
            ·
              refine ⟨12721462371630885922921367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480974914420590615280911 12721462371630885922921367)
              ·
                refine ⟨19082193557446328884382051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721462371630885922921367 19082193557446328884382051)
                ·
                  refine ⟨28623290336169493326573077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19082193557446328884382051 28623290336169493326573077)
                  ·
                    refine ⟨1341716734507944999683113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28623290336169493326573077 1341716734507944999683113)
                    ·
                      refine ⟨1006287550880958749762335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341716734507944999683113 1006287550880958749762335)
                      ·
                        rfl

theorem cell23_1959738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_1959738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959738 prefixEnd_1959738 := by exact prefixLift 1959738
  have htrace : WordTrace (prefixWord ++ tailWord_1959738) baseStart_1959738 baseEnd_1959738 := by
    simpa [prefixWord, tailWord_1959738, baseEnd_1959738] using wordTrace_append hprefix tailTrace_1959738
  have hstable : (prefixWord ++ tailWord_1959738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959738).length < 2 ^ (prefixWord ++ tailWord_1959738).sum := by decide
  have hdescent : baseEnd_1959738 < baseStart_1959738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959744 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 12]
def baseStart_1959744 : Nat := 118140960795 + 1959744 * 2 ^ 59
def prefixEnd_1959744 : Nat := 4983230072969 + 3 ^ 40 * 1959744 * 2
def baseEnd_1959744 : Nat := 111810070196098414031923

theorem tailTrace_1959744 : CollatzResearch.WordTrace tailWord_1959744 prefixEnd_1959744 111810070196098414031923 := by
  unfold tailWord_1959744
  simp only [CollatzResearch.WordTrace]
  refine ⟨35738867906094830236835143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47651823874793106982446857 35738867906094830236835143)
  ·
    refine ⟨53608301859142245355252715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35738867906094830236835143 53608301859142245355252715)
    ·
      refine ⟨80412452788713368032879073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53608301859142245355252715 80412452788713368032879073)
      ·
        refine ⟨60309339591535026024659305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80412452788713368032879073 60309339591535026024659305)
        ·
          refine ⟨45232004693651269518494479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60309339591535026024659305 45232004693651269518494479)
          ·
            refine ⟨67848007040476904277741719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45232004693651269518494479 67848007040476904277741719)
            ·
              refine ⟨101772010560715356416612579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67848007040476904277741719 101772010560715356416612579)
              ·
                refine ⟨152658015841073034624918869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101772010560715356416612579 152658015841073034624918869)
                ·
                  refine ⟨111810070196098414031923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 152658015841073034624918869 111810070196098414031923)
                  ·
                    rfl

theorem cell23_1959744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_1959744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959744 prefixEnd_1959744 := by exact prefixLift 1959744
  have htrace : WordTrace (prefixWord ++ tailWord_1959744) baseStart_1959744 baseEnd_1959744 := by
    simpa [prefixWord, tailWord_1959744, baseEnd_1959744] using wordTrace_append hprefix tailTrace_1959744
  have hstable : (prefixWord ++ tailWord_1959744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959744).length < 2 ^ (prefixWord ++ tailWord_1959744).sum := by decide
  have hdescent : baseEnd_1959744 < baseStart_1959744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959765 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_1959765 : Nat := 118140960795 + 1959765 * 2 ^ 59
def prefixEnd_1959765 : Nat := 4983230072969 + 3 ^ 40 * 1959765 * 2
def baseEnd_1959765 : Nat := 335433804952876714708237

theorem tailTrace_1959765 : CollatzResearch.WordTrace tailWord_1959765 prefixEnd_1959765 335433804952876714708237 := by
  unfold tailWord_1959765
  simp only [CollatzResearch.WordTrace]
  refine ⟨71478501745113581060184749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47652334496742387373456499 71478501745113581060184749)
  ·
    refine ⟨26804438154417592897569281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71478501745113581060184749 26804438154417592897569281)
    ·
      refine ⟨20103328615813194673176961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26804438154417592897569281 20103328615813194673176961)
      ·
        refine ⟨15077496461859896004882721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20103328615813194673176961 15077496461859896004882721)
        ·
          refine ⟨11308122346394922003662041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15077496461859896004882721 11308122346394922003662041)
          ·
            refine ⟨8481091759796191502746531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11308122346394922003662041 8481091759796191502746531)
            ·
              refine ⟨12721637639694287254119797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481091759796191502746531 12721637639694287254119797)
              ·
                refine ⟨1192653528721339430073731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12721637639694287254119797 1192653528721339430073731)
                ·
                  refine ⟨1788980293082009145110597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192653528721339430073731 1788980293082009145110597)
                  ·
                    refine ⟨335433804952876714708237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788980293082009145110597 335433804952876714708237)
                    ·
                      rfl

theorem cell23_1959765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_1959765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959765 prefixEnd_1959765 := by exact prefixLift 1959765
  have htrace : WordTrace (prefixWord ++ tailWord_1959765) baseStart_1959765 baseEnd_1959765 := by
    simpa [prefixWord, tailWord_1959765, baseEnd_1959765] using wordTrace_append hprefix tailTrace_1959765
  have hstable : (prefixWord ++ tailWord_1959765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959765).length < 2 ^ (prefixWord ++ tailWord_1959765).sum := by decide
  have hdescent : baseEnd_1959765 < baseStart_1959765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959778 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1959778 : Nat := 118140960795 + 1959778 * 2 ^ 59
def prefixEnd_1959778 : Nat := 4983230072969 + 3 ^ 40 * 1959778 * 2
def baseEnd_1959778 : Nat := 111812010011904288140239

theorem tailTrace_1959778 : CollatzResearch.WordTrace tailWord_1959778 prefixEnd_1959778 111812010011904288140239 := by
  unfold tailWord_1959778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869743973516621070101997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47652650596044322853605325 17869743973516621070101997)
  ·
    refine ⟨6701153990068732901288249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17869743973516621070101997 6701153990068732901288249)
    ·
      refine ⟨5025865492551549675966187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6701153990068732901288249 5025865492551549675966187)
      ·
        refine ⟨7538798238827324513949281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025865492551549675966187 7538798238827324513949281)
        ·
          refine ⟨5654098679120493385461961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7538798238827324513949281 5654098679120493385461961)
          ·
            refine ⟨4240574009340370039096471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5654098679120493385461961 4240574009340370039096471)
            ·
              refine ⟨6360861014010555058644707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240574009340370039096471 6360861014010555058644707)
              ·
                refine ⟨9541291521015832587967061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360861014010555058644707 9541291521015832587967061)
                ·
                  refine ⟨111812010011904288140239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9541291521015832587967061 111812010011904288140239)
                  ·
                    rfl

theorem cell23_1959778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1959778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959778 prefixEnd_1959778 := by exact prefixLift 1959778
  have htrace : WordTrace (prefixWord ++ tailWord_1959778) baseStart_1959778 baseEnd_1959778 := by
    simpa [prefixWord, tailWord_1959778, baseEnd_1959778] using wordTrace_append hprefix tailTrace_1959778
  have hstable : (prefixWord ++ tailWord_1959778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959778).length < 2 ^ (prefixWord ++ tailWord_1959778).sum := by decide
  have hdescent : baseEnd_1959778 < baseStart_1959778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959808 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_1959808 : Nat := 118140960795 + 1959808 * 2 ^ 59
def prefixEnd_1959808 : Nat := 4983230072969 + 3 ^ 40 * 1959808 * 2
def baseEnd_1959808 : Nat := 335441164842257825295671

theorem tailTrace_1959808 : CollatzResearch.WordTrace tailWord_1959808 prefixEnd_1959808 335441164842257825295671 := by
  unfold tailWord_1959808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35740035041978899702000039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47653380055971866269333385 35740035041978899702000039)
  ·
    refine ⟨53610052562968349553000059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35740035041978899702000039 53610052562968349553000059)
    ·
      refine ⟨80415078844452524329500089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53610052562968349553000059 80415078844452524329500089)
      ·
        refine ⟨60311309133339393247125067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80415078844452524329500089 60311309133339393247125067)
        ·
          refine ⟨90466963700009089870687601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60311309133339393247125067 90466963700009089870687601)
          ·
            refine ⟨67850222775006817403015701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90466963700009089870687601 67850222775006817403015701)
            ·
              refine ⟨3180479192578444565766361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67850222775006817403015701 3180479192578444565766361)
              ·
                refine ⟨2385359394433833424324771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180479192578444565766361 2385359394433833424324771)
                ·
                  refine ⟨3578039091650750136487157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385359394433833424324771 3578039091650750136487157)
                  ·
                    refine ⟨335441164842257825295671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3578039091650750136487157 335441164842257825295671)
                    ·
                      rfl

theorem cell23_1959808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_1959808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959808 prefixEnd_1959808 := by exact prefixLift 1959808
  have htrace : WordTrace (prefixWord ++ tailWord_1959808) baseStart_1959808 baseEnd_1959808 := by
    simpa [prefixWord, tailWord_1959808, baseEnd_1959808] using wordTrace_append hprefix tailTrace_1959808
  have hstable : (prefixWord ++ tailWord_1959808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959808).length < 2 ^ (prefixWord ++ tailWord_1959808).sum := by decide
  have hdescent : baseEnd_1959808 < baseStart_1959808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959839 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 3, 1, 3]
def baseStart_1959839 : Nat := 118140960795 + 1959839 * 2 ^ 59
def prefixEnd_1959839 : Nat := 4983230072969 + 3 ^ 40 * 1959839 * 2
def baseEnd_1959839 : Nat := 1006339412427062854599371

theorem tailTrace_1959839 : CollatzResearch.WordTrace tailWord_1959839 prefixEnd_1959839 1006339412427062854599371 := by
  unfold tailWord_1959839
  simp only [CollatzResearch.WordTrace]
  refine ⟨71481200746845491698378571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47654133831230327798919047 71481200746845491698378571)
  ·
    refine ⟨107221801120268237547567857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71481200746845491698378571 107221801120268237547567857)
    ·
      refine ⟨80416350840201178160675893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107221801120268237547567857 80416350840201178160675893)
      ·
        refine ⟨7539032891268860452563365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80416350840201178160675893 7539032891268860452563365)
        ·
          refine ⟨1413568667112911334855631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7539032891268860452563365 1413568667112911334855631)
          ·
            refine ⟨2120353000669367002283447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413568667112911334855631 2120353000669367002283447)
            ·
              refine ⟨3180529501004050503425171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120353000669367002283447 3180529501004050503425171)
              ·
                refine ⟨4770794251506075755137757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180529501004050503425171 4770794251506075755137757)
                ·
                  refine ⟨1789047844314778408176659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4770794251506075755137757 1789047844314778408176659)
                  ·
                    refine ⟨2683571766472167612264989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1789047844314778408176659 2683571766472167612264989)
                    ·
                      refine ⟨1006339412427062854599371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2683571766472167612264989 1006339412427062854599371)
                      ·
                        rfl

theorem cell23_1959839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_1959839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959839 prefixEnd_1959839 := by exact prefixLift 1959839
  have htrace : WordTrace (prefixWord ++ tailWord_1959839) baseStart_1959839 baseEnd_1959839 := by
    simpa [prefixWord, tailWord_1959839, baseEnd_1959839] using wordTrace_append hprefix tailTrace_1959839
  have hstable : (prefixWord ++ tailWord_1959839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959839).length < 2 ^ (prefixWord ++ tailWord_1959839).sum := by decide
  have hdescent : baseEnd_1959839 < baseStart_1959839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959905 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_1959905 : Nat := 118140960795 + 1959905 * 2 ^ 59
def prefixEnd_1959905 : Nat := 4983230072969 + 3 ^ 40 * 1959905 * 2
def baseEnd_1959905 : Nat := 1006373302150259596374067

theorem tailTrace_1959905 : CollatzResearch.WordTrace tailWord_1959905 prefixEnd_1959905 1006373302150259596374067 := by
  unfold tailWord_1959905
  simp only [CollatzResearch.WordTrace]
  refine ⟨71483607964606384970281169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47655738643070923313520779 71483607964606384970281169)
  ·
    refine ⟨53612705973454788727710877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71483607964606384970281169 53612705973454788727710877)
    ·
      refine ⟨20104764740045545772891579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53612705973454788727710877 20104764740045545772891579)
      ·
        refine ⟨30157147110068318659337369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20104764740045545772891579 30157147110068318659337369)
        ·
          refine ⟨22617860332551238994503027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30157147110068318659337369 22617860332551238994503027)
          ·
            refine ⟨33926790498826858491754541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22617860332551238994503027 33926790498826858491754541)
            ·
              refine ⟨12722546437060071934407953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33926790498826858491754541 12722546437060071934407953)
              ·
                refine ⟨9541909827795053950805965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12722546437060071934407953 9541909827795053950805965)
                ·
                  refine ⟨3578216185423145231552237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9541909827795053950805965 3578216185423145231552237)
                  ·
                    refine ⟨1341831069533679461832089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578216185423145231552237 1341831069533679461832089)
                    ·
                      refine ⟨1006373302150259596374067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341831069533679461832089 1006373302150259596374067)
                      ·
                        rfl

theorem cell23_1959905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_1959905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959905 prefixEnd_1959905 := by exact prefixLift 1959905
  have htrace : WordTrace (prefixWord ++ tailWord_1959905) baseStart_1959905 baseEnd_1959905 := by
    simpa [prefixWord, tailWord_1959905, baseEnd_1959905] using wordTrace_append hprefix tailTrace_1959905
  have hstable : (prefixWord ++ tailWord_1959905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959905).length < 2 ^ (prefixWord ++ tailWord_1959905).sum := by decide
  have hdescent : baseEnd_1959905 < baseStart_1959905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959946 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_1959946 : Nat := 118140960795 + 1959946 * 2 ^ 59
def prefixEnd_1959946 : Nat := 4983230072969 + 3 ^ 40 * 1959946 * 2
def baseEnd_1959946 : Nat := 1006394354857093935961379

theorem tailTrace_1959946 : CollatzResearch.WordTrace tailWord_1959946 prefixEnd_1959946 1006394354857093935961379 := by
  unfold tailWord_1959946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17871275839364462243130923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47656735571638565981682461 17871275839364462243130923)
  ·
    refine ⟨26806913759046693364696385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17871275839364462243130923 26806913759046693364696385)
    ·
      refine ⟨20105185319285020023522289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26806913759046693364696385 20105185319285020023522289)
      ·
        refine ⟨15078888989463765017641717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20105185319285020023522289 15078888989463765017641717)
        ·
          refine ⟨1413645842762227970403911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15078888989463765017641717 1413645842762227970403911)
          ·
            refine ⟨2120468764143341955605867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413645842762227970403911 2120468764143341955605867)
            ·
              refine ⟨3180703146215012933408801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120468764143341955605867 3180703146215012933408801)
              ·
                refine ⟨2385527359661259700056601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180703146215012933408801 2385527359661259700056601)
                ·
                  refine ⟨1789145519745944775042451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385527359661259700056601 1789145519745944775042451)
                  ·
                    refine ⟨2683718279618917162563677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1789145519745944775042451 2683718279618917162563677)
                    ·
                      refine ⟨1006394354857093935961379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2683718279618917162563677 1006394354857093935961379)
                      ·
                        rfl

theorem cell23_1959946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_1959946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959946 prefixEnd_1959946 := by exact prefixLift 1959946
  have htrace : WordTrace (prefixWord ++ tailWord_1959946) baseStart_1959946 baseEnd_1959946 := by
    simpa [prefixWord, tailWord_1959946, baseEnd_1959946] using wordTrace_append hprefix tailTrace_1959946
  have hstable : (prefixWord ++ tailWord_1959946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959946).length < 2 ^ (prefixWord ++ tailWord_1959946).sum := by decide
  have hdescent : baseEnd_1959946 < baseStart_1959946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959948 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1959948 : Nat := 118140960795 + 1959948 * 2 ^ 59
def prefixEnd_1959948 : Nat := 4983230072969 + 3 ^ 40 * 1959948 * 2
def baseEnd_1959948 : Nat := 1006395381818402928136369

theorem tailTrace_1959948 : CollatzResearch.WordTrace tailWord_1959948 prefixEnd_1959948 1006395381818402928136369 := by
  unfold tailWord_1959948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35742588151725301657048249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47656784202300402209397665 35742588151725301657048249)
  ·
    refine ⟨26806941113793976242786187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35742588151725301657048249 26806941113793976242786187)
    ·
      refine ⟨40210411670690964364179281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26806941113793976242786187 40210411670690964364179281)
      ·
        refine ⟨30157808753018223273134461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40210411670690964364179281 30157808753018223273134461)
        ·
          refine ⟨11309178282381833727425423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30157808753018223273134461 11309178282381833727425423)
          ·
            refine ⟨16963767423572750591138135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11309178282381833727425423 16963767423572750591138135)
            ·
              refine ⟨25445651135359125886707203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16963767423572750591138135 25445651135359125886707203)
              ·
                refine ⟨38168476703038688830060805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25445651135359125886707203 38168476703038688830060805)
                ·
                  refine ⟨7156589381819754155636401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38168476703038688830060805 7156589381819754155636401)
                  ·
                    refine ⟨5367442036364815616727301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156589381819754155636401 5367442036364815616727301)
                    ·
                      refine ⟨1006395381818402928136369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5367442036364815616727301 1006395381818402928136369)
                      ·
                        rfl

theorem cell23_1959948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1959948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959948 prefixEnd_1959948 := by exact prefixLift 1959948
  have htrace : WordTrace (prefixWord ++ tailWord_1959948) baseStart_1959948 baseEnd_1959948 := by
    simpa [prefixWord, tailWord_1959948, baseEnd_1959948] using wordTrace_append hprefix tailTrace_1959948
  have hstable : (prefixWord ++ tailWord_1959948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959948).length < 2 ^ (prefixWord ++ tailWord_1959948).sum := by decide
  have hdescent : baseEnd_1959948 < baseStart_1959948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959965 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1959965 : Nat := 118140960795 + 1959965 * 2 ^ 59
def prefixEnd_1959965 : Nat := 4983230072969 + 3 ^ 40 * 1959965 * 2
def baseEnd_1959965 : Nat := 1006404110989529361623791

theorem tailTrace_1959965 : CollatzResearch.WordTrace tailWord_1959965 prefixEnd_1959965 1006404110989529361623791 := by
  unfold tailWord_1959965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71485796344389015217465349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47657197562926010144976899 71485796344389015217465349)
  ·
    refine ⟨13403586814572940353274753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71485796344389015217465349 13403586814572940353274753)
    ·
      refine ⟨10052690110929705264956065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13403586814572940353274753 10052690110929705264956065)
      ·
        refine ⟨7539517583197278948717049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10052690110929705264956065 7539517583197278948717049)
        ·
          refine ⟨5654638187397959211537787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7539517583197278948717049 5654638187397959211537787)
          ·
            refine ⟨8481957281096938817306681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654638187397959211537787 8481957281096938817306681)
            ·
              refine ⟨6361467960822704112980011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481957281096938817306681 6361467960822704112980011)
              ·
                refine ⟨9542201941234056169470017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361467960822704112980011 9542201941234056169470017)
                ·
                  refine ⟨7156651455925542127102513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9542201941234056169470017 7156651455925542127102513)
                  ·
                    refine ⟨5367488591944156595326885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156651455925542127102513 5367488591944156595326885)
                    ·
                      refine ⟨1006404110989529361623791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5367488591944156595326885 1006404110989529361623791)
                      ·
                        rfl

theorem cell23_1959965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1959965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959965 prefixEnd_1959965 := by exact prefixLift 1959965
  have htrace : WordTrace (prefixWord ++ tailWord_1959965) baseStart_1959965 baseEnd_1959965 := by
    simpa [prefixWord, tailWord_1959965, baseEnd_1959965] using wordTrace_append hprefix tailTrace_1959965
  have hstable : (prefixWord ++ tailWord_1959965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959965).length < 2 ^ (prefixWord ++ tailWord_1959965).sum := by decide
  have hdescent : baseEnd_1959965 < baseStart_1959965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959969 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1959969 : Nat := 118140960795 + 1959969 * 2 ^ 59
def prefixEnd_1959969 : Nat := 4983230072969 + 3 ^ 40 * 1959969 * 2
def baseEnd_1959969 : Nat := 1006406164912147345973773

theorem tailTrace_1959969 : CollatzResearch.WordTrace tailWord_1959969 prefixEnd_1959969 1006406164912147345973773 := by
  unfold tailWord_1959969
  simp only [CollatzResearch.WordTrace]
  refine ⟨71485942236374523900610961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47657294824249682600407307 71485942236374523900610961)
  ·
    refine ⟨53614456677280892925458221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71485942236374523900610961 53614456677280892925458221)
    ·
      refine ⟨20105421253980334847046833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53614456677280892925458221 20105421253980334847046833)
      ·
        refine ⟨15079065940485251135285125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20105421253980334847046833 15079065940485251135285125)
        ·
          refine ⟨2827324863840984587865961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15079065940485251135285125 2827324863840984587865961)
          ·
            refine ⟨2120493647880738440899471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827324863840984587865961 2120493647880738440899471)
            ·
              refine ⟨3180740471821107661349207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120493647880738440899471 3180740471821107661349207)
              ·
                refine ⟨4771110707731661492023811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180740471821107661349207 4771110707731661492023811)
                ·
                  refine ⟨7156666061597492238035717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771110707731661492023811 7156666061597492238035717)
                  ·
                    refine ⟨1341874886549529794631697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156666061597492238035717 1341874886549529794631697)
                    ·
                      refine ⟨1006406164912147345973773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341874886549529794631697 1006406164912147345973773)
                      ·
                        rfl

theorem cell23_1959969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1959969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959969 prefixEnd_1959969 := by exact prefixLift 1959969
  have htrace : WordTrace (prefixWord ++ tailWord_1959969) baseStart_1959969 baseEnd_1959969 := by
    simpa [prefixWord, tailWord_1959969, baseEnd_1959969] using wordTrace_append hprefix tailTrace_1959969
  have hstable : (prefixWord ++ tailWord_1959969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959969).length < 2 ^ (prefixWord ++ tailWord_1959969).sum := by decide
  have hdescent : baseEnd_1959969 < baseStart_1959969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960008 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1960008 : Nat := 118140960795 + 1960008 * 2 ^ 59
def prefixEnd_1960008 : Nat := 4983230072969 + 3 ^ 40 * 1960008 * 2
def baseEnd_1960008 : Nat := 1006426190657672693386093

theorem tailTrace_1960008 : CollatzResearch.WordTrace tailWord_1960008 prefixEnd_1960008 1006426190657672693386093 := by
  unfold tailWord_1960008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35743682341616616780640339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47658243122155489040853785 35743682341616616780640339)
  ·
    refine ⟨53615523512424925170960509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35743682341616616780640339 53615523512424925170960509)
    ·
      refine ⟨20105821317159346939110191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53615523512424925170960509 20105821317159346939110191)
      ·
        refine ⟨30158731975739020408665287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20105821317159346939110191 30158731975739020408665287)
        ·
          refine ⟨45238097963608530612997931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30158731975739020408665287 45238097963608530612997931)
          ·
            refine ⟨67857146945412795919496897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45238097963608530612997931 67857146945412795919496897)
            ·
              refine ⟨50892860209059596939622673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67857146945412795919496897 50892860209059596939622673)
              ·
                refine ⟨38169645156794697704717005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50892860209059596939622673 38169645156794697704717005)
                ·
                  refine ⟨14313616933798011639268877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38169645156794697704717005 14313616933798011639268877)
                  ·
                    refine ⟨5367606350174254364725829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14313616933798011639268877 5367606350174254364725829)
                    ·
                      refine ⟨1006426190657672693386093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5367606350174254364725829 1006426190657672693386093)
                      ·
                        rfl

theorem cell23_1960008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1960008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960008 prefixEnd_1960008 := by exact prefixLift 1960008
  have htrace : WordTrace (prefixWord ++ tailWord_1960008) baseStart_1960008 baseEnd_1960008 := by
    simpa [prefixWord, tailWord_1960008, baseEnd_1960008] using wordTrace_append hprefix tailTrace_1960008
  have hstable : (prefixWord ++ tailWord_1960008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960008).length < 2 ^ (prefixWord ++ tailWord_1960008).sum := by decide
  have hdescent : baseEnd_1960008 < baseStart_1960008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960025 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 6, 2]
def baseStart_1960025 : Nat := 118140960795 + 1960025 * 2 ^ 59
def prefixEnd_1960025 : Nat := 4983230072969 + 3 ^ 40 * 1960025 * 2
def baseEnd_1960025 : Nat := 1006434919828799126873515

theorem tailTrace_1960025 : CollatzResearch.WordTrace tailWord_1960025 prefixEnd_1960025 1006434919828799126873515 := by
  unfold tailWord_1960025
  simp only [CollatzResearch.WordTrace]
  refine ⟨71487984724171645464649529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47658656482781096976433019 71487984724171645464649529)
  ·
    refine ⟨53615988543128734098487147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71487984724171645464649529 53615988543128734098487147)
    ·
      refine ⟨80423982814693101147730721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53615988543128734098487147 80423982814693101147730721)
      ·
        refine ⟨60317987111019825860798041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80423982814693101147730721 60317987111019825860798041)
        ·
          refine ⟨45238490333264869395598531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60317987111019825860798041 45238490333264869395598531)
          ·
            refine ⟨67857735499897304093397797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45238490333264869395598531 67857735499897304093397797)
            ·
              refine ⟨12723325406230744517512087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67857735499897304093397797 12723325406230744517512087)
              ·
                refine ⟨19084988109346116776268131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12723325406230744517512087 19084988109346116776268131)
                ·
                  refine ⟨28627482164019175164402197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19084988109346116776268131 28627482164019175164402197)
                  ·
                    refine ⟨1341913226438398835831353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28627482164019175164402197 1341913226438398835831353)
                    ·
                      refine ⟨1006434919828799126873515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1341913226438398835831353 1006434919828799126873515)
                      ·
                        rfl

theorem cell23_1960025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_1960025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960025 prefixEnd_1960025 := by exact prefixLift 1960025
  have htrace : WordTrace (prefixWord ++ tailWord_1960025) baseStart_1960025 baseEnd_1960025 := by
    simpa [prefixWord, tailWord_1960025, baseEnd_1960025] using wordTrace_append hprefix tailTrace_1960025
  have hstable : (prefixWord ++ tailWord_1960025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960025).length < 2 ^ (prefixWord ++ tailWord_1960025).sum := by decide
  have hdescent : baseEnd_1960025 < baseStart_1960025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960035 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 3, 4]
def baseStart_1960035 : Nat := 118140960795 + 1960035 * 2 ^ 59
def prefixEnd_1960035 : Nat := 4983230072969 + 3 ^ 40 * 1960035 * 2
def baseEnd_1960035 : Nat := 335480018211781362582823

theorem tailTrace_1960035 : CollatzResearch.WordTrace tailWord_1960035 prefixEnd_1960035 335480018211781362582823 := by
  unfold tailWord_1960035
  simp only [CollatzResearch.WordTrace]
  refine ⟨71488349454135417172513559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47658899636090278115009039 71488349454135417172513559)
  ·
    refine ⟨107232524181203125758770339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71488349454135417172513559 107232524181203125758770339)
    ·
      refine ⟨160848786271804688638155509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107232524181203125758770339 160848786271804688638155509)
      ·
        refine ⟨15079573712981689559827079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160848786271804688638155509 15079573712981689559827079)
        ·
          refine ⟨22619360569472534339740619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15079573712981689559827079 22619360569472534339740619)
          ·
            refine ⟨33929040854208801509610929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22619360569472534339740619 33929040854208801509610929)
            ·
              refine ⟨25446780640656601132208197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33929040854208801509610929 25446780640656601132208197)
              ·
                refine ⟨4771271370123112712289037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25446780640656601132208197 4771271370123112712289037)
                ·
                  refine ⟨1789226763796167267108389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4771271370123112712289037 1789226763796167267108389)
                  ·
                    refine ⟨335480018211781362582823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789226763796167267108389 335480018211781362582823)
                    ·
                      rfl

theorem cell23_1960035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 4].length) (baseStart_1960035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960035 prefixEnd_1960035 := by exact prefixLift 1960035
  have htrace : WordTrace (prefixWord ++ tailWord_1960035) baseStart_1960035 baseEnd_1960035 := by
    simpa [prefixWord, tailWord_1960035, baseEnd_1960035] using wordTrace_append hprefix tailTrace_1960035
  have hstable : (prefixWord ++ tailWord_1960035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960035).length < 2 ^ (prefixWord ++ tailWord_1960035).sum := by decide
  have hdescent : baseEnd_1960035 < baseStart_1960035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960069 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_1960069 : Nat := 118140960795 + 1960069 * 2 ^ 59
def prefixEnd_1960069 : Nat := 4983230072969 + 3 ^ 40 * 1960069 * 2
def baseEnd_1960069 : Nat := 335485837659198984907771

theorem tailTrace_1960069 : CollatzResearch.WordTrace tailWord_1960069 prefixEnd_1960069 335485837659198984907771 := by
  unfold tailWord_1960069
  simp only [CollatzResearch.WordTrace]
  refine ⟨71489589536012240979251261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47659726357341493986167507 71489589536012240979251261)
  ·
    refine ⟨26808596076004590367219223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71489589536012240979251261 26808596076004590367219223)
    ·
      refine ⟨40212894114006885550828835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26808596076004590367219223 40212894114006885550828835)
      ·
        refine ⟨60319341171010328326243253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40212894114006885550828835 60319341171010328326243253)
        ·
          refine ⟨5654938234782218280585305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60319341171010328326243253 5654938234782218280585305)
          ·
            refine ⟨4241203676086663710438979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5654938234782218280585305 4241203676086663710438979)
            ·
              refine ⟨6361805514129995565658469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241203676086663710438979 6361805514129995565658469)
              ·
                refine ⟨1192838533899374168560963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6361805514129995565658469 1192838533899374168560963)
                ·
                  refine ⟨1789257800849061252841445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192838533899374168560963 1789257800849061252841445)
                  ·
                    refine ⟨335485837659198984907771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789257800849061252841445 335485837659198984907771)
                    ·
                      rfl

theorem cell23_1960069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_1960069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960069 prefixEnd_1960069 := by exact prefixLift 1960069
  have htrace : WordTrace (prefixWord ++ tailWord_1960069) baseStart_1960069 baseEnd_1960069 := by
    simpa [prefixWord, tailWord_1960069, baseEnd_1960069] using wordTrace_append hprefix tailTrace_1960069
  have hstable : (prefixWord ++ tailWord_1960069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960069).length < 2 ^ (prefixWord ++ tailWord_1960069).sum := by decide
  have hdescent : baseEnd_1960069 < baseStart_1960069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960108 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1960108 : Nat := 118140960795 + 1960108 * 2 ^ 59
def prefixEnd_1960108 : Nat := 4983230072969 + 3 ^ 40 * 1960108 * 2
def baseEnd_1960108 : Nat := 335492512907707434045211

theorem tailTrace_1960108 : CollatzResearch.WordTrace tailWord_1960108 prefixEnd_1960108 335492512907707434045211 := by
  unfold tailWord_1960108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35745505991435475319960489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47660674655247300426613985 35745505991435475319960489)
  ·
    refine ⟨26809129493576606489970367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35745505991435475319960489 26809129493576606489970367)
    ·
      refine ⟨40213694240364909734955551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26809129493576606489970367 40213694240364909734955551)
      ·
        refine ⟨60320541360547364602433327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40213694240364909734955551 60320541360547364602433327)
        ·
          refine ⟨90480812040821046903649991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60320541360547364602433327 90480812040821046903649991)
          ·
            refine ⟨135721218061231570355474987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90480812040821046903649991 135721218061231570355474987)
            ·
              refine ⟨203581827091847355533212481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135721218061231570355474987 203581827091847355533212481)
              ·
                refine ⟨152686370318885516649909361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203581827091847355533212481 152686370318885516649909361)
                ·
                  refine ⟨114514777739164137487432021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152686370318885516649909361 114514777739164137487432021)
                  ·
                    refine ⟨335492512907707434045211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 114514777739164137487432021 335492512907707434045211)
                    ·
                      rfl

theorem cell23_1960108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1960108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960108 prefixEnd_1960108 := by exact prefixLift 1960108
  have htrace : WordTrace (prefixWord ++ tailWord_1960108) baseStart_1960108 baseEnd_1960108 := by
    simpa [prefixWord, tailWord_1960108, baseEnd_1960108] using wordTrace_append hprefix tailTrace_1960108
  have hstable : (prefixWord ++ tailWord_1960108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960108).length < 2 ^ (prefixWord ++ tailWord_1960108).sum := by decide
  have hdescent : baseEnd_1960108 < baseStart_1960108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960116 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 8]
def baseStart_1960116 : Nat := 118140960795 + 1960116 * 2 ^ 59
def prefixEnd_1960116 : Nat := 4983230072969 + 3 ^ 40 * 1960116 * 2
def baseEnd_1960116 : Nat := 111831294063150918981733

theorem tailTrace_1960116 : CollatzResearch.WordTrace tailWord_1960116 prefixEnd_1960116 111831294063150918981733 := by
  unfold tailWord_1960116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35745651883420984003106101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47660869177894645337474801 35745651883420984003106101)
  ·
    refine ⟨3351154864070717250291197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35745651883420984003106101 3351154864070717250291197)
    ·
      refine ⟨1256683074026518968859199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3351154864070717250291197 1256683074026518968859199)
      ·
        refine ⟨1885024611039778453288799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256683074026518968859199 1885024611039778453288799)
        ·
          refine ⟨2827536916559667679933199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885024611039778453288799 2827536916559667679933199)
          ·
            refine ⟨4241305374839501519899799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827536916559667679933199 4241305374839501519899799)
            ·
              refine ⟨6361958062259252279849699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241305374839501519899799 6361958062259252279849699)
              ·
                refine ⟨9542937093388878419774549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361958062259252279849699 9542937093388878419774549)
                ·
                  refine ⟨111831294063150918981733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9542937093388878419774549 111831294063150918981733)
                  ·
                    rfl

theorem cell23_1960116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_1960116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960116 prefixEnd_1960116 := by exact prefixLift 1960116
  have htrace : WordTrace (prefixWord ++ tailWord_1960116) baseStart_1960116 baseEnd_1960116 := by
    simpa [prefixWord, tailWord_1960116, baseEnd_1960116] using wordTrace_append hprefix tailTrace_1960116
  have hstable : (prefixWord ++ tailWord_1960116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960116).length < 2 ^ (prefixWord ++ tailWord_1960116).sum := by decide
  have hdescent : baseEnd_1960116 < baseStart_1960116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960126 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1960126 : Nat := 118140960795 + 1960126 * 2 ^ 59
def prefixEnd_1960126 : Nat := 4983230072969 + 3 ^ 40 * 1960126 * 2
def baseEnd_1960126 : Nat := 1006486781374903231710551

theorem tailTrace_1960126 : CollatzResearch.WordTrace tailWord_1960126 prefixEnd_1960126 1006486781374903231710551 := by
  unfold tailWord_1960126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936458562100717464259529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47661112331203826476050821 8936458562100717464259529)
  ·
    refine ⟨6702343921575538098194647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8936458562100717464259529 6702343921575538098194647)
    ·
      refine ⟨10053515882363307147291971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702343921575538098194647 10053515882363307147291971)
      ·
        refine ⟨15080273823544960720937957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053515882363307147291971 15080273823544960720937957)
        ·
          refine ⟨2827551341914680135175867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15080273823544960720937957 2827551341914680135175867)
          ·
            refine ⟨4241327012872020202763801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827551341914680135175867 4241327012872020202763801)
            ·
              refine ⟨3180995259654015152072851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241327012872020202763801 3180995259654015152072851)
              ·
                refine ⟨4771492889481022728109277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180995259654015152072851 4771492889481022728109277)
                ·
                  refine ⟨1789309833555383523040979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4771492889481022728109277 1789309833555383523040979)
                  ·
                    refine ⟨2683964750333075284561469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1789309833555383523040979 2683964750333075284561469)
                    ·
                      refine ⟨1006486781374903231710551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2683964750333075284561469 1006486781374903231710551)
                      ·
                        rfl

theorem cell23_1960126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1960126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960126 prefixEnd_1960126 := by exact prefixLift 1960126
  have htrace : WordTrace (prefixWord ++ tailWord_1960126) baseStart_1960126 baseEnd_1960126 := by
    simpa [prefixWord, tailWord_1960126, baseEnd_1960126] using wordTrace_append hprefix tailTrace_1960126
  have hstable : (prefixWord ++ tailWord_1960126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960126).length < 2 ^ (prefixWord ++ tailWord_1960126).sum := by decide
  have hdescent : baseEnd_1960126 < baseStart_1960126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960142 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1960142 : Nat := 118140960795 + 1960142 * 2 ^ 59
def prefixEnd_1960142 : Nat := 4983230072969 + 3 ^ 40 * 1960142 * 2
def baseEnd_1960142 : Nat := 335498332355125056370159

theorem tailTrace_1960142 : CollatzResearch.WordTrace tailWord_1960142 prefixEnd_1960142 335498332355125056370159 := by
  unfold tailWord_1960142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936531508093471805832335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47661501376498516297772453 8936531508093471805832335)
  ·
    refine ⟨13404797262140207708748503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936531508093471805832335 13404797262140207708748503)
    ·
      refine ⟨20107195893210311563122755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13404797262140207708748503 20107195893210311563122755)
      ·
        refine ⟨30160793839815467344684133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107195893210311563122755 30160793839815467344684133)
        ·
          refine ⟨5655148844965400127128275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30160793839815467344684133 5655148844965400127128275)
          ·
            refine ⟨8482723267448100190692413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655148844965400127128275 8482723267448100190692413)
            ·
              refine ⟨3181021225293037571509655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8482723267448100190692413 3181021225293037571509655)
              ·
                refine ⟨4771531837939556357264483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181021225293037571509655 4771531837939556357264483)
                ·
                  refine ⟨7157297756909334535896725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771531837939556357264483 7157297756909334535896725)
                  ·
                    refine ⟨335498332355125056370159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7157297756909334535896725 335498332355125056370159)
                    ·
                      rfl

theorem cell23_1960142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1960142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960142 prefixEnd_1960142 := by exact prefixLift 1960142
  have htrace : WordTrace (prefixWord ++ tailWord_1960142) baseStart_1960142 baseEnd_1960142 := by
    simpa [prefixWord, tailWord_1960142, baseEnd_1960142] using wordTrace_append hprefix tailTrace_1960142
  have hstable : (prefixWord ++ tailWord_1960142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960142).length < 2 ^ (prefixWord ++ tailWord_1960142).sum := by decide
  have hdescent : baseEnd_1960142 < baseStart_1960142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960209 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_1960209 : Nat := 118140960795 + 1960209 * 2 ^ 59
def prefixEnd_1960209 : Nat := 4983230072969 + 3 ^ 40 * 1960209 * 2
def baseEnd_1960209 : Nat := 1006529400269226406972669

theorem tailTrace_1960209 : CollatzResearch.WordTrace tailWord_1960209 prefixEnd_1960209 1006529400269226406972669 := by
  unfold tailWord_1960209
  simp only [CollatzResearch.WordTrace]
  refine ⟨71494695755505044889347681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47663130503670029926231787 71494695755505044889347681)
  ·
    refine ⟨53621021816628783667010761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71494695755505044889347681 53621021816628783667010761)
    ·
      refine ⟨40215766362471587750258071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53621021816628783667010761 40215766362471587750258071)
      ·
        refine ⟨60323649543707381625387107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40215766362471587750258071 60323649543707381625387107)
        ·
          refine ⟨90485474315561072438080661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60323649543707381625387107 90485474315561072438080661)
          ·
            refine ⟨4241506608541925270535031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90485474315561072438080661 4241506608541925270535031)
            ·
              refine ⟨6362259912812887905802547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241506608541925270535031 6362259912812887905802547)
              ·
                refine ⟨9543389869219331858703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362259912812887905802547 9543389869219331858703821)
                ·
                  refine ⟨3578771200957249447013933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9543389869219331858703821 3578771200957249447013933)
                  ·
                    refine ⟨1342039200358968542630225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578771200957249447013933 1342039200358968542630225)
                    ·
                      refine ⟨1006529400269226406972669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342039200358968542630225 1006529400269226406972669)
                      ·
                        rfl

theorem cell23_1960209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_1960209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960209 prefixEnd_1960209 := by exact prefixLift 1960209
  have htrace : WordTrace (prefixWord ++ tailWord_1960209) baseStart_1960209 baseEnd_1960209 := by
    simpa [prefixWord, tailWord_1960209, baseEnd_1960209] using wordTrace_append hprefix tailTrace_1960209
  have hstable : (prefixWord ++ tailWord_1960209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960209).length < 2 ^ (prefixWord ++ tailWord_1960209).sum := by decide
  have hdescent : baseEnd_1960209 < baseStart_1960209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960234 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1960234 : Nat := 118140960795 + 1960234 * 2 ^ 59
def prefixEnd_1960234 : Nat := 4983230072969 + 3 ^ 40 * 1960234 * 2
def baseEnd_1960234 : Nat := 1006542237285588809160055

theorem tailTrace_1960234 : CollatzResearch.WordTrace tailWord_1960234 prefixEnd_1960234 1006542237285588809160055 := by
  unfold tailWord_1960234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873901895103618539751939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47663738386942982772671837 17873901895103618539751939)
  ·
    refine ⟨26810852842655427809627909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17873901895103618539751939 26810852842655427809627909)
    ·
      refine ⟨5027034907997892714305233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26810852842655427809627909 5027034907997892714305233)
      ·
        refine ⟨3770276180998419535728925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5027034907997892714305233 3770276180998419535728925)
        ·
          refine ⟨1413853567874407325898347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3770276180998419535728925 1413853567874407325898347)
          ·
            refine ⟨2120780351811610988847521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413853567874407325898347 2120780351811610988847521)
            ·
              refine ⟨1590585263858708241635641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120780351811610988847521 1590585263858708241635641)
              ·
                refine ⟨1192938947894031181226731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590585263858708241635641 1192938947894031181226731)
                ·
                  refine ⟨1789408421841046771840097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192938947894031181226731 1789408421841046771840097)
                  ·
                    refine ⟨1342056316380785078880073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1789408421841046771840097 1342056316380785078880073)
                    ·
                      refine ⟨1006542237285588809160055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342056316380785078880073 1006542237285588809160055)
                      ·
                        rfl

theorem cell23_1960234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1960234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960234 prefixEnd_1960234 := by exact prefixLift 1960234
  have htrace : WordTrace (prefixWord ++ tailWord_1960234) baseStart_1960234 baseEnd_1960234 := by
    simpa [prefixWord, tailWord_1960234, baseEnd_1960234] using wordTrace_append hprefix tailTrace_1960234
  have hstable : (prefixWord ++ tailWord_1960234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960234).length < 2 ^ (prefixWord ++ tailWord_1960234).sum := by decide
  have hdescent : baseEnd_1960234 < baseStart_1960234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960239 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 4, 2, 2]
def baseStart_1960239 : Nat := 118140960795 + 1960239 * 2 ^ 59
def prefixEnd_1960239 : Nat := 4983230072969 + 3 ^ 40 * 1960239 * 2
def baseEnd_1960239 : Nat := 1006544804688861289597531

theorem tailTrace_1960239 : CollatzResearch.WordTrace tailWord_1960239 prefixEnd_1960239 1006544804688861289597531 := by
  unfold tailWord_1960239
  simp only [CollatzResearch.WordTrace]
  refine ⟨71495789945396360012939771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47663859963597573341959847 71495789945396360012939771)
  ·
    refine ⟨107243684918094540019409657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71495789945396360012939771 107243684918094540019409657)
    ·
      refine ⟨80432763688570905014557243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107243684918094540019409657 80432763688570905014557243)
      ·
        refine ⟨120649145532856357521835865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80432763688570905014557243 120649145532856357521835865)
        ·
          refine ⟨90486859149642268141376899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120649145532856357521835865 90486859149642268141376899)
          ·
            refine ⟨135730288724463402212065349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90486859149642268141376899 135730288724463402212065349)
            ·
              refine ⟨25449429135836887914762253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135730288724463402212065349 25449429135836887914762253)
              ·
                refine ⟨9543535925938832968035845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25449429135836887914762253 9543535925938832968035845)
                ·
                  refine ⟨1789412986113531181506721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9543535925938832968035845 1789412986113531181506721)
                  ·
                    refine ⟨1342059739585148386130041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1789412986113531181506721 1342059739585148386130041)
                    ·
                      refine ⟨1006544804688861289597531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342059739585148386130041 1006544804688861289597531)
                      ·
                        rfl

theorem cell23_1960239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2, 2].length) (baseStart_1960239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960239 prefixEnd_1960239 := by exact prefixLift 1960239
  have htrace : WordTrace (prefixWord ++ tailWord_1960239) baseStart_1960239 baseEnd_1960239 := by
    simpa [prefixWord, tailWord_1960239, baseEnd_1960239] using wordTrace_append hprefix tailTrace_1960239
  have hstable : (prefixWord ++ tailWord_1960239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960239).length < 2 ^ (prefixWord ++ tailWord_1960239).sum := by decide
  have hdescent : baseEnd_1960239 < baseStart_1960239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960252 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1960252 : Nat := 118140960795 + 1960252 * 2 ^ 59
def prefixEnd_1960252 : Nat := 4983230072969 + 3 ^ 40 * 1960252 * 2
def baseEnd_1960252 : Nat := 1006551479937369738734971

theorem tailTrace_1960252 : CollatzResearch.WordTrace tailWord_1960252 prefixEnd_1960252 1006551479937369738734971 := by
  unfold tailWord_1960252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35748132047174631616581505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47664176062899508822108673 35748132047174631616581505)
  ·
    refine ⟨26811099035380973712436129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35748132047174631616581505 26811099035380973712436129)
    ·
      refine ⟨20108324276535730284327097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26811099035380973712436129 20108324276535730284327097)
      ·
        refine ⟨15081243207401797713245323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20108324276535730284327097 15081243207401797713245323)
        ·
          refine ⟨22621864811102696569867985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081243207401797713245323 22621864811102696569867985)
          ·
            refine ⟨16966398608327022427400989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22621864811102696569867985 16966398608327022427400989)
            ·
              refine ⟨6362399478122633410275371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16966398608327022427400989 6362399478122633410275371)
              ·
                refine ⟨9543599217183950115413057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362399478122633410275371 9543599217183950115413057)
                ·
                  refine ⟨7157699412887962586559793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543599217183950115413057 7157699412887962586559793)
                  ·
                    refine ⟨5368274559665971939919845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157699412887962586559793 5368274559665971939919845)
                    ·
                      refine ⟨1006551479937369738734971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5368274559665971939919845 1006551479937369738734971)
                      ·
                        rfl

theorem cell23_1960252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1960252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960252 prefixEnd_1960252 := by exact prefixLift 1960252
  have htrace : WordTrace (prefixWord ++ tailWord_1960252) baseStart_1960252 baseEnd_1960252 := by
    simpa [prefixWord, tailWord_1960252, baseEnd_1960252] using wordTrace_append hprefix tailTrace_1960252
  have hstable : (prefixWord ++ tailWord_1960252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960252).length < 2 ^ (prefixWord ++ tailWord_1960252).sum := by decide
  have hdescent : baseEnd_1960252 < baseStart_1960252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960279 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 5]
def baseStart_1960279 : Nat := 118140960795 + 1960279 * 2 ^ 59
def prefixEnd_1960279 : Nat := 4983230072969 + 3 ^ 40 * 1960279 * 2
def baseEnd_1960279 : Nat := 111840593768337903677483

theorem tailTrace_1960279 : CollatzResearch.WordTrace tailWord_1960279 prefixEnd_1960279 111840593768337903677483 := by
  unfold tailWord_1960279
  simp only [CollatzResearch.WordTrace]
  refine ⟨71497248865251446844395891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47664832576834297896263927 71497248865251446844395891)
  ·
    refine ⟨107245873297877170266593837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71497248865251446844395891 107245873297877170266593837)
    ·
      refine ⟨40217202486703938849972689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107245873297877170266593837 40217202486703938849972689)
      ·
        refine ⟨30162901865027954137479517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40217202486703938849972689 30162901865027954137479517)
        ·
          refine ⟨11311088199385482801554819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30162901865027954137479517 11311088199385482801554819)
          ·
            refine ⟨16966632299078224202332229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311088199385482801554819 16966632299078224202332229)
            ·
              refine ⟨3181243556077167037937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16966632299078224202332229 3181243556077167037937293)
              ·
                refine ⟨1192966333528937639226485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181243556077167037937293 1192966333528937639226485)
                ·
                  refine ⟨111840593768337903677483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192966333528937639226485 111840593768337903677483)
                  ·
                    rfl

theorem cell23_1960279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 5].length) (baseStart_1960279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960279 prefixEnd_1960279 := by exact prefixLift 1960279
  have htrace : WordTrace (prefixWord ++ tailWord_1960279) baseStart_1960279 baseEnd_1960279 := by
    simpa [prefixWord, tailWord_1960279, baseEnd_1960279] using wordTrace_append hprefix tailTrace_1960279
  have hstable : (prefixWord ++ tailWord_1960279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960279).length < 2 ^ (prefixWord ++ tailWord_1960279).sum := by decide
  have hdescent : baseEnd_1960279 < baseStart_1960279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960290 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1960290 : Nat := 118140960795 + 1960290 * 2 ^ 59
def prefixEnd_1960290 : Nat := 4983230072969 + 3 ^ 40 * 1960290 * 2
def baseEnd_1960290 : Nat := 1006570992202240590059797

theorem tailTrace_1960290 : CollatzResearch.WordTrace tailWord_1960290 prefixEnd_1960290 1006570992202240590059797 := by
  unfold tailWord_1960290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874412517052898930761581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47665100045474397148697549 17874412517052898930761581)
  ·
    refine ⟨6702904693894837099035593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17874412517052898930761581 6702904693894837099035593)
    ·
      refine ⟨5027178520421127824276695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6702904693894837099035593 5027178520421127824276695)
      ·
        refine ⟨7540767780631691736415043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5027178520421127824276695 7540767780631691736415043)
        ·
          refine ⟨11311151670947537604622565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540767780631691736415043 11311151670947537604622565)
          ·
            refine ⟨2120840938302663300866731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11311151670947537604622565 2120840938302663300866731)
            ·
              refine ⟨3181261407453994951300097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120840938302663300866731 3181261407453994951300097)
              ·
                refine ⟨2385946055590496213475073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181261407453994951300097 2385946055590496213475073)
                ·
                  refine ⟨1789459541692872160106305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385946055590496213475073 1789459541692872160106305)
                  ·
                    refine ⟨1342094656269654120079729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1789459541692872160106305 1342094656269654120079729)
                    ·
                      refine ⟨1006570992202240590059797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342094656269654120079729 1006570992202240590059797)
                      ·
                        rfl

theorem cell23_1960290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1960290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960290 prefixEnd_1960290 := by exact prefixLift 1960290
  have htrace : WordTrace (prefixWord ++ tailWord_1960290) baseStart_1960290 baseEnd_1960290 := by
    simpa [prefixWord, tailWord_1960290, baseEnd_1960290] using wordTrace_append hprefix tailTrace_1960290
  have hstable : (prefixWord ++ tailWord_1960290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960290).length < 2 ^ (prefixWord ++ tailWord_1960290).sum := by decide
  have hdescent : baseEnd_1960290 < baseStart_1960290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960292 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1960292 : Nat := 118140960795 + 1960292 * 2 ^ 59
def prefixEnd_1960292 : Nat := 4983230072969 + 3 ^ 40 * 1960292 * 2
def baseEnd_1960292 : Nat := 335524006387849860744929

theorem tailTrace_1960292 : CollatzResearch.WordTrace tailWord_1960292 prefixEnd_1960292 335524006387849860744929 := by
  unfold tailWord_1960292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35748861507102175032309565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47665148676136233376412753 35748861507102175032309565)
  ·
    refine ⟨13405823065163315637116087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35748861507102175032309565 13405823065163315637116087)
    ·
      refine ⟨20108734597744973455674131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13405823065163315637116087 20108734597744973455674131)
      ·
        refine ⟨30163101896617460183511197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108734597744973455674131 30163101896617460183511197)
        ·
          refine ⟨11311163211231547568816699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30163101896617460183511197 11311163211231547568816699)
          ·
            refine ⟨16966744816847321353225049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311163211231547568816699 16966744816847321353225049)
            ·
              refine ⟨12725058612635491014918787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16966744816847321353225049 12725058612635491014918787)
              ·
                refine ⟨19087587918953236522378181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725058612635491014918787 19087587918953236522378181)
                ·
                  refine ⟨3578922734803731847945909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19087587918953236522378181 3578922734803731847945909)
                  ·
                    refine ⟨335524006387849860744929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3578922734803731847945909 335524006387849860744929)
                    ·
                      rfl

theorem cell23_1960292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1960292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960292 prefixEnd_1960292 := by exact prefixLift 1960292
  have htrace : WordTrace (prefixWord ++ tailWord_1960292) baseStart_1960292 baseEnd_1960292 := by
    simpa [prefixWord, tailWord_1960292, baseEnd_1960292] using wordTrace_append hprefix tailTrace_1960292
  have hstable : (prefixWord ++ tailWord_1960292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960292).length < 2 ^ (prefixWord ++ tailWord_1960292).sum := by decide
  have hdescent : baseEnd_1960292 < baseStart_1960292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960330 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_1960330 : Nat := 118140960795 + 1960330 * 2 ^ 59
def prefixEnd_1960330 : Nat := 4983230072969 + 3 ^ 40 * 1960330 * 2
def baseEnd_1960330 : Nat := 111843503492046714839957

theorem tailTrace_1960330 : CollatzResearch.WordTrace tailWord_1960330 prefixEnd_1960330 111843503492046714839957 := by
  unfold tailWord_1960330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874777247016670638625611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47666072658711121703001629 17874777247016670638625611)
  ·
    refine ⟨26812165870525005957938417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17874777247016670638625611 26812165870525005957938417)
    ·
      refine ⟨20109124402893754468453813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26812165870525005957938417 20109124402893754468453813)
      ·
        refine ⟨1885230412771289481417545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20109124402893754468453813 1885230412771289481417545)
        ·
          refine ⟨1413922809578467111063159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885230412771289481417545 1413922809578467111063159)
          ·
            refine ⟨2120884214367700666594739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413922809578467111063159 2120884214367700666594739)
            ·
              refine ⟨3181326321551550999892109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120884214367700666594739 3181326321551550999892109)
              ·
                refine ⟨1192997370581831624959541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181326321551550999892109 1192997370581831624959541)
                ·
                  refine ⟨111843503492046714839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192997370581831624959541 111843503492046714839957)
                  ·
                    rfl

theorem cell23_1960330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_1960330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960330 prefixEnd_1960330 := by exact prefixLift 1960330
  have htrace : WordTrace (prefixWord ++ tailWord_1960330) baseStart_1960330 baseEnd_1960330 := by
    simpa [prefixWord, tailWord_1960330, baseEnd_1960330] using wordTrace_append hprefix tailTrace_1960330
  have hstable : (prefixWord ++ tailWord_1960330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960330).length < 2 ^ (prefixWord ++ tailWord_1960330).sum := by decide
  have hdescent : baseEnd_1960330 < baseStart_1960330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960352 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 8]
def baseStart_1960352 : Nat := 118140960795 + 1960352 * 2 ^ 59
def prefixEnd_1960352 : Nat := 4983230072969 + 3 ^ 40 * 1960352 * 2
def baseEnd_1960352 : Nat := 111844758666979927498279

theorem tailTrace_1960352 : CollatzResearch.WordTrace tailWord_1960352 prefixEnd_1960352 111844758666979927498279 := by
  unfold tailWord_1960352
  simp only [CollatzResearch.WordTrace]
  refine ⟨35749955696993490155901655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47666607595991320207868873 35749955696993490155901655)
  ·
    refine ⟨53624933545490235233852483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35749955696993490155901655 53624933545490235233852483)
    ·
      refine ⟨80437400318235352850778725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53624933545490235233852483 80437400318235352850778725)
      ·
        refine ⟨15082012559669128659521011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80437400318235352850778725 15082012559669128659521011)
        ·
          refine ⟨22623018839503692989281517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15082012559669128659521011 22623018839503692989281517)
          ·
            refine ⟨8483632064813884870980569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22623018839503692989281517 8483632064813884870980569)
            ·
              refine ⟨6362724048610413653235427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8483632064813884870980569 6362724048610413653235427)
              ·
                refine ⟨9544086072915620479853141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362724048610413653235427 9544086072915620479853141)
                ·
                  refine ⟨111844758666979927498279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9544086072915620479853141 111844758666979927498279)
                  ·
                    rfl

theorem cell23_1960352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_1960352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960352 prefixEnd_1960352 := by exact prefixLift 1960352
  have htrace : WordTrace (prefixWord ++ tailWord_1960352) baseStart_1960352 baseEnd_1960352 := by
    simpa [prefixWord, tailWord_1960352, baseEnd_1960352] using wordTrace_append hprefix tailTrace_1960352
  have hstable : (prefixWord ++ tailWord_1960352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960352).length < 2 ^ (prefixWord ++ tailWord_1960352).sum := by decide
  have hdescent : baseEnd_1960352 < baseStart_1960352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960356 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_1960356 : Nat := 118140960795 + 1960356 * 2 ^ 59
def prefixEnd_1960356 : Nat := 4983230072969 + 3 ^ 40 * 1960356 * 2
def baseEnd_1960356 : Nat := 335534960641812443944831

theorem tailTrace_1960356 : CollatzResearch.WordTrace tailWord_1960356 prefixEnd_1960356 335534960641812443944831 := by
  unfold tailWord_1960356
  simp only [CollatzResearch.WordTrace]
  refine ⟨35750028642986244497474461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47666704857314992663299281 35750028642986244497474461)
  ·
    refine ⟨13406260741119841686552923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35750028642986244497474461 13406260741119841686552923)
    ·
      refine ⟨20109391111679762529829385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13406260741119841686552923 20109391111679762529829385)
      ·
        refine ⟨15082043333759821897372039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20109391111679762529829385 15082043333759821897372039)
        ·
          refine ⟨22623065000639732846058059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15082043333759821897372039 22623065000639732846058059)
          ·
            refine ⟨33934597500959599269087089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22623065000639732846058059 33934597500959599269087089)
            ·
              refine ⟨25450948125719699451815317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33934597500959599269087089 25450948125719699451815317)
              ·
                refine ⟨1193013193393110911803843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25450948125719699451815317 1193013193393110911803843)
                ·
                  refine ⟨1789519790089666367705765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193013193393110911803843 1789519790089666367705765)
                  ·
                    refine ⟨335534960641812443944831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789519790089666367705765 335534960641812443944831)
                    ·
                      rfl

theorem cell23_1960356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_1960356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960356 prefixEnd_1960356 := by exact prefixLift 1960356
  have htrace : WordTrace (prefixWord ++ tailWord_1960356) baseStart_1960356 baseEnd_1960356 := by
    simpa [prefixWord, tailWord_1960356, baseEnd_1960356] using wordTrace_append hprefix tailTrace_1960356
  have hstable : (prefixWord ++ tailWord_1960356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960356).length < 2 ^ (prefixWord ++ tailWord_1960356).sum := by decide
  have hdescent : baseEnd_1960356 < baseStart_1960356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960369 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 6]
def baseStart_1960369 : Nat := 118140960795 + 1960369 * 2 ^ 59
def prefixEnd_1960369 : Nat := 4983230072969 + 3 ^ 40 * 1960369 * 2
def baseEnd_1960369 : Nat := 111845728574882864552437

theorem tailTrace_1960369 : CollatzResearch.WordTrace tailWord_1960369 prefixEnd_1960369 111845728574882864552437 := by
  unfold tailWord_1960369
  simp only [CollatzResearch.WordTrace]
  refine ⟨71500531434925392215172161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47667020956616928143448107 71500531434925392215172161)
  ·
    refine ⟨53625398576194044161379121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71500531434925392215172161 53625398576194044161379121)
    ·
      refine ⟨40219048932145533121034341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53625398576194044161379121 40219048932145533121034341)
      ·
        refine ⟨7541071674777287460193939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40219048932145533121034341 7541071674777287460193939)
        ·
          refine ⟨11311607512165931190290909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541071674777287460193939 11311607512165931190290909)
          ·
            refine ⟨4241852817062224196359091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11311607512165931190290909 4241852817062224196359091)
            ·
              refine ⟨6362779225593336294538637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241852817062224196359091 6362779225593336294538637)
              ·
                refine ⟨2386042209597501110451989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362779225593336294538637 2386042209597501110451989)
                ·
                  refine ⟨111845728574882864552437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2386042209597501110451989 111845728574882864552437)
                  ·
                    rfl

theorem cell23_1960369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_1960369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960369 prefixEnd_1960369 := by exact prefixLift 1960369
  have htrace : WordTrace (prefixWord ++ tailWord_1960369) baseStart_1960369 baseEnd_1960369 := by
    simpa [prefixWord, tailWord_1960369, baseEnd_1960369] using wordTrace_append hprefix tailTrace_1960369
  have hstable : (prefixWord ++ tailWord_1960369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960369).length < 2 ^ (prefixWord ++ tailWord_1960369).sum := by decide
  have hdescent : baseEnd_1960369 < baseStart_1960369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960480 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 2, 4]
def baseStart_1960480 : Nat := 118140960795 + 1960480 * 2 ^ 59
def prefixEnd_1960480 : Nat := 4983230072969 + 3 ^ 40 * 1960480 * 2
def baseEnd_1960480 : Nat := 335556184508864948894641

theorem tailTrace_1960480 : CollatzResearch.WordTrace tailWord_1960480 prefixEnd_1960480 335556184508864948894641 := by
  unfold tailWord_1960480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752289968761629086231447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47669719958348838781641929 35752289968761629086231447)
  ·
    refine ⟨53628434953142443629347171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35752289968761629086231447 53628434953142443629347171)
    ·
      refine ⟨80442652429713665444020757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53628434953142443629347171 80442652429713665444020757)
      ·
        refine ⟨3770749332642828067688473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80442652429713665444020757 3770749332642828067688473)
        ·
          refine ⟨2828061999482121050766355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770749332642828067688473 2828061999482121050766355)
          ·
            refine ⟨4242092999223181576149533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828061999482121050766355 4242092999223181576149533)
            ·
              refine ⟨1590784874708693091056075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4242092999223181576149533 1590784874708693091056075)
              ·
                refine ⟨2386177312063039636584113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590784874708693091056075 2386177312063039636584113)
                ·
                  refine ⟨1789632984047279727438085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386177312063039636584113 1789632984047279727438085)
                  ·
                    refine ⟨335556184508864948894641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789632984047279727438085 335556184508864948894641)
                    ·
                      rfl

theorem cell23_1960480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_1960480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960480 prefixEnd_1960480 := by exact prefixLift 1960480
  have htrace : WordTrace (prefixWord ++ tailWord_1960480) baseStart_1960480 baseEnd_1960480 := by
    simpa [prefixWord, tailWord_1960480, baseEnd_1960480] using wordTrace_append hprefix tailTrace_1960480
  have hstable : (prefixWord ++ tailWord_1960480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960480).length < 2 ^ (prefixWord ++ tailWord_1960480).sum := by decide
  have hdescent : baseEnd_1960480 < baseStart_1960480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960496 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2]
def baseStart_1960496 : Nat := 118140960795 + 1960496 * 2 ^ 59
def prefixEnd_1960496 : Nat := 4983230072969 + 3 ^ 40 * 1960496 * 2
def baseEnd_1960496 : Nat := 1006676769217066784083849

theorem tailTrace_1960496 : CollatzResearch.WordTrace tailWord_1960496 prefixEnd_1960496 1006676769217066784083849 := by
  unfold tailWord_1960496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752581752732646452522671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47670109003643528603363561 35752581752732646452522671)
  ·
    refine ⟨53628872629098969678784007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35752581752732646452522671 53628872629098969678784007)
    ·
      refine ⟨80443308943648454518176011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53628872629098969678784007 80443308943648454518176011)
      ·
        refine ⟨120664963415472681777264017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80443308943648454518176011 120664963415472681777264017)
        ·
          refine ⟨90498722561604511332948013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120664963415472681777264017 90498722561604511332948013)
          ·
            refine ⟨33937020960601691749855505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90498722561604511332948013 33937020960601691749855505)
            ·
              refine ⟨25452765720451268812391629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33937020960601691749855505 25452765720451268812391629)
              ·
                refine ⟨9544787145169225804646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25452765720451268812391629 9544787145169225804646861)
                ·
                  refine ⟨3579295179438459676742573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9544787145169225804646861 3579295179438459676742573)
                  ·
                    refine ⟨1342235692289422378778465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579295179438459676742573 1342235692289422378778465)
                    ·
                      refine ⟨1006676769217066784083849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342235692289422378778465 1006676769217066784083849)
                      ·
                        rfl

theorem cell23_1960496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2].length) (baseStart_1960496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960496 prefixEnd_1960496 := by exact prefixLift 1960496
  have htrace : WordTrace (prefixWord ++ tailWord_1960496) baseStart_1960496 baseEnd_1960496 := by
    simpa [prefixWord, tailWord_1960496, baseEnd_1960496] using wordTrace_append hprefix tailTrace_1960496
  have hstable : (prefixWord ++ tailWord_1960496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960496).length < 2 ^ (prefixWord ++ tailWord_1960496).sum := by decide
  have hdescent : baseEnd_1960496 < baseStart_1960496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960626 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1960626 : Nat := 118140960795 + 1960626 * 2 ^ 59
def prefixEnd_1960626 : Nat := 4983230072969 + 3 ^ 40 * 1960626 * 2
def baseEnd_1960626 : Nat := 335581173900717091819417

theorem tailTrace_1960626 : CollatzResearch.WordTrace tailWord_1960626 prefixEnd_1960626 335581173900717091819417 := by
  unfold tailWord_1960626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877476248748581276819433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47673269996662883404851821 17877476248748581276819433)
  ·
    refine ⟨13408107186561435957614575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17877476248748581276819433 13408107186561435957614575)
    ·
      refine ⟨20112160779842153936421863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13408107186561435957614575 20112160779842153936421863)
      ·
        refine ⟨30168241169763230904632795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112160779842153936421863 30168241169763230904632795)
        ·
          refine ⟨45252361754644846356949193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30168241169763230904632795 45252361754644846356949193)
          ·
            refine ⟨33939271315983634767711895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45252361754644846356949193 33939271315983634767711895)
            ·
              refine ⟨50908906973975452151567843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33939271315983634767711895 50908906973975452151567843)
              ·
                refine ⟨76363360460963178227351765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50908906973975452151567843 76363360460963178227351765)
                ·
                  refine ⟨1789766260803824489703557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 76363360460963178227351765 1789766260803824489703557)
                  ·
                    refine ⟨335581173900717091819417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789766260803824489703557 335581173900717091819417)
                    ·
                      rfl

theorem cell23_1960626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1960626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960626 prefixEnd_1960626 := by exact prefixLift 1960626
  have htrace : WordTrace (prefixWord ++ tailWord_1960626) baseStart_1960626 baseEnd_1960626 := by
    simpa [prefixWord, tailWord_1960626, baseEnd_1960626] using wordTrace_append hprefix tailTrace_1960626
  have hstable : (prefixWord ++ tailWord_1960626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960626).length < 2 ^ (prefixWord ++ tailWord_1960626).sum := by decide
  have hdescent : baseEnd_1960626 < baseStart_1960626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960666 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1960666 : Nat := 118140960795 + 1960666 * 2 ^ 59
def prefixEnd_1960666 : Nat := 4983230072969 + 3 ^ 40 * 1960666 * 2
def baseEnd_1960666 : Nat := 1006764060928331118958067

theorem tailTrace_1960666 : CollatzResearch.WordTrace tailWord_1960666 prefixEnd_1960666 1006764060928331118958067 := by
  unfold tailWord_1960666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877840978712352984683463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47674242609899607959155901 17877840978712352984683463)
  ·
    refine ⟨26816761468068529477025195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877840978712352984683463 26816761468068529477025195)
    ·
      refine ⟨40225142202102794215537793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26816761468068529477025195 40225142202102794215537793)
      ·
        refine ⟨30168856651577095661653345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40225142202102794215537793 30168856651577095661653345)
        ·
          refine ⟨22626642488682821746240009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30168856651577095661653345 22626642488682821746240009)
          ·
            refine ⟨16969981866512116309680007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22626642488682821746240009 16969981866512116309680007)
            ·
              refine ⟨25454972799768174464520011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969981866512116309680007 25454972799768174464520011)
              ·
                refine ⟨38182459199652261696780017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25454972799768174464520011 38182459199652261696780017)
                ·
                  refine ⟨28636844399739196272585013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38182459199652261696780017 28636844399739196272585013)
                  ·
                    refine ⟨2684704162475549650554845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28636844399739196272585013 2684704162475549650554845)
                    ·
                      refine ⟨1006764060928331118958067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2684704162475549650554845 1006764060928331118958067)
                      ·
                        rfl

theorem cell23_1960666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1960666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960666 prefixEnd_1960666 := by exact prefixLift 1960666
  have htrace : WordTrace (prefixWord ++ tailWord_1960666) baseStart_1960666 baseEnd_1960666 := by
    simpa [prefixWord, tailWord_1960666, baseEnd_1960666] using wordTrace_append hprefix tailTrace_1960666
  have hstable : (prefixWord ++ tailWord_1960666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960666).length < 2 ^ (prefixWord ++ tailWord_1960666).sum := by decide
  have hdescent : baseEnd_1960666 < baseStart_1960666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960677 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_1960677 : Nat := 118140960795 + 1960677 * 2 ^ 59
def prefixEnd_1960677 : Nat := 4983230072969 + 3 ^ 40 * 1960677 * 2
def baseEnd_1960677 : Nat := 335589903071843525306839

theorem tailTrace_1960677 : CollatzResearch.WordTrace tailWord_1960677 prefixEnd_1960677 335589903071843525306839 := by
  unfold tailWord_1960677
  simp only [CollatzResearch.WordTrace]
  refine ⟨71511765117809560817384285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47674510078539707211589523 71511765117809560817384285)
  ·
    refine ⟨26816911919178585306519107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71511765117809560817384285 26816911919178585306519107)
    ·
      refine ⟨40225367878767877959778661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26816911919178585306519107 40225367878767877959778661)
      ·
        refine ⟨7542256477268977117458499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40225367878767877959778661 7542256477268977117458499)
        ·
          refine ⟨11313384715903465676187749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542256477268977117458499 11313384715903465676187749)
          ·
            refine ⟨2121259634231899814285203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11313384715903465676187749 2121259634231899814285203)
            ·
              refine ⟨3181889451347849721427805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121259634231899814285203 3181889451347849721427805)
              ·
                refine ⟨1193208544255443645535427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181889451347849721427805 1193208544255443645535427)
                ·
                  refine ⟨1789812816383165468303141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193208544255443645535427 1789812816383165468303141)
                  ·
                    refine ⟨335589903071843525306839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789812816383165468303141 335589903071843525306839)
                    ·
                      rfl

theorem cell23_1960677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_1960677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960677 prefixEnd_1960677 := by exact prefixLift 1960677
  have htrace : WordTrace (prefixWord ++ tailWord_1960677) baseStart_1960677 baseEnd_1960677 := by
    simpa [prefixWord, tailWord_1960677, baseEnd_1960677] using wordTrace_append hprefix tailTrace_1960677
  have hstable : (prefixWord ++ tailWord_1960677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960677).length < 2 ^ (prefixWord ++ tailWord_1960677).sum := by decide
  have hdescent : baseEnd_1960677 < baseStart_1960677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960700 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1960700 : Nat := 118140960795 + 1960700 * 2 ^ 59
def prefixEnd_1960700 : Nat := 4983230072969 + 3 ^ 40 * 1960700 * 2
def baseEnd_1960700 : Nat := 1006781519270583985932911

theorem tailTrace_1960700 : CollatzResearch.WordTrace tailWord_1960700 prefixEnd_1960700 1006781519270583985932911 := by
  unfold tailWord_1960700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35756301998363117872735777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47675069331150823830314369 35756301998363117872735777)
  ·
    refine ⟨26817226498772338404551833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35756301998363117872735777 26817226498772338404551833)
    ·
      refine ⟨20112919874079253803413875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26817226498772338404551833 20112919874079253803413875)
      ·
        refine ⟨30169379811118880705120813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112919874079253803413875 30169379811118880705120813)
        ·
          refine ⟨11313517429169580264420305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30169379811118880705120813 11313517429169580264420305)
          ·
            refine ⟨8485138071877185198315229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11313517429169580264420305 8485138071877185198315229)
            ·
              refine ⟨3181926776953944449368211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8485138071877185198315229 3181926776953944449368211)
              ·
                refine ⟨4772890165430916674052317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181926776953944449368211 4772890165430916674052317)
                ·
                  refine ⟨1789833812036593752769619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4772890165430916674052317 1789833812036593752769619)
                  ·
                    refine ⟨2684750718054890629154429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1789833812036593752769619 2684750718054890629154429)
                    ·
                      refine ⟨1006781519270583985932911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2684750718054890629154429 1006781519270583985932911)
                      ·
                        rfl

theorem cell23_1960700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1960700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960700 prefixEnd_1960700 := by exact prefixLift 1960700
  have htrace : WordTrace (prefixWord ++ tailWord_1960700) baseStart_1960700 baseEnd_1960700 := by
    simpa [prefixWord, tailWord_1960700, baseEnd_1960700] using wordTrace_append hprefix tailTrace_1960700
  have hstable : (prefixWord ++ tailWord_1960700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960700).length < 2 ^ (prefixWord ++ tailWord_1960700).sum := by decide
  have hdescent : baseEnd_1960700 < baseStart_1960700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960716 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_1960716 : Nat := 118140960795 + 1960716 * 2 ^ 59
def prefixEnd_1960716 : Nat := 4983230072969 + 3 ^ 40 * 1960716 * 2
def baseEnd_1960716 : Nat := 335596578320351974444279

theorem tailTrace_1960716 : CollatzResearch.WordTrace tailWord_1960716 prefixEnd_1960716 335596578320351974444279 := by
  unfold tailWord_1960716
  simp only [CollatzResearch.WordTrace]
  refine ⟨35756593782334135239027001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47675458376445513652036001 35756593782334135239027001)
  ·
    refine ⟨26817445336750601429270251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35756593782334135239027001 26817445336750601429270251)
    ·
      refine ⟨40226168005125902143905377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26817445336750601429270251 40226168005125902143905377)
      ·
        refine ⟨30169626003844426607929033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40226168005125902143905377 30169626003844426607929033)
        ·
          refine ⟨22627219502883319955946775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30169626003844426607929033 22627219502883319955946775)
          ·
            refine ⟨33940829254324979933920163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22627219502883319955946775 33940829254324979933920163)
            ·
              refine ⟨50911243881487469900880245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33940829254324979933920163 50911243881487469900880245)
              ·
                refine ⟨4772929113889450303207523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50911243881487469900880245 4772929113889450303207523)
                ·
                  refine ⟨7159393670834175454811285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772929113889450303207523 7159393670834175454811285)
                  ·
                    refine ⟨335596578320351974444279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7159393670834175454811285 335596578320351974444279)
                    ·
                      rfl

theorem cell23_1960716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_1960716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960716 prefixEnd_1960716 := by exact prefixLift 1960716
  have htrace : WordTrace (prefixWord ++ tailWord_1960716) baseStart_1960716 baseEnd_1960716 := by
    simpa [prefixWord, tailWord_1960716, baseEnd_1960716] using wordTrace_append hprefix tailTrace_1960716
  have hstable : (prefixWord ++ tailWord_1960716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960716).length < 2 ^ (prefixWord ++ tailWord_1960716).sum := by decide
  have hdescent : baseEnd_1960716 < baseStart_1960716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960727 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1960727 : Nat := 118140960795 + 1960727 * 2 ^ 59
def prefixEnd_1960727 : Nat := 4983230072969 + 3 ^ 40 * 1960727 * 2
def baseEnd_1960727 : Nat := 1006795383248255380295287

theorem tailTrace_1960727 : CollatzResearch.WordTrace tailWord_1960727 prefixEnd_1960727 1006795383248255380295287 := by
  unfold tailWord_1960727
  simp only [CollatzResearch.WordTrace]
  refine ⟨71513588767628419356704435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47675725845085612904469623 71513588767628419356704435)
  ·
    refine ⟨107270383151442629035056653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71513588767628419356704435 107270383151442629035056653)
    ·
      refine ⟨40226393681790985888146245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107270383151442629035056653 40226393681790985888146245)
      ·
        refine ⟨7542448815335809854027421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40226393681790985888146245 7542448815335809854027421)
        ·
          refine ⟨2828418305750928695260283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7542448815335809854027421 2828418305750928695260283)
          ·
            refine ⟨4242627458626393042890425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828418305750928695260283 4242627458626393042890425)
            ·
              refine ⟨3181970593969794782167819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242627458626393042890425 3181970593969794782167819)
              ·
                refine ⟨4772955890954692173251729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181970593969794782167819 4772955890954692173251729)
                ·
                  refine ⟨3579716918216019129938797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4772955890954692173251729 3579716918216019129938797)
                  ·
                    refine ⟨1342393844331007173727049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579716918216019129938797 1342393844331007173727049)
                    ·
                      refine ⟨1006795383248255380295287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342393844331007173727049 1006795383248255380295287)
                      ·
                        rfl

theorem cell23_1960727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1960727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960727 prefixEnd_1960727 := by exact prefixLift 1960727
  have htrace : WordTrace (prefixWord ++ tailWord_1960727) baseStart_1960727 baseEnd_1960727 := by
    simpa [prefixWord, tailWord_1960727, baseEnd_1960727] using wordTrace_append hprefix tailTrace_1960727
  have hstable : (prefixWord ++ tailWord_1960727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960727).length < 2 ^ (prefixWord ++ tailWord_1960727).sum := by decide
  have hdescent : baseEnd_1960727 < baseStart_1960727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960776 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1960776 : Nat := 118140960795 + 1960776 * 2 ^ 59
def prefixEnd_1960776 : Nat := 4983230072969 + 3 ^ 40 * 1960776 * 2
def baseEnd_1960776 : Nat := 335606847933441896194187

theorem tailTrace_1960776 : CollatzResearch.WordTrace tailWord_1960776 prefixEnd_1960776 335606847933441896194187 := by
  unfold tailWord_1960776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35757687972225450362619091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47676917296300600483492121 35757687972225450362619091)
  ·
    refine ⟨53636531958338175543928637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35757687972225450362619091 53636531958338175543928637)
    ·
      refine ⟨20113699484376815828973239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53636531958338175543928637 20113699484376815828973239)
      ·
        refine ⟨30170549226565223743459859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20113699484376815828973239 30170549226565223743459859)
        ·
          refine ⟨45255823839847835615189789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30170549226565223743459859 45255823839847835615189789)
          ·
            refine ⟨16970933939942938355696171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45255823839847835615189789 16970933939942938355696171)
            ·
              refine ⟨25456400909914407533544257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970933939942938355696171 25456400909914407533544257)
              ·
                refine ⟨19092300682435805650158193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25456400909914407533544257 19092300682435805650158193)
                ·
                  refine ⟨14319225511826854237618645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19092300682435805650158193 14319225511826854237618645)
                  ·
                    refine ⟨335606847933441896194187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14319225511826854237618645 335606847933441896194187)
                    ·
                      rfl

theorem cell23_1960776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1960776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960776 prefixEnd_1960776 := by exact prefixLift 1960776
  have htrace : WordTrace (prefixWord ++ tailWord_1960776) baseStart_1960776 baseEnd_1960776 := by
    simpa [prefixWord, tailWord_1960776, baseEnd_1960776] using wordTrace_append hprefix tailTrace_1960776
  have hstable : (prefixWord ++ tailWord_1960776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960776).length < 2 ^ (prefixWord ++ tailWord_1960776).sum := by decide
  have hdescent : baseEnd_1960776 < baseStart_1960776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960807 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1960807 : Nat := 118140960795 + 1960807 * 2 ^ 59
def prefixEnd_1960807 : Nat := 4983230072969 + 3 ^ 40 * 1960807 * 2
def baseEnd_1960807 : Nat := 1006836461700615067294919

theorem tailTrace_1960807 : CollatzResearch.WordTrace tailWord_1960807 prefixEnd_1960807 1006836461700615067294919 := by
  unfold tailWord_1960807
  simp only [CollatzResearch.WordTrace]
  refine ⟨71516506607338593019616675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47677671071559062013077783 71516506607338593019616675)
  ·
    refine ⟨107274759911007889529425013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71516506607338593019616675 107274759911007889529425013)
    ·
      refine ⟨10057008741656989643383595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107274759911007889529425013 10057008741656989643383595)
      ·
        refine ⟨15085513112485484465075393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057008741656989643383595 15085513112485484465075393)
        ·
          refine ⟨11314134834364113348806545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085513112485484465075393 11314134834364113348806545)
          ·
            refine ⟨8485601125773085011604909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314134834364113348806545 8485601125773085011604909)
            ·
              refine ⟨3182100422164906879351841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8485601125773085011604909 3182100422164906879351841)
              ·
                refine ⟨2386575316623680159513881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182100422164906879351841 2386575316623680159513881)
                ·
                  refine ⟨1789931487467760119635411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386575316623680159513881 1789931487467760119635411)
                  ·
                    refine ⟨2684897231201640179453117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1789931487467760119635411 2684897231201640179453117)
                    ·
                      refine ⟨1006836461700615067294919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2684897231201640179453117 1006836461700615067294919)
                      ·
                        rfl

theorem cell23_1960807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1960807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960807 prefixEnd_1960807 := by exact prefixLift 1960807
  have htrace : WordTrace (prefixWord ++ tailWord_1960807) baseStart_1960807 baseEnd_1960807 := by
    simpa [prefixWord, tailWord_1960807, baseEnd_1960807] using wordTrace_append hprefix tailTrace_1960807
  have hstable : (prefixWord ++ tailWord_1960807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960807).length < 2 ^ (prefixWord ++ tailWord_1960807).sum := by decide
  have hdescent : baseEnd_1960807 < baseStart_1960807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960902 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1960902 : Nat := 118140960795 + 1960902 * 2 ^ 59
def prefixEnd_1960902 : Nat := 4983230072969 + 3 ^ 40 * 1960902 * 2
def baseEnd_1960902 : Nat := 1006885242362792195606983

theorem tailTrace_1960902 : CollatzResearch.WordTrace tailWord_1960902 prefixEnd_1960902 1006885242362792195606983 := by
  unfold tailWord_1960902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234999110687325757635155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47679981027996282829549973 2234999110687325757635155)
  ·
    refine ⟨3352498666030988636452733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234999110687325757635155 3352498666030988636452733)
    ·
      refine ⟨1257186999761620738669775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3352498666030988636452733 1257186999761620738669775)
      ·
        refine ⟨1885780499642431108004663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257186999761620738669775 1885780499642431108004663)
        ·
          refine ⟨2828670749463646662006995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885780499642431108004663 2828670749463646662006995)
          ·
            refine ⟨4243006124195469993010493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828670749463646662006995 4243006124195469993010493)
            ·
              refine ⟨1591127296573301247378935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4243006124195469993010493 1591127296573301247378935)
              ·
                refine ⟨2386690944859951871068403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591127296573301247378935 2386690944859951871068403)
                ·
                  refine ⟨3580036417289927806602605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386690944859951871068403 3580036417289927806602605)
                  ·
                    refine ⟨1342513656483722927475977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580036417289927806602605 1342513656483722927475977)
                    ·
                      refine ⟨1006885242362792195606983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342513656483722927475977 1006885242362792195606983)
                      ·
                        rfl

theorem cell23_1960902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1960902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960902 prefixEnd_1960902 := by exact prefixLift 1960902
  have htrace : WordTrace (prefixWord ++ tailWord_1960902) baseStart_1960902 baseEnd_1960902 := by
    simpa [prefixWord, tailWord_1960902, baseEnd_1960902] using wordTrace_append hprefix tailTrace_1960902
  have hstable : (prefixWord ++ tailWord_1960902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960902).length < 2 ^ (prefixWord ++ tailWord_1960902).sum := by decide
  have hdescent : baseEnd_1960902 < baseStart_1960902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960903 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1960903 : Nat := 118140960795 + 1960903 * 2 ^ 59
def prefixEnd_1960903 : Nat := 4983230072969 + 3 ^ 40 * 1960903 * 2
def baseEnd_1960903 : Nat := 1006885755843446691694477

theorem tailTrace_1960903 : CollatzResearch.WordTrace tailWord_1960903 prefixEnd_1960903 1006885755843446691694477 := by
  unfold tailWord_1960903
  simp only [CollatzResearch.WordTrace]
  refine ⟨71520008014990801415111363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47680005343327200943407575 71520008014990801415111363)
  ·
    refine ⟨107280012022486202122667045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71520008014990801415111363 107280012022486202122667045)
    ·
      refine ⟨20115002254216162898000071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107280012022486202122667045 20115002254216162898000071)
      ·
        refine ⟨30172503381324244347000107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20115002254216162898000071 30172503381324244347000107)
        ·
          refine ⟨45258755071986366520500161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30172503381324244347000107 45258755071986366520500161)
          ·
            refine ⟨33944066303989774890375121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45258755071986366520500161 33944066303989774890375121)
            ·
              refine ⟨25458049727992331167781341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33944066303989774890375121 25458049727992331167781341)
              ·
                refine ⟨9546768647997124187918003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25458049727992331167781341 9546768647997124187918003)
                ·
                  refine ⟨14320152971995686281877005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9546768647997124187918003 14320152971995686281877005)
                  ·
                    refine ⟨5370057364498382355703877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14320152971995686281877005 5370057364498382355703877)
                    ·
                      refine ⟨1006885755843446691694477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5370057364498382355703877 1006885755843446691694477)
                      ·
                        rfl

theorem cell23_1960903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1960903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960903 prefixEnd_1960903 := by exact prefixLift 1960903
  have htrace : WordTrace (prefixWord ++ tailWord_1960903) baseStart_1960903 baseEnd_1960903 := by
    simpa [prefixWord, tailWord_1960903, baseEnd_1960903] using wordTrace_append hprefix tailTrace_1960903
  have hstable : (prefixWord ++ tailWord_1960903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960903).length < 2 ^ (prefixWord ++ tailWord_1960903).sum := by decide
  have hdescent : baseEnd_1960903 < baseStart_1960903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960920 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1960920 : Nat := 118140960795 + 1960920 * 2 ^ 59
def prefixEnd_1960920 : Nat := 4983230072969 + 3 ^ 40 * 1960920 * 2
def baseEnd_1960920 : Nat := 1006894485014573125181899

theorem tailTrace_1960920 : CollatzResearch.WordTrace tailWord_1960920 prefixEnd_1960920 1006894485014573125181899 := by
  unfold tailWord_1960920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760314027964606659240107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47680418703952808878986809 35760314027964606659240107)
  ·
    refine ⟨53640471041946909988860161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35760314027964606659240107 53640471041946909988860161)
    ·
      refine ⟨40230353281460182491645121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53640471041946909988860161 40230353281460182491645121)
      ·
        refine ⟨30172764961095136868733841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40230353281460182491645121 30172764961095136868733841)
        ·
          refine ⟨22629573720821352651550381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30172764961095136868733841 22629573720821352651550381)
          ·
            refine ⟨8486090145308007244331393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22629573720821352651550381 8486090145308007244331393)
            ·
              refine ⟨6364567608981005433248545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486090145308007244331393 6364567608981005433248545)
              ·
                refine ⟨4773425706735754074936409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364567608981005433248545 4773425706735754074936409)
                ·
                  refine ⟨3580069280051815556202307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4773425706735754074936409 3580069280051815556202307)
                  ·
                    refine ⟨5370103920077723334303461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580069280051815556202307 5370103920077723334303461)
                    ·
                      refine ⟨1006894485014573125181899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5370103920077723334303461 1006894485014573125181899)
                      ·
                        rfl

theorem cell23_1960920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1960920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1960920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1960920 prefixEnd_1960920 := by exact prefixLift 1960920
  have htrace : WordTrace (prefixWord ++ tailWord_1960920) baseStart_1960920 baseEnd_1960920 := by
    simpa [prefixWord, tailWord_1960920, baseEnd_1960920] using wordTrace_append hprefix tailTrace_1960920
  have hstable : (prefixWord ++ tailWord_1960920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960920).length < 2 ^ (prefixWord ++ tailWord_1960920).sum := by decide
  have hdescent : baseEnd_1960920 < baseStart_1960920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961014 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_1961014 : Nat := 118140960795 + 1961014 * 2 ^ 59
def prefixEnd_1961014 : Nat := 4983230072969 + 3 ^ 40 * 1961014 * 2
def baseEnd_1961014 : Nat := 1006942752196095757406467

theorem tailTrace_1961014 : CollatzResearch.WordTrace tailWord_1961014 prefixEnd_1961014 1006942752196095757406467 := by
  unfold tailWord_1961014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470253532349291710775131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47682704345059111581601397 4470253532349291710775131)
  ·
    refine ⟨6705380298523937566162697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470253532349291710775131 6705380298523937566162697)
    ·
      refine ⟨5029035223892953174622023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6705380298523937566162697 5029035223892953174622023)
      ·
        refine ⟨7543552835839429761933035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029035223892953174622023 7543552835839429761933035)
        ·
          refine ⟨11315329253759144642899553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543552835839429761933035 11315329253759144642899553)
          ·
            refine ⟨8486496940319358482174665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11315329253759144642899553 8486496940319358482174665)
            ·
              refine ⟨6364872705239518861630999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486496940319358482174665 6364872705239518861630999)
              ·
                refine ⟨9547309057859278292446499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364872705239518861630999 9547309057859278292446499)
                ·
                  refine ⟨14320963586788917438669749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547309057859278292446499 14320963586788917438669749)
                  ·
                    refine ⟨1342590336261461009875289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14320963586788917438669749 1342590336261461009875289)
                    ·
                      refine ⟨1006942752196095757406467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342590336261461009875289 1006942752196095757406467)
                      ·
                        rfl

theorem cell23_1961014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_1961014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961014 prefixEnd_1961014 := by exact prefixLift 1961014
  have htrace : WordTrace (prefixWord ++ tailWord_1961014) baseStart_1961014 baseEnd_1961014 := by
    simpa [prefixWord, tailWord_1961014, baseEnd_1961014] using wordTrace_append hprefix tailTrace_1961014
  have hstable : (prefixWord ++ tailWord_1961014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961014).length < 2 ^ (prefixWord ++ tailWord_1961014).sum := by decide
  have hdescent : baseEnd_1961014 < baseStart_1961014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961021 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1961021 : Nat := 118140960795 + 1961021 * 2 ^ 59
def prefixEnd_1961021 : Nat := 4983230072969 + 3 ^ 40 * 1961021 * 2
def baseEnd_1961021 : Nat := 1006946346560677230018935

theorem tailTrace_1961021 : CollatzResearch.WordTrace tailWord_1961021 prefixEnd_1961021 1006946346560677230018935 := by
  unfold tailWord_1961021
  simp only [CollatzResearch.WordTrace]
  refine ⟨71524311828563307567906917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47682874552375538378604611 71524311828563307567906917)
  ·
    refine ⟨13410808467855620168982547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71524311828563307567906917 13410808467855620168982547)
    ·
      refine ⟨20116212701783430253473821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13410808467855620168982547 20116212701783430253473821)
      ·
        refine ⟨7543579763168786345052683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20116212701783430253473821 7543579763168786345052683)
        ·
          refine ⟨11315369644753179517579025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543579763168786345052683 11315369644753179517579025)
          ·
            refine ⟨8486527233564884638184269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11315369644753179517579025 8486527233564884638184269)
            ·
              refine ⟨3182447712586831739319101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8486527233564884638184269 3182447712586831739319101)
              ·
                refine ⟨1193417892220061902244663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3182447712586831739319101 1193417892220061902244663)
                ·
                  refine ⟨1790126838330092853366995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193417892220061902244663 1790126838330092853366995)
                  ·
                    refine ⟨2685190257495139280050493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1790126838330092853366995 2685190257495139280050493)
                    ·
                      refine ⟨1006946346560677230018935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2685190257495139280050493 1006946346560677230018935)
                      ·
                        rfl

theorem cell23_1961021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1961021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961021 prefixEnd_1961021 := by exact prefixLift 1961021
  have htrace : WordTrace (prefixWord ++ tailWord_1961021) baseStart_1961021 baseEnd_1961021 := by
    simpa [prefixWord, tailWord_1961021, baseEnd_1961021] using wordTrace_append hprefix tailTrace_1961021
  have hstable : (prefixWord ++ tailWord_1961021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961021).length < 2 ^ (prefixWord ++ tailWord_1961021).sum := by decide
  have hdescent : baseEnd_1961021 < baseStart_1961021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961043 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_1961043 : Nat := 118140960795 + 1961043 * 2 ^ 59
def prefixEnd_1961043 : Nat := 4983230072969 + 3 ^ 40 * 1961043 * 2
def baseEnd_1961043 : Nat := 1006957643135076143943833

theorem tailTrace_1961043 : CollatzResearch.WordTrace tailWord_1961043 prefixEnd_1961043 1006957643135076143943833 := by
  unfold tailWord_1961043
  simp only [CollatzResearch.WordTrace]
  refine ⟨71525114234483605325207783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47683409489655736883471855 71525114234483605325207783)
  ·
    refine ⟨107287671351725407987811675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71525114234483605325207783 107287671351725407987811675)
    ·
      refine ⟨160931507027588111981717513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107287671351725407987811675 160931507027588111981717513)
      ·
        refine ⟨120698630270691083986288135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160931507027588111981717513 120698630270691083986288135)
        ·
          refine ⟨181047945406036625979432203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120698630270691083986288135 181047945406036625979432203)
          ·
            refine ⟨271571918109054938969148305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181047945406036625979432203 271571918109054938969148305)
            ·
              refine ⟨203678938581791204226861229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271571918109054938969148305 203678938581791204226861229)
              ·
                refine ⟨76379601968171701585072961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203678938581791204226861229 76379601968171701585072961)
                ·
                  refine ⟨57284701476128776188804721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76379601968171701585072961 57284701476128776188804721)
                  ·
                    refine ⟨42963526107096582141603541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57284701476128776188804721 42963526107096582141603541)
                    ·
                      refine ⟨1006957643135076143943833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42963526107096582141603541 1006957643135076143943833)
                      ·
                        rfl

theorem cell23_1961043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_1961043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961043 prefixEnd_1961043 := by exact prefixLift 1961043
  have htrace : WordTrace (prefixWord ++ tailWord_1961043) baseStart_1961043 baseEnd_1961043 := by
    simpa [prefixWord, tailWord_1961043, baseEnd_1961043] using wordTrace_append hprefix tailTrace_1961043
  have hstable : (prefixWord ++ tailWord_1961043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961043).length < 2 ^ (prefixWord ++ tailWord_1961043).sum := by decide
  have hdescent : baseEnd_1961043 < baseStart_1961043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961078 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1961078 : Nat := 118140960795 + 1961078 * 2 ^ 59
def prefixEnd_1961078 : Nat := 4983230072969 + 3 ^ 40 * 1961078 * 2
def baseEnd_1961078 : Nat := 1006975614957983507006173

theorem tailTrace_1961078 : CollatzResearch.WordTrace tailWord_1961078 prefixEnd_1961078 1006975614957983507006173 := by
  unfold tailWord_1961078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470399424334800393920743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47684260526237870868487925 4470399424334800393920743)
  ·
    refine ⟨6705599136502200590881115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470399424334800393920743 6705599136502200590881115)
    ·
      refine ⟨10058398704753300886321673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705599136502200590881115 10058398704753300886321673)
      ·
        refine ⟨7543799028564975664741255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10058398704753300886321673 7543799028564975664741255)
        ·
          refine ⟨11315698542847463497111883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543799028564975664741255 11315698542847463497111883)
          ·
            refine ⟨16973547814271195245667825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315698542847463497111883 16973547814271195245667825)
            ·
              refine ⟨12730160860703396434250869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16973547814271195245667825 12730160860703396434250869)
              ·
                refine ⟨1193452580690943415711019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12730160860703396434250869 1193452580690943415711019)
                ·
                  refine ⟨1790178871036415123566529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193452580690943415711019 1790178871036415123566529)
                  ·
                    refine ⟨1342634153277311342674897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790178871036415123566529 1342634153277311342674897)
                    ·
                      refine ⟨1006975614957983507006173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342634153277311342674897 1006975614957983507006173)
                      ·
                        rfl

theorem cell23_1961078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1961078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961078 prefixEnd_1961078 := by exact prefixLift 1961078
  have htrace : WordTrace (prefixWord ++ tailWord_1961078) baseStart_1961078 baseEnd_1961078 := by
    simpa [prefixWord, tailWord_1961078, baseEnd_1961078] using wordTrace_append hprefix tailTrace_1961078
  have hstable : (prefixWord ++ tailWord_1961078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961078).length < 2 ^ (prefixWord ++ tailWord_1961078).sum := by decide
  have hdescent : baseEnd_1961078 < baseStart_1961078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961081 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 1, 2, 3]
def baseStart_1961081 : Nat := 118140960795 + 1961081 * 2 ^ 59
def prefixEnd_1961081 : Nat := 4983230072969 + 3 ^ 40 * 1961081 * 2
def baseEnd_1961081 : Nat := 1006977155399946995268659

theorem tailTrace_1961081 : CollatzResearch.WordTrace tailWord_1961081 prefixEnd_1961081 1006977155399946995268659 := by
  unfold tailWord_1961081
  simp only [CollatzResearch.WordTrace]
  refine ⟨71526500208345937815091097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47684333472230625210060731 71526500208345937815091097)
  ·
    refine ⟨53644875156259453361318323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71526500208345937815091097 53644875156259453361318323)
    ·
      refine ⟨80467312734389180041977485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53644875156259453361318323 80467312734389180041977485)
      ·
        refine ⟨30175242275395942515741557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80467312734389180041977485 30175242275395942515741557)
        ·
          refine ⟨2828928963318369610850771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30175242275395942515741557 2828928963318369610850771)
          ·
            refine ⟨4243393444977554416276157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828928963318369610850771 4243393444977554416276157)
            ·
              refine ⟨1591272541866582906103559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4243393444977554416276157 1591272541866582906103559)
              ·
                refine ⟨2386908812799874359155339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591272541866582906103559 2386908812799874359155339)
                ·
                  refine ⟨3580363219199811538733009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386908812799874359155339 3580363219199811538733009)
                  ·
                    refine ⟨2685272414399858654049757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580363219199811538733009 2685272414399858654049757)
                    ·
                      refine ⟨1006977155399946995268659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2685272414399858654049757 1006977155399946995268659)
                      ·
                        rfl

theorem cell23_1961081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_1961081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961081 prefixEnd_1961081 := by exact prefixLift 1961081
  have htrace : WordTrace (prefixWord ++ tailWord_1961081) baseStart_1961081 baseEnd_1961081 := by
    simpa [prefixWord, tailWord_1961081, baseEnd_1961081] using wordTrace_append hprefix tailTrace_1961081
  have hstable : (prefixWord ++ tailWord_1961081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961081).length < 2 ^ (prefixWord ++ tailWord_1961081).sum := by decide
  have hdescent : baseEnd_1961081 < baseStart_1961081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961138 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_1961138 : Nat := 118140960795 + 1961138 * 2 ^ 59
def prefixEnd_1961138 : Nat := 4983230072969 + 3 ^ 40 * 1961138 * 2
def baseEnd_1961138 : Nat := 1007006423797253272255897

theorem tailTrace_1961138 : CollatzResearch.WordTrace tailWord_1961138 prefixEnd_1961138 1007006423797253272255897 := by
  unfold tailWord_1961138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17882144792284859137479017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47685719446092957699944045 17882144792284859137479017)
  ·
    refine ⟨13411608594213644353109263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17882144792284859137479017 13411608594213644353109263)
    ·
      refine ⟨20117412891320466529663895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13411608594213644353109263 20117412891320466529663895)
      ·
        refine ⟨30176119336980699794495843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20117412891320466529663895 30176119336980699794495843)
        ·
          refine ⟨45264179005471049691743765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30176119336980699794495843 45264179005471049691743765)
          ·
            refine ⟨2121758390881455454300489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45264179005471049691743765 2121758390881455454300489)
            ·
              refine ⟨1591318793161091590725367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121758390881455454300489 1591318793161091590725367)
              ·
                refine ⟨2386978189741637386088051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591318793161091590725367 2386978189741637386088051)
                ·
                  refine ⟨3580467284612456079132077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386978189741637386088051 3580467284612456079132077)
                  ·
                    refine ⟨1342675231729671029674529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580467284612456079132077 1342675231729671029674529)
                    ·
                      refine ⟨1007006423797253272255897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342675231729671029674529 1007006423797253272255897)
                      ·
                        rfl

theorem cell23_1961138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_1961138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961138 prefixEnd_1961138 := by exact prefixLift 1961138
  have htrace : WordTrace (prefixWord ++ tailWord_1961138) baseStart_1961138 baseEnd_1961138 := by
    simpa [prefixWord, tailWord_1961138, baseEnd_1961138] using wordTrace_append hprefix tailTrace_1961138
  have hstable : (prefixWord ++ tailWord_1961138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961138).length < 2 ^ (prefixWord ++ tailWord_1961138).sum := by decide
  have hdescent : baseEnd_1961138 < baseStart_1961138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961151 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 2, 2, 2]
def baseStart_1961151 : Nat := 118140960795 + 1961151 * 2 ^ 59
def prefixEnd_1961151 : Nat := 4983230072969 + 3 ^ 40 * 1961151 * 2
def baseEnd_1961151 : Nat := 1007013099045761721393337

theorem tailTrace_1961151 : CollatzResearch.WordTrace tailWord_1961151 prefixEnd_1961151 1007013099045761721393337 := by
  unfold tailWord_1961151
  simp only [CollatzResearch.WordTrace]
  refine ⟨71529053318092339770139307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47686035545394893180092871 71529053318092339770139307)
  ·
    refine ⟨107293579977138509655208961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71529053318092339770139307 107293579977138509655208961)
    ·
      refine ⟨80470184982853882241406721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107293579977138509655208961 80470184982853882241406721)
      ·
        refine ⟨60352638737140411681055041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80470184982853882241406721 60352638737140411681055041)
        ·
          refine ⟨45264479052855308760791281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60352638737140411681055041 45264479052855308760791281)
          ·
            refine ⟨33948359289641481570593461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45264479052855308760791281 33948359289641481570593461)
            ·
              refine ⟨3182658683403888897243137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33948359289641481570593461 3182658683403888897243137)
              ·
                refine ⟨2386994012552916672932353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182658683403888897243137 2386994012552916672932353)
                ·
                  refine ⟨1790245509414687504699265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386994012552916672932353 1790245509414687504699265)
                  ·
                    refine ⟨1342684132061015628524449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790245509414687504699265 1342684132061015628524449)
                    ·
                      refine ⟨1007013099045761721393337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342684132061015628524449 1007013099045761721393337)
                      ·
                        rfl

theorem cell23_1961151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_1961151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961151 prefixEnd_1961151 := by exact prefixLift 1961151
  have htrace : WordTrace (prefixWord ++ tailWord_1961151) baseStart_1961151 baseEnd_1961151 := by
    simpa [prefixWord, tailWord_1961151, baseEnd_1961151] using wordTrace_append hprefix tailTrace_1961151
  have hstable : (prefixWord ++ tailWord_1961151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961151).length < 2 ^ (prefixWord ++ tailWord_1961151).sum := by decide
  have hdescent : baseEnd_1961151 < baseStart_1961151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961207 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1961207 : Nat := 118140960795 + 1961207 * 2 ^ 59
def prefixEnd_1961207 : Nat := 4983230072969 + 3 ^ 40 * 1961207 * 2
def baseEnd_1961207 : Nat := 1007041853962413502293079

theorem tailTrace_1961207 : CollatzResearch.WordTrace tailWord_1961207 prefixEnd_1961207 1007041853962413502293079 := by
  unfold tailWord_1961207
  simp only [CollatzResearch.WordTrace]
  refine ⟨71531095805889461334177875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47687397203926307556118583 71531095805889461334177875)
  ·
    refine ⟨107296643708834192001266813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71531095805889461334177875 107296643708834192001266813)
    ·
      refine ⟨40236241390812822000475055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107296643708834192001266813 40236241390812822000475055)
      ·
        refine ⟨60354362086219233000712583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40236241390812822000475055 60354362086219233000712583)
        ·
          refine ⟨90531543129328849501068875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60354362086219233000712583 90531543129328849501068875)
          ·
            refine ⟨135797314693993274251603313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90531543129328849501068875 135797314693993274251603313)
            ·
              refine ⟨101847986020494955688702485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135797314693993274251603313 101847986020494955688702485)
              ·
                refine ⟨4774124344710701047907929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101847986020494955688702485 4774124344710701047907929)
                ·
                  refine ⟨3580593258533025785930947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774124344710701047907929 3580593258533025785930947)
                  ·
                    refine ⟨5370889887799538678896421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580593258533025785930947 5370889887799538678896421)
                    ·
                      refine ⟨1007041853962413502293079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5370889887799538678896421 1007041853962413502293079)
                      ·
                        rfl

theorem cell23_1961207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1961207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961207 prefixEnd_1961207 := by exact prefixLift 1961207
  have htrace : WordTrace (prefixWord ++ tailWord_1961207) baseStart_1961207 baseEnd_1961207 := by
    simpa [prefixWord, tailWord_1961207, baseEnd_1961207] using wordTrace_append hprefix tailTrace_1961207
  have hstable : (prefixWord ++ tailWord_1961207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961207).length < 2 ^ (prefixWord ++ tailWord_1961207).sum := by decide
  have hdescent : baseEnd_1961207 < baseStart_1961207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961214 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1961214 : Nat := 118140960795 + 1961214 * 2 ^ 59
def prefixEnd_1961214 : Nat := 4983230072969 + 3 ^ 40 * 1961214 * 2
def baseEnd_1961214 : Nat := 1007045448326994974905547

theorem tailTrace_1961214 : CollatzResearch.WordTrace tailWord_1961214 prefixEnd_1961214 1007045448326994974905547 := by
  unfold tailWord_1961214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941418889608012691210337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47687567411242734353121797 8941418889608012691210337)
  ·
    refine ⟨6706064167206009518407753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8941418889608012691210337 6706064167206009518407753)
    ·
      refine ⟨5029548125404507138805815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6706064167206009518407753 5029548125404507138805815)
      ·
        refine ⟨7544322188106760708208723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029548125404507138805815 7544322188106760708208723)
        ·
          refine ⟨11316483282160141062313085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544322188106760708208723 11316483282160141062313085)
          ·
            refine ⟨4243681230810052898367407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11316483282160141062313085 4243681230810052898367407)
            ·
              refine ⟨6365521846215079347551111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243681230810052898367407 6365521846215079347551111)
              ·
                refine ⟨9548282769322619021326667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6365521846215079347551111 9548282769322619021326667)
                ·
                  refine ⟨14322424153983928531990001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548282769322619021326667 14322424153983928531990001)
                  ·
                    refine ⟨10741818115487946398992501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14322424153983928531990001 10741818115487946398992501)
                    ·
                      refine ⟨1007045448326994974905547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10741818115487946398992501 1007045448326994974905547)
                      ·
                        rfl

theorem cell23_1961214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1961214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961214 prefixEnd_1961214 := by exact prefixLift 1961214
  have htrace : WordTrace (prefixWord ++ tailWord_1961214) baseStart_1961214 baseEnd_1961214 := by
    simpa [prefixWord, tailWord_1961214, baseEnd_1961214] using wordTrace_append hprefix tailTrace_1961214
  have hstable : (prefixWord ++ tailWord_1961214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961214).length < 2 ^ (prefixWord ++ tailWord_1961214).sum := by decide
  have hdescent : baseEnd_1961214 < baseStart_1961214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961244 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1961244 : Nat := 118140960795 + 1961244 * 2 ^ 59
def prefixEnd_1961244 : Nat := 4983230072969 + 3 ^ 40 * 1961244 * 2
def baseEnd_1961244 : Nat := 1007060852746629857530409

theorem tailTrace_1961244 : CollatzResearch.WordTrace tailWord_1961244 prefixEnd_1961244 1007060852746629857530409 := by
  unfold tailWord_1961244
  simp only [CollatzResearch.WordTrace]
  refine ⟨35766222653377708326637393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47688296871170277768849857 35766222653377708326637393)
  ·
    refine ⟨26824666990033281244978045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35766222653377708326637393 26824666990033281244978045)
    ·
      refine ⟨10059250121262480466866767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26824666990033281244978045 10059250121262480466866767)
      ·
        refine ⟨15088875181893720700300151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10059250121262480466866767 15088875181893720700300151)
        ·
          refine ⟨22633312772840581050450227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15088875181893720700300151 22633312772840581050450227)
          ·
            refine ⟨33949969159260871575675341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633312772840581050450227 33949969159260871575675341)
            ·
              refine ⟨12731238434722826840878253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33949969159260871575675341 12731238434722826840878253)
              ·
                refine ⟨4774214413021060065329345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12731238434722826840878253 4774214413021060065329345)
                ·
                  refine ⟨3580660809765795048997009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774214413021060065329345 3580660809765795048997009)
                  ·
                    refine ⟨2685495607324346286747757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580660809765795048997009 2685495607324346286747757)
                    ·
                      refine ⟨1007060852746629857530409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2685495607324346286747757 1007060852746629857530409)
                      ·
                        rfl

theorem cell23_1961244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1961244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961244 prefixEnd_1961244 := by exact prefixLift 1961244
  have htrace : WordTrace (prefixWord ++ tailWord_1961244) baseStart_1961244 baseEnd_1961244 := by
    simpa [prefixWord, tailWord_1961244, baseEnd_1961244] using wordTrace_append hprefix tailTrace_1961244
  have hstable : (prefixWord ++ tailWord_1961244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961244).length < 2 ^ (prefixWord ++ tailWord_1961244).sum := by decide
  have hdescent : baseEnd_1961244 < baseStart_1961244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961268 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_1961268 : Nat := 118140960795 + 1961268 * 2 ^ 59
def prefixEnd_1961268 : Nat := 4983230072969 + 3 ^ 40 * 1961268 * 2
def baseEnd_1961268 : Nat := 335691058760779254543433

theorem tailTrace_1961268 : CollatzResearch.WordTrace tailWord_1961268 prefixEnd_1961268 335691058760779254543433 := by
  unfold tailWord_1961268
  simp only [CollatzResearch.WordTrace]
  refine ⟨35766660329334234376074229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47688880439112312501432305 35766660329334234376074229)
  ·
    refine ⟨3353124405875084472756959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35766660329334234376074229 3353124405875084472756959)
    ·
      refine ⟨5029686608812626709135439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353124405875084472756959 5029686608812626709135439)
      ·
        refine ⟨7544529913218940063703159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029686608812626709135439 7544529913218940063703159)
        ·
          refine ⟨11316794869828410095554739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544529913218940063703159 11316794869828410095554739)
          ·
            refine ⟨16975192304742615143332109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316794869828410095554739 16975192304742615143332109)
            ·
              refine ⟨6365697114278480678749541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16975192304742615143332109 6365697114278480678749541)
              ·
                refine ⟨1193568208927215127265539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6365697114278480678749541 1193568208927215127265539)
                ·
                  refine ⟨1790352313390822690898309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193568208927215127265539 1790352313390822690898309)
                  ·
                    refine ⟨335691058760779254543433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1790352313390822690898309 335691058760779254543433)
                    ·
                      rfl

theorem cell23_1961268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_1961268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961268 prefixEnd_1961268 := by exact prefixLift 1961268
  have htrace : WordTrace (prefixWord ++ tailWord_1961268) baseStart_1961268 baseEnd_1961268 := by
    simpa [prefixWord, tailWord_1961268, baseEnd_1961268] using wordTrace_append hprefix tailTrace_1961268
  have hstable : (prefixWord ++ tailWord_1961268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961268).length < 2 ^ (prefixWord ++ tailWord_1961268).sum := by decide
  have hdescent : baseEnd_1961268 < baseStart_1961268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961294 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_1961294 : Nat := 118140960795 + 1961294 * 2 ^ 59
def prefixEnd_1961294 : Nat := 4983230072969 + 3 ^ 40 * 1961294 * 2
def baseEnd_1961294 : Nat := 335695508926451553968393

theorem tailTrace_1961294 : CollatzResearch.WordTrace tailWord_1961294 prefixEnd_1961294 335695508926451553968393 := by
  unfold tailWord_1961294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941783619571784399074367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47689512637716183461729957 8941783619571784399074367)
  ·
    refine ⟨13412675429357676598611551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8941783619571784399074367 13412675429357676598611551)
    ·
      refine ⟨20119013144036514897917327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13412675429357676598611551 20119013144036514897917327)
      ·
        refine ⟨30178519716054772346875991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119013144036514897917327 30178519716054772346875991)
        ·
          refine ⟨45267779574082158520313987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30178519716054772346875991 45267779574082158520313987)
          ·
            refine ⟨67901669361123237780470981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45267779574082158520313987 67901669361123237780470981)
            ·
              refine ⟨12731563005210607083838309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67901669361123237780470981 12731563005210607083838309)
              ·
                refine ⟨2387168063476988828219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12731563005210607083838309 2387168063476988828219683)
                ·
                  refine ⟨3580752095215483242329525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387168063476988828219683 3580752095215483242329525)
                  ·
                    refine ⟨335695508926451553968393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3580752095215483242329525 335695508926451553968393)
                    ·
                      rfl

theorem cell23_1961294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_1961294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961294 prefixEnd_1961294 := by exact prefixLift 1961294
  have htrace : WordTrace (prefixWord ++ tailWord_1961294) baseStart_1961294 baseEnd_1961294 := by
    simpa [prefixWord, tailWord_1961294, baseEnd_1961294] using wordTrace_append hprefix tailTrace_1961294
  have hstable : (prefixWord ++ tailWord_1961294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961294).length < 2 ^ (prefixWord ++ tailWord_1961294).sum := by decide
  have hdescent : baseEnd_1961294 < baseStart_1961294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961301 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1961301 : Nat := 118140960795 + 1961301 * 2 ^ 59
def prefixEnd_1961301 : Nat := 4983230072969 + 3 ^ 40 * 1961301 * 2
def baseEnd_1961301 : Nat := 1007090121143936134517647

theorem tailTrace_1961301 : CollatzResearch.WordTrace tailWord_1961301 prefixEnd_1961301 1007090121143936134517647 := by
  unfold tailWord_1961301
  simp only [CollatzResearch.WordTrace]
  refine ⟨71534524267548915388099757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47689682845032610258733171 71534524267548915388099757)
  ·
    refine ⟨26825446600330843270537409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71534524267548915388099757 26825446600330843270537409)
    ·
      refine ⟨20119084950248132452903057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26825446600330843270537409 20119084950248132452903057)
      ·
        refine ⟨15089313712686099339677293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20119084950248132452903057 15089313712686099339677293)
        ·
          refine ⟨5658492642257287252378985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15089313712686099339677293 5658492642257287252378985)
          ·
            refine ⟨4243869481692965439284239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5658492642257287252378985 4243869481692965439284239)
            ·
              refine ⟨6365804222539448158926359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243869481692965439284239 6365804222539448158926359)
              ·
                refine ⟨9548706333809172238389539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6365804222539448158926359 9548706333809172238389539)
                ·
                  refine ⟨14323059500713758357584309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548706333809172238389539 14323059500713758357584309)
                  ·
                    refine ⟨1342786828191914846023529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14323059500713758357584309 1342786828191914846023529)
                    ·
                      refine ⟨1007090121143936134517647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342786828191914846023529 1007090121143936134517647)
                      ·
                        rfl

theorem cell23_1961301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1961301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961301 prefixEnd_1961301 := by exact prefixLift 1961301
  have htrace : WordTrace (prefixWord ++ tailWord_1961301) baseStart_1961301 baseEnd_1961301 := by
    simpa [prefixWord, tailWord_1961301, baseEnd_1961301] using wordTrace_append hprefix tailTrace_1961301
  have hstable : (prefixWord ++ tailWord_1961301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961301).length < 2 ^ (prefixWord ++ tailWord_1961301).sum := by decide
  have hdescent : baseEnd_1961301 < baseStart_1961301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961327 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_1961327 : Nat := 118140960795 + 1961327 * 2 ^ 59
def prefixEnd_1961327 : Nat := 4983230072969 + 3 ^ 40 * 1961327 * 2
def baseEnd_1961327 : Nat := 1007103471640953032792527

theorem tailTrace_1961327 : CollatzResearch.WordTrace tailWord_1961327 prefixEnd_1961327 1007103471640953032792527 := by
  unfold tailWord_1961327
  simp only [CollatzResearch.WordTrace]
  refine ⟨71535472565454721828546235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47690315043636481219030823 71535472565454721828546235)
  ·
    refine ⟨107303208848182082742819353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71535472565454721828546235 107303208848182082742819353)
    ·
      refine ⟨80477406636136562057114515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107303208848182082742819353 80477406636136562057114515)
      ·
        refine ⟨120716109954204843085671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80477406636136562057114515 120716109954204843085671773)
        ·
          refine ⟨45268541232826816157126915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120716109954204843085671773 45268541232826816157126915)
          ·
            refine ⟨67902811849240224235690373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45268541232826816157126915 67902811849240224235690373)
            ·
              refine ⟨12731777221732542044191945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67902811849240224235690373 12731777221732542044191945)
              ·
                refine ⟨9548832916299406533143959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12731777221732542044191945 9548832916299406533143959)
                ·
                  refine ⟨14323249374449109799715939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548832916299406533143959 14323249374449109799715939)
                  ·
                    refine ⟨21484874061673664699573909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14323249374449109799715939 21484874061673664699573909)
                    ·
                      refine ⟨1007103471640953032792527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21484874061673664699573909 1007103471640953032792527)
                      ·
                        rfl

theorem cell23_1961327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_1961327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961327 prefixEnd_1961327 := by exact prefixLift 1961327
  have htrace : WordTrace (prefixWord ++ tailWord_1961327) baseStart_1961327 baseEnd_1961327 := by
    simpa [prefixWord, tailWord_1961327, baseEnd_1961327] using wordTrace_append hprefix tailTrace_1961327
  have hstable : (prefixWord ++ tailWord_1961327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961327).length < 2 ^ (prefixWord ++ tailWord_1961327).sum := by decide
  have hdescent : baseEnd_1961327 < baseStart_1961327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961348 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_1961348 : Nat := 118140960795 + 1961348 * 2 ^ 59
def prefixEnd_1961348 : Nat := 4983230072969 + 3 ^ 40 * 1961348 * 2
def baseEnd_1961348 : Nat := 1007114254734697450629931

theorem tailTrace_1961348 : CollatzResearch.WordTrace tailWord_1961348 prefixEnd_1961348 1007114254734697450629931 := by
  unfold tailWord_1961348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35768119249189321207530349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47690825665585761610040465 35768119249189321207530349)
  ·
    refine ⟨13413044718445995452823881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35768119249189321207530349 13413044718445995452823881)
    ·
      refine ⟨10059783538834496589617911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13413044718445995452823881 10059783538834496589617911)
      ·
        refine ⟨15089675308251744884426867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10059783538834496589617911 15089675308251744884426867)
        ·
          refine ⟨22634512962377617326640301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089675308251744884426867 22634512962377617326640301)
          ·
            refine ⟨8487942360891606497490113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22634512962377617326640301 8487942360891606497490113)
            ·
              refine ⟨6365956770668704873117585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8487942360891606497490113 6365956770668704873117585)
              ·
                refine ⟨4774467578001528654838189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6365956770668704873117585 4774467578001528654838189)
                ·
                  refine ⟨1790425341750573245564321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4774467578001528654838189 1790425341750573245564321)
                  ·
                    refine ⟨1342819006312929934173241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790425341750573245564321 1342819006312929934173241)
                    ·
                      refine ⟨1007114254734697450629931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342819006312929934173241 1007114254734697450629931)
                      ·
                        rfl

theorem cell23_1961348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_1961348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961348 prefixEnd_1961348 := by exact prefixLift 1961348
  have htrace : WordTrace (prefixWord ++ tailWord_1961348) baseStart_1961348 baseEnd_1961348 := by
    simpa [prefixWord, tailWord_1961348, baseEnd_1961348] using wordTrace_append hprefix tailTrace_1961348
  have hstable : (prefixWord ++ tailWord_1961348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961348).length < 2 ^ (prefixWord ++ tailWord_1961348).sum := by decide
  have hdescent : baseEnd_1961348 < baseStart_1961348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961351 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1961351 : Nat := 118140960795 + 1961351 * 2 ^ 59
def prefixEnd_1961351 : Nat := 4983230072969 + 3 ^ 40 * 1961351 * 2
def baseEnd_1961351 : Nat := 1007115795176660938892417

theorem tailTrace_1961351 : CollatzResearch.WordTrace tailWord_1961351 prefixEnd_1961351 1007115795176660938892417 := by
  unfold tailWord_1961351
  simp only [CollatzResearch.WordTrace]
  refine ⟨71536347917367773927419907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47690898611578515951613271 71536347917367773927419907)
  ·
    refine ⟨107304521876051660891129861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71536347917367773927419907 107304521876051660891129861)
    ·
      refine ⟨20119597851759686417086849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107304521876051660891129861 20119597851759686417086849)
      ·
        refine ⟨15089698388819764812815137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20119597851759686417086849 15089698388819764812815137)
        ·
          refine ⟨11317273791614823609611353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15089698388819764812815137 11317273791614823609611353)
          ·
            refine ⟨8487955343711117707208515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317273791614823609611353 8487955343711117707208515)
            ·
              refine ⟨12731933015566676560812773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487955343711117707208515 12731933015566676560812773)
              ·
                refine ⟨2387237440418751855152395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12731933015566676560812773 2387237440418751855152395)
                ·
                  refine ⟨3580856160628127782728593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387237440418751855152395 3580856160628127782728593)
                  ·
                    refine ⟨2685642120471095837046445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580856160628127782728593 2685642120471095837046445)
                    ·
                      refine ⟨1007115795176660938892417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2685642120471095837046445 1007115795176660938892417)
                      ·
                        rfl

theorem cell23_1961351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1961351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961351 prefixEnd_1961351 := by exact prefixLift 1961351
  have htrace : WordTrace (prefixWord ++ tailWord_1961351) baseStart_1961351 baseEnd_1961351 := by
    simpa [prefixWord, tailWord_1961351, baseEnd_1961351] using wordTrace_append hprefix tailTrace_1961351
  have hstable : (prefixWord ++ tailWord_1961351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961351).length < 2 ^ (prefixWord ++ tailWord_1961351).sum := by decide
  have hdescent : baseEnd_1961351 < baseStart_1961351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961365 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_1961365 : Nat := 118140960795 + 1961365 * 2 ^ 59
def prefixEnd_1961365 : Nat := 4983230072969 + 3 ^ 40 * 1961365 * 2
def baseEnd_1961365 : Nat := 1007122983905823884117353

theorem tailTrace_1961365 : CollatzResearch.WordTrace tailWord_1961365 prefixEnd_1961365 1007122983905823884117353 := by
  unfold tailWord_1961365
  simp only [CollatzResearch.WordTrace]
  refine ⟨71536858539317054318429549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47691239026211369545619699 71536858539317054318429549)
  ·
    refine ⟨26826321952243895369411081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71536858539317054318429549 26826321952243895369411081)
    ·
      refine ⟨20119741464182921527058311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26826321952243895369411081 20119741464182921527058311)
      ·
        refine ⟨30179612196274382290587467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119741464182921527058311 30179612196274382290587467)
        ·
          refine ⟨45269418294411573435881201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30179612196274382290587467 45269418294411573435881201)
          ·
            refine ⟨33952063720808680076910901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45269418294411573435881201 33952063720808680076910901)
            ·
              refine ⟨3183005973825813757210397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33952063720808680076910901 3183005973825813757210397)
              ·
                refine ⟨1193627240184680158953899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183005973825813757210397 1193627240184680158953899)
                ·
                  refine ⟨1790440860277020238430849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193627240184680158953899 1790440860277020238430849)
                  ·
                    refine ⟨1342830645207765178823137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790440860277020238430849 1342830645207765178823137)
                    ·
                      refine ⟨1007122983905823884117353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342830645207765178823137 1007122983905823884117353)
                      ·
                        rfl

theorem cell23_1961365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_1961365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961365 prefixEnd_1961365 := by exact prefixLift 1961365
  have htrace : WordTrace (prefixWord ++ tailWord_1961365) baseStart_1961365 baseEnd_1961365 := by
    simpa [prefixWord, tailWord_1961365, baseEnd_1961365] using wordTrace_append hprefix tailTrace_1961365
  have hstable : (prefixWord ++ tailWord_1961365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961365).length < 2 ^ (prefixWord ++ tailWord_1961365).sum := by decide
  have hdescent : baseEnd_1961365 < baseStart_1961365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961367 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 9]
def baseStart_1961367 : Nat := 118140960795 + 1961367 * 2 ^ 59
def prefixEnd_1961367 : Nat := 4983230072969 + 3 ^ 40 * 1961367 * 2
def baseEnd_1961367 : Nat := 335708003622377625430781

theorem tailTrace_1961367 : CollatzResearch.WordTrace tailWord_1961367 prefixEnd_1961367 335708003622377625430781 := by
  unfold tailWord_1961367
  simp only [CollatzResearch.WordTrace]
  refine ⟨71536931485309808660002355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47691287656873205773334903 71536931485309808660002355)
  ·
    refine ⟨107305397227964712990003533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71536931485309808660002355 107305397227964712990003533)
    ·
      refine ⟨40239523960486767371251325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107305397227964712990003533 40239523960486767371251325)
      ·
        refine ⟨15089821485182537764219247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40239523960486767371251325 15089821485182537764219247)
        ·
          refine ⟨22634732227773806646328871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089821485182537764219247 22634732227773806646328871)
          ·
            refine ⟨33952098341660709969493307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22634732227773806646328871 33952098341660709969493307)
            ·
              refine ⟨50928147512491064954239961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33952098341660709969493307 50928147512491064954239961)
              ·
                refine ⟨38196110634368298715679971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50928147512491064954239961 38196110634368298715679971)
                ·
                  refine ⟨57294165951552448073519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38196110634368298715679971 57294165951552448073519957)
                  ·
                    refine ⟨335708003622377625430781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 57294165951552448073519957 335708003622377625430781)
                    ·
                      rfl

theorem cell23_1961367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_1961367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961367 prefixEnd_1961367 := by exact prefixLift 1961367
  have htrace : WordTrace (prefixWord ++ tailWord_1961367) baseStart_1961367 baseEnd_1961367 := by
    simpa [prefixWord, tailWord_1961367, baseEnd_1961367] using wordTrace_append hprefix tailTrace_1961367
  have hstable : (prefixWord ++ tailWord_1961367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961367).length < 2 ^ (prefixWord ++ tailWord_1961367).sum := by decide
  have hdescent : baseEnd_1961367 < baseStart_1961367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961408 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2]
def baseStart_1961408 : Nat := 118140960795 + 1961408 * 2 ^ 59
def prefixEnd_1961408 : Nat := 4983230072969 + 3 ^ 40 * 1961408 * 2
def baseEnd_1961408 : Nat := 1007145063573967215879655

theorem tailTrace_1961408 : CollatzResearch.WordTrace tailWord_1961408 prefixEnd_1961408 1007145063573967215879655 := by
  unfold tailWord_1961408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35769213439080636331122439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47692284585440848441496585 35769213439080636331122439)
  ·
    refine ⟨53653820158620954496683659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35769213439080636331122439 53653820158620954496683659)
    ·
      refine ⟨80480730237931431745025489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53653820158620954496683659 80480730237931431745025489)
      ·
        refine ⟨60360547678448573808769117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80480730237931431745025489 60360547678448573808769117)
        ·
          refine ⟨22635205379418215178288419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60360547678448573808769117 22635205379418215178288419)
          ·
            refine ⟨33952808069127322767432629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22635205379418215178288419 33952808069127322767432629)
            ·
              refine ⟨3183075756480686509446809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33952808069127322767432629 3183075756480686509446809)
              ·
                refine ⟨2387306817360514882085107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183075756480686509446809 2387306817360514882085107)
                ·
                  refine ⟨3580960226040772323127661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387306817360514882085107 3580960226040772323127661)
                  ·
                    refine ⟨1342860084765289621172873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580960226040772323127661 1342860084765289621172873)
                    ·
                      refine ⟨1007145063573967215879655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1342860084765289621172873 1007145063573967215879655)
                      ·
                        rfl

theorem cell23_1961408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_1961408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961408 prefixEnd_1961408 := by exact prefixLift 1961408
  have htrace : WordTrace (prefixWord ++ tailWord_1961408) baseStart_1961408 baseEnd_1961408 := by
    simpa [prefixWord, tailWord_1961408, baseEnd_1961408] using wordTrace_append hprefix tailTrace_1961408
  have hstable : (prefixWord ++ tailWord_1961408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961408).length < 2 ^ (prefixWord ++ tailWord_1961408).sum := by decide
  have hdescent : baseEnd_1961408 < baseStart_1961408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961461 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 9]
def baseStart_1961461 : Nat := 118140960795 + 1961461 * 2 ^ 59
def prefixEnd_1961461 : Nat := 4983230072969 + 3 ^ 40 * 1961461 * 2
def baseEnd_1961461 : Nat := 111908030894295056501879

theorem tailTrace_1961461 : CollatzResearch.WordTrace tailWord_1961461 prefixEnd_1961461 111908030894295056501879 := by
  unfold tailWord_1961461
  simp only [CollatzResearch.WordTrace]
  refine ⟨71540359946969262713924237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47693573297979508475949491 71540359946969262713924237)
  ·
    refine ⟨26827634980113473517721589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71540359946969262713924237 26827634980113473517721589)
    ·
      refine ⟨2515090779385638142286399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26827634980113473517721589 2515090779385638142286399)
      ·
        refine ⟨3772636169078457213429599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515090779385638142286399 3772636169078457213429599)
        ·
          refine ⟨5658954253617685820144399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772636169078457213429599 5658954253617685820144399)
          ·
            refine ⟨8488431380426528730216599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658954253617685820144399 8488431380426528730216599)
            ·
              refine ⟨12732647070639793095324899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488431380426528730216599 12732647070639793095324899)
              ·
                refine ⟨19098970605959689642987349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732647070639793095324899 19098970605959689642987349)
                ·
                  refine ⟨111908030894295056501879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19098970605959689642987349 111908030894295056501879)
                  ·
                    rfl

theorem cell23_1961461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_1961461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961461 prefixEnd_1961461 := by exact prefixLift 1961461
  have htrace : WordTrace (prefixWord ++ tailWord_1961461) baseStart_1961461 baseEnd_1961461 := by
    simpa [prefixWord, tailWord_1961461, baseEnd_1961461] using wordTrace_append hprefix tailTrace_1961461
  have hstable : (prefixWord ++ tailWord_1961461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961461).length < 2 ^ (prefixWord ++ tailWord_1961461).sum := by decide
  have hdescent : baseEnd_1961461 < baseStart_1961461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961548 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1961548 : Nat := 118140960795 + 1961548 * 2 ^ 59
def prefixEnd_1961548 : Nat := 4983230072969 + 3 ^ 40 * 1961548 * 2
def baseEnd_1961548 : Nat := 1007216950865596668129011

theorem tailTrace_1961548 : CollatzResearch.WordTrace tailWord_1961548 prefixEnd_1961548 1007216950865596668129011 := by
  unfold tailWord_1961548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35771766548827038286170649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47695688731769384381560865 35771766548827038286170649)
  ·
    refine ⟨26828824911620278714627987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35771766548827038286170649 26828824911620278714627987)
    ·
      refine ⟨40243237367430418071941981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26828824911620278714627987 40243237367430418071941981)
      ·
        refine ⟨15091214012786406776978243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40243237367430418071941981 15091214012786406776978243)
        ·
          refine ⟨22636821019179610165467365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15091214012786406776978243 22636821019179610165467365)
          ·
            refine ⟨4244403941096176906025131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22636821019179610165467365 4244403941096176906025131)
            ·
              refine ⟨6366605911644265359037697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244403941096176906025131 6366605911644265359037697)
              ·
                refine ⟨4774954433733199019278273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366605911644265359037697 4774954433733199019278273)
                ·
                  refine ⟨3581215825299899264458705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774954433733199019278273 3581215825299899264458705)
                  ·
                    refine ⟨2685911868974924448344029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581215825299899264458705 2685911868974924448344029)
                    ·
                      refine ⟨1007216950865596668129011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2685911868974924448344029 1007216950865596668129011)
                      ·
                        rfl

theorem cell23_1961548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1961548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961548 prefixEnd_1961548 := by exact prefixLift 1961548
  have htrace : WordTrace (prefixWord ++ tailWord_1961548) baseStart_1961548 baseEnd_1961548 := by
    simpa [prefixWord, tailWord_1961548, baseEnd_1961548] using wordTrace_append hprefix tailTrace_1961548
  have hstable : (prefixWord ++ tailWord_1961548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961548).length < 2 ^ (prefixWord ++ tailWord_1961548).sum := by decide
  have hdescent : baseEnd_1961548 < baseStart_1961548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961595 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 1, 1, 3]
def baseStart_1961595 : Nat := 118140960795 + 1961595 * 2 ^ 59
def prefixEnd_1961595 : Nat := 4983230072969 + 3 ^ 40 * 1961595 * 2
def baseEnd_1961595 : Nat := 1007241084456357984241295

theorem tailTrace_1961595 : CollatzResearch.WordTrace tailWord_1961595 prefixEnd_1961595 1007241084456357984241295 := by
  unfold tailWord_1961595
  simp only [CollatzResearch.WordTrace]
  refine ⟨71545247328483803599302239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47696831552322535732868159 71545247328483803599302239)
  ·
    refine ⟨107317870992725705398953359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71545247328483803599302239 107317870992725705398953359)
    ·
      refine ⟨160976806489088558098430039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107317870992725705398953359 160976806489088558098430039)
      ·
        refine ⟨241465209733632837147645059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160976806489088558098430039 241465209733632837147645059)
        ·
          refine ⟨362197814600449255721467589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241465209733632837147645059 362197814600449255721467589)
          ·
            refine ⟨67912090237584235447775173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362197814600449255721467589 67912090237584235447775173)
            ·
              refine ⟨12733516919547044146457845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67912090237584235447775173 12733516919547044146457845)
              ·
                refine ⟨1193767211207535388730423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12733516919547044146457845 1193767211207535388730423)
                ·
                  refine ⟨1790650816811303083095635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193767211207535388730423 1790650816811303083095635)
                  ·
                    refine ⟨2685976225216954624643453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1790650816811303083095635 2685976225216954624643453)
                    ·
                      refine ⟨1007241084456357984241295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2685976225216954624643453 1007241084456357984241295)
                      ·
                        rfl

theorem cell23_1961595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 1, 3].length) (baseStart_1961595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961595 prefixEnd_1961595 := by exact prefixLift 1961595
  have htrace : WordTrace (prefixWord ++ tailWord_1961595) baseStart_1961595 baseEnd_1961595 := by
    simpa [prefixWord, tailWord_1961595, baseEnd_1961595] using wordTrace_append hprefix tailTrace_1961595
  have hstable : (prefixWord ++ tailWord_1961595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961595).length < 2 ^ (prefixWord ++ tailWord_1961595).sum := by decide
  have hdescent : baseEnd_1961595 < baseStart_1961595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961621 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1961621 : Nat := 118140960795 + 1961621 * 2 ^ 59
def prefixEnd_1961621 : Nat := 4983230072969 + 3 ^ 40 * 1961621 * 2
def baseEnd_1961621 : Nat := 1007254434953374882516175

theorem tailTrace_1961621 : CollatzResearch.WordTrace tailWord_1961621 prefixEnd_1961621 1007254434953374882516175 := by
  unfold tailWord_1961621
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546195626389610039748717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47697463750926406693165811 71546195626389610039748717)
  ·
    refine ⟨26829823359896103764905769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71546195626389610039748717 26829823359896103764905769)
    ·
      refine ⟨20122367519922077823679327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26829823359896103764905769 20122367519922077823679327)
      ·
        refine ⟨30183551279883116735518991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20122367519922077823679327 30183551279883116735518991)
        ·
          refine ⟨45275326919824675103278487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30183551279883116735518991 45275326919824675103278487)
          ·
            refine ⟨67912990379737012654917731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45275326919824675103278487 67912990379737012654917731)
            ·
              refine ⟨101869485569605518982376597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67912990379737012654917731 101869485569605518982376597)
              ·
                refine ⟨4775132136075258702298903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101869485569605518982376597 4775132136075258702298903)
                ·
                  refine ⟨7162698204112888053448355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775132136075258702298903 7162698204112888053448355)
                  ·
                    refine ⟨10744047306169332080172533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7162698204112888053448355 10744047306169332080172533)
                    ·
                      refine ⟨1007254434953374882516175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10744047306169332080172533 1007254434953374882516175)
                      ·
                        rfl

theorem cell23_1961621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1961621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961621 prefixEnd_1961621 := by exact prefixLift 1961621
  have htrace : WordTrace (prefixWord ++ tailWord_1961621) baseStart_1961621 baseEnd_1961621 := by
    simpa [prefixWord, tailWord_1961621, baseEnd_1961621] using wordTrace_append hprefix tailTrace_1961621
  have hstable : (prefixWord ++ tailWord_1961621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961621).length < 2 ^ (prefixWord ++ tailWord_1961621).sum := by decide
  have hdescent : baseEnd_1961621 < baseStart_1961621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961635 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 3, 2, 2]
def baseStart_1961635 : Nat := 118140960795 + 1961635 * 2 ^ 59
def prefixEnd_1961635 : Nat := 4983230072969 + 3 ^ 40 * 1961635 * 2
def baseEnd_1961635 : Nat := 1007261623682537827741111

theorem tailTrace_1961635 : CollatzResearch.WordTrace tailWord_1961635 prefixEnd_1961635 1007261623682537827741111 := by
  unfold tailWord_1961635
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546706248338890430758359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47697804165559260287172239 71546706248338890430758359)
  ·
    refine ⟨107320059372508335646137539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71546706248338890430758359 107320059372508335646137539)
    ·
      refine ⟨160980089058762503469206309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107320059372508335646137539 160980089058762503469206309)
      ·
        refine ⟨30183766698517969400476183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160980089058762503469206309 30183766698517969400476183)
        ·
          refine ⟨45275650047776954100714275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30183766698517969400476183 45275650047776954100714275)
          ·
            refine ⟨67913475071665431151071413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45275650047776954100714275 67913475071665431151071413)
            ·
              refine ⟨6366888287968634170412945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67913475071665431151071413 6366888287968634170412945)
              ·
                refine ⟨4775166215976475627809709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366888287968634170412945 4775166215976475627809709)
                ·
                  refine ⟨1790687330991178360428641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4775166215976475627809709 1790687330991178360428641)
                  ·
                    refine ⟨1343015498243383770321481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790687330991178360428641 1343015498243383770321481)
                    ·
                      refine ⟨1007261623682537827741111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343015498243383770321481 1007261623682537827741111)
                      ·
                        rfl

theorem cell23_1961635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_1961635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961635 prefixEnd_1961635 := by exact prefixLift 1961635
  have htrace : WordTrace (prefixWord ++ tailWord_1961635) baseStart_1961635 baseEnd_1961635 := by
    simpa [prefixWord, tailWord_1961635, baseEnd_1961635] using wordTrace_append hprefix tailTrace_1961635
  have hstable : (prefixWord ++ tailWord_1961635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961635).length < 2 ^ (prefixWord ++ tailWord_1961635).sum := by decide
  have hdescent : baseEnd_1961635 < baseStart_1961635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961646 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1961646 : Nat := 118140960795 + 1961646 * 2 ^ 59
def prefixEnd_1961646 : Nat := 4983230072969 + 3 ^ 40 * 1961646 * 2
def baseEnd_1961646 : Nat := 1007267271969737284703561

theorem tailTrace_1961646 : CollatzResearch.WordTrace tailWord_1961646 prefixEnd_1961646 1007267271969737284703561 := by
  unfold tailWord_1961646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943388431412379913676099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47698071634199359539605861 8943388431412379913676099)
  ·
    refine ⟨13415082647118569870514149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8943388431412379913676099 13415082647118569870514149)
    ·
      refine ⟨2515327996334731850721403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13415082647118569870514149 2515327996334731850721403)
      ·
        refine ⟨3772991994502097776082105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515327996334731850721403 3772991994502097776082105)
        ·
          refine ⟨2829743995876573332061579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3772991994502097776082105 2829743995876573332061579)
          ·
            refine ⟨4244615993814859998092369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829743995876573332061579 4244615993814859998092369)
            ·
              refine ⟨3183461995361144998569277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244615993814859998092369 3183461995361144998569277)
              ·
                refine ⟨1193798248260429374463479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183461995361144998569277 1193798248260429374463479)
                ·
                  refine ⟨1790697372390644061695219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193798248260429374463479 1790697372390644061695219)
                  ·
                    refine ⟨2686046058585966092542829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1790697372390644061695219 2686046058585966092542829)
                    ·
                      refine ⟨1007267271969737284703561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686046058585966092542829 1007267271969737284703561)
                      ·
                        rfl

theorem cell23_1961646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1961646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961646 prefixEnd_1961646 := by exact prefixLift 1961646
  have htrace : WordTrace (prefixWord ++ tailWord_1961646) baseStart_1961646 baseEnd_1961646 := by
    simpa [prefixWord, tailWord_1961646, baseEnd_1961646] using wordTrace_append hprefix tailTrace_1961646
  have hstable : (prefixWord ++ tailWord_1961646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961646).length < 2 ^ (prefixWord ++ tailWord_1961646).sum := by decide
  have hdescent : baseEnd_1961646 < baseStart_1961646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961655 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_1961655 : Nat := 118140960795 + 1961655 * 2 ^ 59
def prefixEnd_1961655 : Nat := 4983230072969 + 3 ^ 40 * 1961655 * 2
def baseEnd_1961655 : Nat := 1007271893295627749491019

theorem tailTrace_1961655 : CollatzResearch.WordTrace tailWord_1961655 prefixEnd_1961655 1007271893295627749491019 := by
  unfold tailWord_1961655
  simp only [CollatzResearch.WordTrace]
  refine ⟨71547435708266433846486419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47698290472177622564324279 71547435708266433846486419)
  ·
    refine ⟨107321153562399650769729629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71547435708266433846486419 107321153562399650769729629)
    ·
      refine ⟨40245432585899869038648611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107321153562399650769729629 40245432585899869038648611)
      ·
        refine ⟨60368148878849803557972917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40245432585899869038648611 60368148878849803557972917)
        ·
          refine ⟨5659513957392169083559961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60368148878849803557972917 5659513957392169083559961)
          ·
            refine ⟨4244635468044126812669971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5659513957392169083559961 4244635468044126812669971)
            ·
              refine ⟨6366953202066190219004957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244635468044126812669971 6366953202066190219004957)
              ·
                refine ⟨2387607450774821332126859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6366953202066190219004957 2387607450774821332126859)
                ·
                  refine ⟨3581411176162231998190289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387607450774821332126859 3581411176162231998190289)
                  ·
                    refine ⟨2686058382121673998642717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581411176162231998190289 2686058382121673998642717)
                    ·
                      refine ⟨1007271893295627749491019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686058382121673998642717 1007271893295627749491019)
                      ·
                        rfl

theorem cell23_1961655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_1961655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961655 prefixEnd_1961655 := by exact prefixLift 1961655
  have htrace : WordTrace (prefixWord ++ tailWord_1961655) baseStart_1961655 baseEnd_1961655 := by
    simpa [prefixWord, tailWord_1961655, baseEnd_1961655] using wordTrace_append hprefix tailTrace_1961655
  have hstable : (prefixWord ++ tailWord_1961655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961655).length < 2 ^ (prefixWord ++ tailWord_1961655).sum := by decide
  have hdescent : baseEnd_1961655 < baseStart_1961655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961662 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1961662 : Nat := 118140960795 + 1961662 * 2 ^ 59
def prefixEnd_1961662 : Nat := 4983230072969 + 3 ^ 40 * 1961662 * 2
def baseEnd_1961662 : Nat := 335758495886736407367829

theorem tailTrace_1961662 : CollatzResearch.WordTrace tailWord_1961662 prefixEnd_1961662 335758495886736407367829 := by
  unfold tailWord_1961662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943461377405134255248905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47698460679494049361327493 8943461377405134255248905)
  ·
    refine ⟨6707596033053850691436679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8943461377405134255248905 6707596033053850691436679)
    ·
      refine ⟨10061394049580776037155019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6707596033053850691436679 10061394049580776037155019)
      ·
        refine ⟨15092091074371164055732529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061394049580776037155019 15092091074371164055732529)
        ·
          refine ⟨11319068305778373041799397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15092091074371164055732529 11319068305778373041799397)
          ·
            refine ⟨2122325307333444945337387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11319068305778373041799397 2122325307333444945337387)
            ·
              refine ⟨3183487961000167418006081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122325307333444945337387 3183487961000167418006081)
              ·
                refine ⟨2387615970750125563504561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183487961000167418006081 2387615970750125563504561)
                ·
                  refine ⟨1790711978062594172628421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2387615970750125563504561 1790711978062594172628421)
                  ·
                    refine ⟨335758495886736407367829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1790711978062594172628421 335758495886736407367829)
                    ·
                      rfl

theorem cell23_1961662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1961662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961662 prefixEnd_1961662 := by exact prefixLift 1961662
  have htrace : WordTrace (prefixWord ++ tailWord_1961662) baseStart_1961662 baseEnd_1961662 := by
    simpa [prefixWord, tailWord_1961662, baseEnd_1961662] using wordTrace_append hprefix tailTrace_1961662
  have hstable : (prefixWord ++ tailWord_1961662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961662).length < 2 ^ (prefixWord ++ tailWord_1961662).sum := by decide
  have hdescent : baseEnd_1961662 < baseStart_1961662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961692 : List Nat := [2, 2, 5, 1, 2, 2, 2, 7]
def baseStart_1961692 : Nat := 118140960795 + 1961692 * 2 ^ 59
def prefixEnd_1961692 : Nat := 4983230072969 + 3 ^ 40 * 1961692 * 2
def baseEnd_1961692 : Nat := 37307070077031263138087

theorem tailTrace_1961692 : CollatzResearch.WordTrace tailWord_1961692 prefixEnd_1961692 37307070077031263138087 := by
  unfold tailWord_1961692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35774392604566194582791665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47699190139421592777055553 35774392604566194582791665)
  ·
    refine ⟨26830794453424645937093749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35774392604566194582791665 26830794453424645937093749)
    ·
      refine ⟨2515386980008560556602539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26830794453424645937093749 2515386980008560556602539)
      ·
        refine ⟨3773080470012840834903809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515386980008560556602539 3773080470012840834903809)
        ·
          refine ⟨2829810352509630626177857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3773080470012840834903809 2829810352509630626177857)
          ·
            refine ⟨2122357764382222969633393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829810352509630626177857 2122357764382222969633393)
            ·
              refine ⟨1591768323286667227225045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122357764382222969633393 1591768323286667227225045)
              ·
                refine ⟨37307070077031263138087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1591768323286667227225045 37307070077031263138087)
                ·
                  rfl

theorem cell23_1961692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 7].length) (baseStart_1961692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961692 prefixEnd_1961692 := by exact prefixLift 1961692
  have htrace : WordTrace (prefixWord ++ tailWord_1961692) baseStart_1961692 baseEnd_1961692 := by
    simpa [prefixWord, tailWord_1961692, baseEnd_1961692] using wordTrace_append hprefix tailTrace_1961692
  have hstable : (prefixWord ++ tailWord_1961692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961692).length < 2 ^ (prefixWord ++ tailWord_1961692).sum := by decide
  have hdescent : baseEnd_1961692 < baseStart_1961692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961703 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1961703 : Nat := 118140960795 + 1961703 * 2 ^ 59
def prefixEnd_1961703 : Nat := 4983230072969 + 3 ^ 40 * 1961703 * 2
def baseEnd_1961703 : Nat := 1007296540367043561690799

theorem tailTrace_1961703 : CollatzResearch.WordTrace tailWord_1961703 prefixEnd_1961703 1007296540367043561690799 := by
  unfold tailWord_1961703
  simp only [CollatzResearch.WordTrace]
  refine ⟨71549186412092538044233763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47699457608061692029489175 71549186412092538044233763)
  ·
    refine ⟨107323779618138807066350645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71549186412092538044233763 107323779618138807066350645)
    ·
      refine ⟨10061604339200513162470373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107323779618138807066350645 10061604339200513162470373)
      ·
        refine ⟨1886550813600096217963195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10061604339200513162470373 1886550813600096217963195)
        ·
          refine ⟨2829826220400144326944793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886550813600096217963195 2829826220400144326944793)
          ·
            refine ⟨2122369665300108245208595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829826220400144326944793 2122369665300108245208595)
            ·
              refine ⟨3183554497950162367812893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122369665300108245208595 3183554497950162367812893)
              ·
                refine ⟨1193832936731310887929835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183554497950162367812893 1193832936731310887929835)
                ·
                  refine ⟨1790749405096966331894753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193832936731310887929835 1790749405096966331894753)
                  ·
                    refine ⟨1343062053822724748921065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790749405096966331894753 1343062053822724748921065)
                    ·
                      refine ⟨1007296540367043561690799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343062053822724748921065 1007296540367043561690799)
                      ·
                        rfl

theorem cell23_1961703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1961703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961703 prefixEnd_1961703 := by exact prefixLift 1961703
  have htrace : WordTrace (prefixWord ++ tailWord_1961703) baseStart_1961703 baseEnd_1961703 := by
    simpa [prefixWord, tailWord_1961703, baseEnd_1961703] using wordTrace_append hprefix tailTrace_1961703
  have hstable : (prefixWord ++ tailWord_1961703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961703).length < 2 ^ (prefixWord ++ tailWord_1961703).sum := by decide
  have hdescent : baseEnd_1961703 < baseStart_1961703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961746 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1961746 : Nat := 118140960795 + 1961746 * 2 ^ 59
def prefixEnd_1961746 : Nat := 4983230072969 + 3 ^ 40 * 1961746 * 2
def baseEnd_1961746 : Nat := 1007318620035186893453101

theorem tailTrace_1961746 : CollatzResearch.WordTrace tailWord_1961746 prefixEnd_1961746 1007318620035186893453101 := by
  unfold tailWord_1961746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887688687734189097012273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47700503167291170925366061 17887688687734189097012273)
  ·
    refine ⟨13415766515800641822759205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17887688687734189097012273 13415766515800641822759205)
    ·
      refine ⟨2515456221712620341767351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13415766515800641822759205 2515456221712620341767351)
      ·
        refine ⟨3773184332568930512651027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515456221712620341767351 3773184332568930512651027)
        ·
          refine ⟨5659776498853395768976541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773184332568930512651027 5659776498853395768976541)
          ·
            refine ⟨2122416187070023413366203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5659776498853395768976541 2122416187070023413366203)
            ·
              refine ⟨3183624280605035120049305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122416187070023413366203 3183624280605035120049305)
              ·
                refine ⟨2387718210453776340036979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183624280605035120049305 2387718210453776340036979)
                ·
                  refine ⟨3581577315680664510055469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387718210453776340036979 3581577315680664510055469)
                  ·
                    refine ⟨1343091493380249191270801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581577315680664510055469 1343091493380249191270801)
                    ·
                      refine ⟨1007318620035186893453101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343091493380249191270801 1007318620035186893453101)
                      ·
                        rfl

theorem cell23_1961746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1961746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961746 prefixEnd_1961746 := by exact prefixLift 1961746
  have htrace : WordTrace (prefixWord ++ tailWord_1961746) baseStart_1961746 baseEnd_1961746 := by
    simpa [prefixWord, tailWord_1961746, baseEnd_1961746] using wordTrace_append hprefix tailTrace_1961746
  have hstable : (prefixWord ++ tailWord_1961746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961746).length < 2 ^ (prefixWord ++ tailWord_1961746).sum := by decide
  have hdescent : baseEnd_1961746 < baseStart_1961746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961788 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1961788 : Nat := 118140960795 + 1961788 * 2 ^ 59
def prefixEnd_1961788 : Nat := 4983230072969 + 3 ^ 40 * 1961788 * 2
def baseEnd_1961788 : Nat := 1007340186222675729127907

theorem tailTrace_1961788 : CollatzResearch.WordTrace tailWord_1961788 prefixEnd_1961788 1007340186222675729127907 := by
  unfold tailWord_1961788
  simp only [CollatzResearch.WordTrace]
  refine ⟨35776143308392298780539009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47701524411189731707385345 35776143308392298780539009)
  ·
    refine ⟨26832107481294224085404257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35776143308392298780539009 26832107481294224085404257)
    ·
      refine ⟨20124080610970668064053193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26832107481294224085404257 20124080610970668064053193)
      ·
        refine ⟨15093060458228001048039895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20124080610970668064053193 15093060458228001048039895)
        ·
          refine ⟨22639590687342001572059843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15093060458228001048039895 22639590687342001572059843)
          ·
            refine ⟨33959386031013002358089765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22639590687342001572059843 33959386031013002358089765)
            ·
              refine ⟨6367384880814937942141831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33959386031013002358089765 6367384880814937942141831)
              ·
                refine ⟨9551077321222406913212747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367384880814937942141831 9551077321222406913212747)
                ·
                  refine ⟨14326615981833610369819121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551077321222406913212747 14326615981833610369819121)
                  ·
                    refine ⟨10744961986375207777364341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14326615981833610369819121 10744961986375207777364341)
                    ·
                      refine ⟨1007340186222675729127907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10744961986375207777364341 1007340186222675729127907)
                      ·
                        rfl

theorem cell23_1961788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1961788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961788 prefixEnd_1961788 := by exact prefixLift 1961788
  have htrace : WordTrace (prefixWord ++ tailWord_1961788) baseStart_1961788 baseEnd_1961788 := by
    simpa [prefixWord, tailWord_1961788, baseEnd_1961788] using wordTrace_append hprefix tailTrace_1961788
  have hstable : (prefixWord ++ tailWord_1961788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961788).length < 2 ^ (prefixWord ++ tailWord_1961788).sum := by decide
  have hdescent : baseEnd_1961788 < baseStart_1961788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961812 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1961812 : Nat := 118140960795 + 1961812 * 2 ^ 59
def prefixEnd_1961812 : Nat := 4983230072969 + 3 ^ 40 * 1961812 * 2
def baseEnd_1961812 : Nat := 335784169919461211742599

theorem tailTrace_1961812 : CollatzResearch.WordTrace tailWord_1961812 prefixEnd_1961812 335784169919461211742599 := by
  unfold tailWord_1961812
  simp only [CollatzResearch.WordTrace]
  refine ⟨35776580984348824829975845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47702107979131766439967793 35776580984348824829975845)
  ·
    refine ⟨6708108934565404655620471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35776580984348824829975845 6708108934565404655620471)
    ·
      refine ⟨10062163401848106983430707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708108934565404655620471 10062163401848106983430707)
      ·
        refine ⟨15093245102772160475146061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10062163401848106983430707 15093245102772160475146061)
        ·
          refine ⟨5659966913539560178179773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15093245102772160475146061 5659966913539560178179773)
          ·
            refine ⟨2122487592577335066817415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5659966913539560178179773 2122487592577335066817415)
            ·
              refine ⟨3183731388866002600226123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122487592577335066817415 3183731388866002600226123)
              ·
                refine ⟨4775597083299003900339185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183731388866002600226123 4775597083299003900339185)
                ·
                  refine ⟨3581697812474252925254389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4775597083299003900339185 3581697812474252925254389)
                  ·
                    refine ⟨335784169919461211742599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3581697812474252925254389 335784169919461211742599)
                    ·
                      rfl

theorem cell23_1961812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1961812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961812 prefixEnd_1961812 := by exact prefixLift 1961812
  have htrace : WordTrace (prefixWord ++ tailWord_1961812) baseStart_1961812 baseEnd_1961812 := by
    simpa [prefixWord, tailWord_1961812, baseEnd_1961812] using wordTrace_append hprefix tailTrace_1961812
  have hstable : (prefixWord ++ tailWord_1961812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961812).length < 2 ^ (prefixWord ++ tailWord_1961812).sum := by decide
  have hdescent : baseEnd_1961812 < baseStart_1961812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961815 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1961815 : Nat := 118140960795 + 1961815 * 2 ^ 59
def prefixEnd_1961815 : Nat := 4983230072969 + 3 ^ 40 * 1961815 * 2
def baseEnd_1961815 : Nat := 1007354050200347123490283

theorem tailTrace_1961815 : CollatzResearch.WordTrace tailWord_1961815 prefixEnd_1961815 1007354050200347123490283 := by
  unfold tailWord_1961815
  simp only [CollatzResearch.WordTrace]
  refine ⟨71553271387686781172310899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47702180925124520781540599 71553271387686781172310899)
  ·
    refine ⟨107329907081530171758466349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71553271387686781172310899 107329907081530171758466349)
    ·
      refine ⟨40248715155573814409424881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107329907081530171758466349 40248715155573814409424881)
      ·
        refine ⟨30186536366680360807068661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40248715155573814409424881 30186536366680360807068661)
        ·
          refine ⟨2829987784376283825662687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30186536366680360807068661 2829987784376283825662687)
          ·
            refine ⟨4244981676564425738494031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829987784376283825662687 4244981676564425738494031)
            ·
              refine ⟨6367472514846638607741047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244981676564425738494031 6367472514846638607741047)
              ·
                refine ⟨9551208772269957911611571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367472514846638607741047 9551208772269957911611571)
                ·
                  refine ⟨14326813158404936867417357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551208772269957911611571 14326813158404936867417357)
                  ·
                    refine ⟨5372554934401851325281509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14326813158404936867417357 5372554934401851325281509)
                    ·
                      refine ⟨1007354050200347123490283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5372554934401851325281509 1007354050200347123490283)
                      ·
                        rfl

theorem cell23_1961815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1961815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961815 prefixEnd_1961815 := by exact prefixLift 1961815
  have htrace : WordTrace (prefixWord ++ tailWord_1961815) baseStart_1961815 baseEnd_1961815 := by
    simpa [prefixWord, tailWord_1961815, baseEnd_1961815] using wordTrace_append hprefix tailTrace_1961815
  have hstable : (prefixWord ++ tailWord_1961815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961815).length < 2 ^ (prefixWord ++ tailWord_1961815).sum := by decide
  have hdescent : baseEnd_1961815 < baseStart_1961815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961876 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1961876 : Nat := 118140960795 + 1961876 * 2 ^ 59
def prefixEnd_1961876 : Nat := 4983230072969 + 3 ^ 40 * 1961876 * 2
def baseEnd_1961876 : Nat := 335795124173423794942501

theorem tailTrace_1961876 : CollatzResearch.WordTrace tailWord_1961876 prefixEnd_1961876 335795124173423794942501 := by
  unfold tailWord_1961876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35777748120232894295140741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47703664160310525726854321 35777748120232894295140741)
  ·
    refine ⟨6708327772543667680338889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35777748120232894295140741 6708327772543667680338889)
    ·
      refine ⟨5031245829407750760254167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6708327772543667680338889 5031245829407750760254167)
      ·
        refine ⟨7546868744111626140381251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031245829407750760254167 7546868744111626140381251)
        ·
          refine ⟨11320303116167439210571877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546868744111626140381251 11320303116167439210571877)
          ·
            refine ⟨2122556834281394851982227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11320303116167439210571877 2122556834281394851982227)
            ·
              refine ⟨3183835251422092277973341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122556834281394851982227 3183835251422092277973341)
              ·
                refine ⟨1193938219283284604240003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183835251422092277973341 1193938219283284604240003)
                ·
                  refine ⟨1790907328924926906360005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193938219283284604240003 1790907328924926906360005)
                  ·
                    refine ⟨335795124173423794942501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1790907328924926906360005 335795124173423794942501)
                    ·
                      rfl

theorem cell23_1961876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1961876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961876 prefixEnd_1961876 := by exact prefixLift 1961876
  have htrace : WordTrace (prefixWord ++ tailWord_1961876) baseStart_1961876 baseEnd_1961876 := by
    simpa [prefixWord, tailWord_1961876, baseEnd_1961876] using wordTrace_append hprefix tailTrace_1961876
  have hstable : (prefixWord ++ tailWord_1961876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961876).length < 2 ^ (prefixWord ++ tailWord_1961876).sum := by decide
  have hdescent : baseEnd_1961876 < baseStart_1961876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961886 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1961886 : Nat := 118140960795 + 1961886 * 2 ^ 59
def prefixEnd_1961886 : Nat := 4983230072969 + 3 ^ 40 * 1961886 * 2
def baseEnd_1961886 : Nat := 1007390507326816345702457

theorem tailTrace_1961886 : CollatzResearch.WordTrace tailWord_1961886 prefixEnd_1961886 1007390507326816345702457 := by
  unfold tailWord_1961886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8944482621303695037268189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47703907313619706865430341 8944482621303695037268189)
  ·
    refine ⟨3354180982988885638975571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8944482621303695037268189 3354180982988885638975571)
    ·
      refine ⟨5031271474483328458463357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3354180982988885638975571 5031271474483328458463357)
      ·
        refine ⟨1886726802931248171923759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5031271474483328458463357 1886726802931248171923759)
        ·
          refine ⟨2830090204396872257885639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886726802931248171923759 2830090204396872257885639)
          ·
            refine ⟨4245135306595308386828459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830090204396872257885639 4245135306595308386828459)
            ·
              refine ⟨6367702959892962580242689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245135306595308386828459 6367702959892962580242689)
              ·
                refine ⟨4775777219919721935182017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6367702959892962580242689 4775777219919721935182017)
                ·
                  refine ⟨3581832914939791451386513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4775777219919721935182017 3581832914939791451386513)
                  ·
                    refine ⟨2686374686204843588539885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581832914939791451386513 2686374686204843588539885)
                    ·
                      refine ⟨1007390507326816345702457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686374686204843588539885 1007390507326816345702457)
                      ·
                        rfl

theorem cell23_1961886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1961886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961886 prefixEnd_1961886 := by exact prefixLift 1961886
  have htrace : WordTrace (prefixWord ++ tailWord_1961886) baseStart_1961886 baseEnd_1961886 := by
    simpa [prefixWord, tailWord_1961886, baseEnd_1961886] using wordTrace_append hprefix tailTrace_1961886
  have hstable : (prefixWord ++ tailWord_1961886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961886).length < 2 ^ (prefixWord ++ tailWord_1961886).sum := by decide
  have hdescent : baseEnd_1961886 < baseStart_1961886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961892 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_1961892 : Nat := 118140960795 + 1961892 * 2 ^ 59
def prefixEnd_1961892 : Nat := 4983230072969 + 3 ^ 40 * 1961892 * 2
def baseEnd_1961892 : Nat := 1007393588210743322227429

theorem tailTrace_1961892 : CollatzResearch.WordTrace tailWord_1961892 prefixEnd_1961892 1007393588210743322227429 := by
  unfold tailWord_1961892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35778039904203911661431965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47704053205605215548575953 35778039904203911661431965)
  ·
    refine ⟨13416764964076466873036987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35778039904203911661431965 13416764964076466873036987)
    ·
      refine ⟨20125147446114700309555481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13416764964076466873036987 20125147446114700309555481)
      ·
        refine ⟨15093860584586025232166611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20125147446114700309555481 15093860584586025232166611)
        ·
          refine ⟨22640790876879037848249917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15093860584586025232166611 22640790876879037848249917)
          ·
            refine ⟨8490296578829639193093719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22640790876879037848249917 8490296578829639193093719)
            ·
              refine ⟨12735444868244458789640579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490296578829639193093719 12735444868244458789640579)
              ·
                refine ⟨19103167302366688184460869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735444868244458789640579 19103167302366688184460869)
                ·
                  refine ⟨3581843869193754034586413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19103167302366688184460869 3581843869193754034586413)
                  ·
                    refine ⟨1343191450947657762969905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581843869193754034586413 1343191450947657762969905)
                    ·
                      refine ⟨1007393588210743322227429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343191450947657762969905 1007393588210743322227429)
                      ·
                        rfl

theorem cell23_1961892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_1961892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961892 prefixEnd_1961892 := by exact prefixLift 1961892
  have htrace : WordTrace (prefixWord ++ tailWord_1961892) baseStart_1961892 baseEnd_1961892 := by
    simpa [prefixWord, tailWord_1961892, baseEnd_1961892] using wordTrace_append hprefix tailTrace_1961892
  have hstable : (prefixWord ++ tailWord_1961892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961892).length < 2 ^ (prefixWord ++ tailWord_1961892).sum := by decide
  have hdescent : baseEnd_1961892 < baseStart_1961892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961935 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_1961935 : Nat := 118140960795 + 1961935 * 2 ^ 59
def prefixEnd_1961935 : Nat := 4983230072969 + 3 ^ 40 * 1961935 * 2
def baseEnd_1961935 : Nat := 1007415667878886653989731

theorem tailTrace_1961935 : CollatzResearch.WordTrace tailWord_1961935 prefixEnd_1961935 1007415667878886653989731 := by
  unfold tailWord_1961935
  simp only [CollatzResearch.WordTrace]
  refine ⟨71557648147252041666679259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47705098764834694444452839 71557648147252041666679259)
  ·
    refine ⟨107336472220878062500018889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71557648147252041666679259 107336472220878062500018889)
    ·
      refine ⟨80502354165658546875014167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107336472220878062500018889 80502354165658546875014167)
      ·
        refine ⟨120753531248487820312521251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80502354165658546875014167 120753531248487820312521251)
        ·
          refine ⟨181130296872731730468781877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120753531248487820312521251 181130296872731730468781877)
          ·
            refine ⟨16980965331818599731448301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181130296872731730468781877 16980965331818599731448301)
            ·
              refine ⟨6367861999431974899293113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16980965331818599731448301 6367861999431974899293113)
              ·
                refine ⟨4775896499573981174469835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6367861999431974899293113 4775896499573981174469835)
                ·
                  refine ⟨7163844749360971761704753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775896499573981174469835 7163844749360971761704753)
                  ·
                    refine ⟨5372883562020728821278565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7163844749360971761704753 5372883562020728821278565)
                    ·
                      refine ⟨1007415667878886653989731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5372883562020728821278565 1007415667878886653989731)
                      ·
                        rfl

theorem cell23_1961935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_1961935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961935 prefixEnd_1961935 := by exact prefixLift 1961935
  have htrace : WordTrace (prefixWord ++ tailWord_1961935) baseStart_1961935 baseEnd_1961935 := by
    simpa [prefixWord, tailWord_1961935, baseEnd_1961935] using wordTrace_append hprefix tailTrace_1961935
  have hstable : (prefixWord ++ tailWord_1961935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961935).length < 2 ^ (prefixWord ++ tailWord_1961935).sum := by decide
  have hdescent : baseEnd_1961935 < baseStart_1961935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961945 : List Nat := [1, 2, 1, 2, 7, 10]
def baseStart_1961945 : Nat := 118140960795 + 1961945 * 2 ^ 59
def prefixEnd_1961945 : Nat := 4983230072969 + 3 ^ 40 * 1961945 * 2
def baseEnd_1961945 : Nat := 4145764620104656851295

theorem tailTrace_1961945 : CollatzResearch.WordTrace tailWord_1961945 prefixEnd_1961945 4145764620104656851295 := by
  unfold tailWord_1961945
  simp only [CollatzResearch.WordTrace]
  refine ⟨71558012877215813374543289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47705341918143875583028859 71558012877215813374543289)
  ·
    refine ⟨53668509657911860030907467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71558012877215813374543289 53668509657911860030907467)
    ·
      refine ⟨80502764486867790046361201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53668509657911860030907467 80502764486867790046361201)
      ·
        refine ⟨60377073365150842534770901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80502764486867790046361201 60377073365150842534770901)
        ·
          refine ⟨1415087656995722871908693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60377073365150842534770901 1415087656995722871908693)
          ·
            refine ⟨4145764620104656851295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1415087656995722871908693 4145764620104656851295)
            ·
              rfl

theorem cell23_1961945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 10].length) (baseStart_1961945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961945 prefixEnd_1961945 := by exact prefixLift 1961945
  have htrace : WordTrace (prefixWord ++ tailWord_1961945) baseStart_1961945 baseEnd_1961945 := by
    simpa [prefixWord, tailWord_1961945, baseEnd_1961945] using wordTrace_append hprefix tailTrace_1961945
  have hstable : (prefixWord ++ tailWord_1961945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961945).length < 2 ^ (prefixWord ++ tailWord_1961945).sum := by decide
  have hdescent : baseEnd_1961945 < baseStart_1961945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961956 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_1961956 : Nat := 118140960795 + 1961956 * 2 ^ 59
def prefixEnd_1961956 : Nat := 4983230072969 + 3 ^ 40 * 1961956 * 2
def baseEnd_1961956 : Nat := 1007426450972631071827135

theorem tailTrace_1961956 : CollatzResearch.WordTrace tailWord_1961956 prefixEnd_1961956 1007426450972631071827135 := by
  unfold tailWord_1961956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35779207040087981126596861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47705609386783974835462481 35779207040087981126596861)
  ·
    refine ⟨13417202640032992922473823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35779207040087981126596861 13417202640032992922473823)
    ·
      refine ⟨20125803960049489383710735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13417202640032992922473823 20125803960049489383710735)
      ·
        refine ⟨30188705940074234075566103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20125803960049489383710735 30188705940074234075566103)
        ·
          refine ⟨45283058910111351113349155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30188705940074234075566103 45283058910111351113349155)
          ·
            refine ⟨67924588365167026670023733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45283058910111351113349155 67924588365167026670023733)
            ·
              refine ⟨6367930159234408750314725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67924588365167026670023733 6367930159234408750314725)
              ·
                refine ⟨1193986904856451640684011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6367930159234408750314725 1193986904856451640684011)
                ·
                  refine ⟨1790980357284677461026017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193986904856451640684011 1790980357284677461026017)
                  ·
                    refine ⟨1343235267963508095769513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1790980357284677461026017 1343235267963508095769513)
                    ·
                      refine ⟨1007426450972631071827135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343235267963508095769513 1007426450972631071827135)
                      ·
                        rfl

theorem cell23_1961956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_1961956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961956 prefixEnd_1961956 := by exact prefixLift 1961956
  have htrace : WordTrace (prefixWord ++ tailWord_1961956) baseStart_1961956 baseEnd_1961956 := by
    simpa [prefixWord, tailWord_1961956, baseEnd_1961956] using wordTrace_append hprefix tailTrace_1961956
  have hstable : (prefixWord ++ tailWord_1961956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961956).length < 2 ^ (prefixWord ++ tailWord_1961956).sum := by decide
  have hdescent : baseEnd_1961956 < baseStart_1961956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961985 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1961985 : Nat := 118140960795 + 1961985 * 2 ^ 59
def prefixEnd_1961985 : Nat := 4983230072969 + 3 ^ 40 * 1961985 * 2
def baseEnd_1961985 : Nat := 1007441341911611458364501

theorem tailTrace_1961985 : CollatzResearch.WordTrace tailWord_1961985 prefixEnd_1961985 1007441341911611458364501 := by
  unfold tailWord_1961985
  simp only [CollatzResearch.WordTrace]
  refine ⟨71559471797070900205999409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47706314531380600137332939 71559471797070900205999409)
  ·
    refine ⟨53669603847803175154499557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71559471797070900205999409 53669603847803175154499557)
    ·
      refine ⟨10063050721463095341468667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53669603847803175154499557 10063050721463095341468667)
      ·
        refine ⟨15094576082194643012203001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10063050721463095341468667 15094576082194643012203001)
        ·
          refine ⟨11320932061645982259152251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15094576082194643012203001 11320932061645982259152251)
          ·
            refine ⟨16981398092468973388728377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11320932061645982259152251 16981398092468973388728377)
            ·
              refine ⟨12736048569351730041546283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16981398092468973388728377 12736048569351730041546283)
              ·
                refine ⟨19104072854027595062319425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736048569351730041546283 19104072854027595062319425)
                ·
                  refine ⟨14328054640520696296739569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19104072854027595062319425 14328054640520696296739569)
                  ·
                    refine ⟨10746040980390522222554677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14328054640520696296739569 10746040980390522222554677)
                    ·
                      refine ⟨1007441341911611458364501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10746040980390522222554677 1007441341911611458364501)
                      ·
                        rfl

theorem cell23_1961985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1961985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961985 prefixEnd_1961985 := by exact prefixLift 1961985
  have htrace : WordTrace (prefixWord ++ tailWord_1961985) baseStart_1961985 baseEnd_1961985 := by
    simpa [prefixWord, tailWord_1961985, baseEnd_1961985] using wordTrace_append hprefix tailTrace_1961985
  have hstable : (prefixWord ++ tailWord_1961985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961985).length < 2 ^ (prefixWord ++ tailWord_1961985).sum := by decide
  have hdescent : baseEnd_1961985 < baseStart_1961985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961990 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1961990 : Nat := 118140960795 + 1961990 * 2 ^ 59
def prefixEnd_1961990 : Nat := 4983230072969 + 3 ^ 40 * 1961990 * 2
def baseEnd_1961990 : Nat := 1007443909314883938801979

theorem tailTrace_1961990 : CollatzResearch.WordTrace tailWord_1961990 prefixEnd_1961990 1007443909314883938801979 := by
  unfold tailWord_1961990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236239192564149564372857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47706436108035190706620949 2236239192564149564372857)
  ·
    refine ⟨1677179394423112173279643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2236239192564149564372857 1677179394423112173279643)
    ·
      refine ⟨2515769091634668259919465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677179394423112173279643 2515769091634668259919465)
      ·
        refine ⟨1886826818726001194939599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515769091634668259919465 1886826818726001194939599)
        ·
          refine ⟨2830240228089001792409399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886826818726001194939599 2830240228089001792409399)
          ·
            refine ⟨4245360342133502688614099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830240228089001792409399 4245360342133502688614099)
            ·
              refine ⟨6368040513200254032921149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245360342133502688614099 6368040513200254032921149)
              ·
                refine ⟨2388015192450095262345431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6368040513200254032921149 2388015192450095262345431)
                ·
                  refine ⟨3582022788675142893518147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388015192450095262345431 3582022788675142893518147)
                  ·
                    refine ⟨5373034183012714340277221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3582022788675142893518147 5373034183012714340277221)
                    ·
                      refine ⟨1007443909314883938801979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5373034183012714340277221 1007443909314883938801979)
                      ·
                        rfl

theorem cell23_1961990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1961990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1961990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1961990 prefixEnd_1961990 := by exact prefixLift 1961990
  have htrace : WordTrace (prefixWord ++ tailWord_1961990) baseStart_1961990 baseEnd_1961990 := by
    simpa [prefixWord, tailWord_1961990, baseEnd_1961990] using wordTrace_append hprefix tailTrace_1961990
  have hstable : (prefixWord ++ tailWord_1961990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961990).length < 2 ^ (prefixWord ++ tailWord_1961990).sum := by decide
  have hdescent : baseEnd_1961990 < baseStart_1961990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962023 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1962023 : Nat := 118140960795 + 1962023 * 2 ^ 59
def prefixEnd_1962023 : Nat := 4983230072969 + 3 ^ 40 * 1962023 * 2
def baseEnd_1962023 : Nat := 1007460854176482309689327

theorem tailTrace_1962023 : CollatzResearch.WordTrace tailWord_1962023 prefixEnd_1962023 1007460854176482309689327 := by
  unfold tailWord_1962023
  simp only [CollatzResearch.WordTrace]
  refine ⟨71560857770933232695882723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47707238513955488463921815 71560857770933232695882723)
  ·
    refine ⟨107341286656399849043824085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71560857770933232695882723 107341286656399849043824085)
    ·
      refine ⟨2515811406009371461964627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107341286656399849043824085 2515811406009371461964627)
      ·
        refine ⟨3773717109014057192946941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515811406009371461964627 3773717109014057192946941)
        ·
          refine ⟨1415143915880271447355103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3773717109014057192946941 1415143915880271447355103)
          ·
            refine ⟨2122715873820407171032655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415143915880271447355103 2122715873820407171032655)
            ·
              refine ⟨3184073810730610756548983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122715873820407171032655 3184073810730610756548983)
              ·
                refine ⟨4776110716095916134823475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184073810730610756548983 4776110716095916134823475)
                ·
                  refine ⟨7164166074143874202235213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776110716095916134823475 7164166074143874202235213)
                  ·
                    refine ⟨2686562277803952825838205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7164166074143874202235213 2686562277803952825838205)
                    ·
                      refine ⟨1007460854176482309689327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686562277803952825838205 1007460854176482309689327)
                      ·
                        rfl

theorem cell23_1962023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1962023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962023 prefixEnd_1962023 := by exact prefixLift 1962023
  have htrace : WordTrace (prefixWord ++ tailWord_1962023) baseStart_1962023 baseEnd_1962023 := by
    simpa [prefixWord, tailWord_1962023, baseEnd_1962023] using wordTrace_append hprefix tailTrace_1962023
  have hstable : (prefixWord ++ tailWord_1962023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962023).length < 2 ^ (prefixWord ++ tailWord_1962023).sum := by decide
  have hdescent : baseEnd_1962023 < baseStart_1962023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962035 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 7]
def baseStart_1962035 : Nat := 118140960795 + 1962035 * 2 ^ 59
def prefixEnd_1962035 : Nat := 4983230072969 + 3 ^ 40 * 1962035 * 2
def baseEnd_1962035 : Nat := 111940779549370695859919

theorem tailTrace_1962035 : CollatzResearch.WordTrace tailWord_1962035 prefixEnd_1962035 111940779549370695859919 := by
  unfold tailWord_1962035
  simp only [CollatzResearch.WordTrace]
  refine ⟨71561295446889758745319559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47707530297926505830213039 71561295446889758745319559)
  ·
    refine ⟨107341943170334638117979339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71561295446889758745319559 107341943170334638117979339)
    ·
      refine ⟨161012914755501957176969009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107341943170334638117979339 161012914755501957176969009)
      ·
        refine ⟨120759686066626467882726757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161012914755501957176969009 120759686066626467882726757)
        ·
          refine ⟨22642441137492462728011267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120759686066626467882726757 22642441137492462728011267)
          ·
            refine ⟨33963661706238694092016901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642441137492462728011267 33963661706238694092016901)
            ·
              refine ⟨6368186569919755142253169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33963661706238694092016901 6368186569919755142253169)
              ·
                refine ⟨4776139927439816356689877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368186569919755142253169 4776139927439816356689877)
                ·
                  refine ⟨111940779549370695859919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4776139927439816356689877 111940779549370695859919)
                  ·
                    rfl

theorem cell23_1962035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 7].length) (baseStart_1962035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962035 prefixEnd_1962035 := by exact prefixLift 1962035
  have htrace : WordTrace (prefixWord ++ tailWord_1962035) baseStart_1962035 baseEnd_1962035 := by
    simpa [prefixWord, tailWord_1962035, baseEnd_1962035] using wordTrace_append hprefix tailTrace_1962035
  have hstable : (prefixWord ++ tailWord_1962035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962035).length < 2 ^ (prefixWord ++ tailWord_1962035).sum := by decide
  have hdescent : baseEnd_1962035 < baseStart_1962035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962136 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1962136 : Nat := 118140960795 + 1962136 * 2 ^ 59
def prefixEnd_1962136 : Nat := 4983230072969 + 3 ^ 40 * 1962136 * 2
def baseEnd_1962136 : Nat := 1007518877490440367576307

theorem tailTrace_1962136 : CollatzResearch.WordTrace tailWord_1962136 prefixEnd_1962136 1007518877490440367576307 := by
  unfold tailWord_1962136
  simp only [CollatzResearch.WordTrace]
  refine ⟨35782489609761926497373131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47709986146349235329830841 35782489609761926497373131)
  ·
    refine ⟨53673734414642889746059697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35782489609761926497373131 53673734414642889746059697)
    ·
      refine ⟨40255300810982167309544773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53673734414642889746059697 40255300810982167309544773)
      ·
        refine ⟨7547868902059156370539645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40255300810982167309544773 7547868902059156370539645)
        ·
          refine ⟨2830450838272183638952367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7547868902059156370539645 2830450838272183638952367)
          ·
            refine ⟨4245676257408275458428551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830450838272183638952367 4245676257408275458428551)
            ·
              refine ⟨6368514386112413187642827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245676257408275458428551 6368514386112413187642827)
              ·
                refine ⟨9552771579168619781464241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368514386112413187642827 9552771579168619781464241)
                ·
                  refine ⟨7164578684376464836098181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9552771579168619781464241 7164578684376464836098181)
                  ·
                    refine ⟨1343358503320587156768409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164578684376464836098181 1343358503320587156768409)
                    ·
                      refine ⟨1007518877490440367576307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343358503320587156768409 1007518877490440367576307)
                      ·
                        rfl

theorem cell23_1962136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1962136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962136 prefixEnd_1962136 := by exact prefixLift 1962136
  have htrace : WordTrace (prefixWord ++ tailWord_1962136) baseStart_1962136 baseEnd_1962136 := by
    simpa [prefixWord, tailWord_1962136, baseEnd_1962136] using wordTrace_append hprefix tailTrace_1962136
  have hstable : (prefixWord ++ tailWord_1962136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962136).length < 2 ^ (prefixWord ++ tailWord_1962136).sum := by decide
  have hdescent : baseEnd_1962136 < baseStart_1962136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962146 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1962146 : Nat := 118140960795 + 1962146 * 2 ^ 59
def prefixEnd_1962146 : Nat := 4983230072969 + 3 ^ 40 * 1962146 * 2
def baseEnd_1962146 : Nat := 335841337432328442817087

theorem tailTrace_1962146 : CollatzResearch.WordTrace tailWord_1962146 prefixEnd_1962146 335841337432328442817087 := by
  unfold tailWord_1962146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17891335987371906175652573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47710229299658416468406861 17891335987371906175652573)
  ·
    refine ⟨6709250995264464815869715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17891335987371906175652573 6709250995264464815869715)
    ·
      refine ⟨10063876492896697223804573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6709250995264464815869715 10063876492896697223804573)
      ·
        refine ⟨3773953684836261458926715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10063876492896697223804573 3773953684836261458926715)
        ·
          refine ⟨5660930527254392188390073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773953684836261458926715 5660930527254392188390073)
          ·
            refine ⟨4245697895440794141292555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5660930527254392188390073 4245697895440794141292555)
            ·
              refine ⟨6368546843161191211938833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245697895440794141292555 6368546843161191211938833)
              ·
                refine ⟨4776410132370893408954125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368546843161191211938833 4776410132370893408954125)
                ·
                  refine ⟨1791153799639085028357797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4776410132370893408954125 1791153799639085028357797)
                  ·
                    refine ⟨335841337432328442817087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791153799639085028357797 335841337432328442817087)
                    ·
                      rfl

theorem cell23_1962146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1962146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962146 prefixEnd_1962146 := by exact prefixLift 1962146
  have htrace : WordTrace (prefixWord ++ tailWord_1962146) baseStart_1962146 baseEnd_1962146 := by
    simpa [prefixWord, tailWord_1962146, baseEnd_1962146] using wordTrace_append hprefix tailTrace_1962146
  have hstable : (prefixWord ++ tailWord_1962146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962146).length < 2 ^ (prefixWord ++ tailWord_1962146).sum := by decide
  have hdescent : baseEnd_1962146 < baseStart_1962146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962169 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1962169 : Nat := 118140960795 + 1962169 * 2 ^ 59
def prefixEnd_1962169 : Nat := 4983230072969 + 3 ^ 40 * 1962169 * 2
def baseEnd_1962169 : Nat := 1007535822352038738463655

theorem tailTrace_1962169 : CollatzResearch.WordTrace tailWord_1962169 prefixEnd_1962169 1007535822352038738463655 := by
  unfold tailWord_1962169
  simp only [CollatzResearch.WordTrace]
  refine ⟨71566182828404299630697561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47710788552269533087131707 71566182828404299630697561)
  ·
    refine ⟨53674637121303224723023171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71566182828404299630697561 53674637121303224723023171)
    ·
      refine ⟨80511955681954837084534757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53674637121303224723023171 80511955681954837084534757)
      ·
        refine ⟨15095991690366531953350267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80511955681954837084534757 15095991690366531953350267)
        ·
          refine ⟨22643987535549797930025401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15095991690366531953350267 22643987535549797930025401)
          ·
            refine ⟨16982990651662348447519051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22643987535549797930025401 16982990651662348447519051)
            ·
              refine ⟨25474485977493522671278577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16982990651662348447519051 25474485977493522671278577)
              ·
                refine ⟨19105864483120142003458933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25474485977493522671278577 19105864483120142003458933)
                ·
                  refine ⟨1791174795292513312824275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19105864483120142003458933 1791174795292513312824275)
                  ·
                    refine ⟨2686762192938769969236413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791174795292513312824275 2686762192938769969236413)
                    ·
                      refine ⟨1007535822352038738463655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686762192938769969236413 1007535822352038738463655)
                      ·
                        rfl

theorem cell23_1962169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1962169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962169 prefixEnd_1962169 := by exact prefixLift 1962169
  have htrace : WordTrace (prefixWord ++ tailWord_1962169) baseStart_1962169 baseEnd_1962169 := by
    simpa [prefixWord, tailWord_1962169, baseEnd_1962169] using wordTrace_append hprefix tailTrace_1962169
  have hstable : (prefixWord ++ tailWord_1962169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962169).length < 2 ^ (prefixWord ++ tailWord_1962169).sum := by decide
  have hdescent : baseEnd_1962169 < baseStart_1962169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962186 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_1962186 : Nat := 118140960795 + 1962186 * 2 ^ 59
def prefixEnd_1962186 : Nat := 4983230072969 + 3 ^ 40 * 1962186 * 2
def baseEnd_1962186 : Nat := 1007544551523165171951077

theorem tailTrace_1962186 : CollatzResearch.WordTrace tailWord_1962186 prefixEnd_1962186 1007544551523165171951077 := by
  unfold tailWord_1962186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17891700717335677883516603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47711201912895141022710941 17891700717335677883516603)
  ·
    refine ⟨26837551076003516825274905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17891700717335677883516603 26837551076003516825274905)
    ·
      refine ⟨20128163307002637618956179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26837551076003516825274905 20128163307002637618956179)
      ·
        refine ⟨30192244960503956428434269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20128163307002637618956179 30192244960503956428434269)
        ·
          refine ⟨11322091860188983660662851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30192244960503956428434269 11322091860188983660662851)
          ·
            refine ⟨16983137790283475490994277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322091860188983660662851 16983137790283475490994277)
            ·
              refine ⟨3184338335678151654561427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16983137790283475490994277 3184338335678151654561427)
              ·
                refine ⟨4776507503517227481842141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184338335678151654561427 4776507503517227481842141)
                ·
                  refine ⟨1791190313818960305690803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4776507503517227481842141 1791190313818960305690803)
                  ·
                    refine ⟨2686785470728440458536205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791190313818960305690803 2686785470728440458536205)
                    ·
                      refine ⟨1007544551523165171951077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686785470728440458536205 1007544551523165171951077)
                      ·
                        rfl

theorem cell23_1962186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_1962186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962186 prefixEnd_1962186 := by exact prefixLift 1962186
  have htrace : WordTrace (prefixWord ++ tailWord_1962186) baseStart_1962186 baseEnd_1962186 := by
    simpa [prefixWord, tailWord_1962186, baseEnd_1962186] using wordTrace_append hprefix tailTrace_1962186
  have hstable : (prefixWord ++ tailWord_1962186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962186).length < 2 ^ (prefixWord ++ tailWord_1962186).sum := by decide
  have hdescent : baseEnd_1962186 < baseStart_1962186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962209 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_1962209 : Nat := 118140960795 + 1962209 * 2 ^ 59
def prefixEnd_1962209 : Nat := 4983230072969 + 3 ^ 40 * 1962209 * 2
def baseEnd_1962209 : Nat := 1007556361578218581963471

theorem tailTrace_1962209 : CollatzResearch.WordTrace tailWord_1962209 prefixEnd_1962209 1007556361578218581963471 := by
  unfold tailWord_1962209
  simp only [CollatzResearch.WordTrace]
  refine ⟨71567641748259386462153681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47711761165506257641435787 71567641748259386462153681)
  ·
    refine ⟨53675731311194539846615261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71567641748259386462153681 53675731311194539846615261)
    ·
      refine ⟨20128399241697952442480723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53675731311194539846615261 20128399241697952442480723)
      ·
        refine ⟨30192598862546928663721085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20128399241697952442480723 30192598862546928663721085)
        ·
          refine ⟨11322224573455098248895407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30192598862546928663721085 11322224573455098248895407)
          ·
            refine ⟨16983336860182647373343111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322224573455098248895407 16983336860182647373343111)
            ·
              refine ⟨25475005290273971060014667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16983336860182647373343111 25475005290273971060014667)
              ·
                refine ⟨38212507935410956590022001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25475005290273971060014667 38212507935410956590022001)
                ·
                  refine ⟨28659380951558217442516501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38212507935410956590022001 28659380951558217442516501)
                  ·
                    refine ⟨1343408482104291442617961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28659380951558217442516501 1343408482104291442617961)
                    ·
                      refine ⟨1007556361578218581963471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343408482104291442617961 1007556361578218581963471)
                      ·
                        rfl

theorem cell23_1962209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_1962209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962209 prefixEnd_1962209 := by exact prefixLift 1962209
  have htrace : WordTrace (prefixWord ++ tailWord_1962209) baseStart_1962209 baseEnd_1962209 := by
    simpa [prefixWord, tailWord_1962209, baseEnd_1962209] using wordTrace_append hprefix tailTrace_1962209
  have hstable : (prefixWord ++ tailWord_1962209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962209).length < 2 ^ (prefixWord ++ tailWord_1962209).sum := by decide
  have hdescent : baseEnd_1962209 < baseStart_1962209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962212 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1962212 : Nat := 118140960795 + 1962212 * 2 ^ 59
def prefixEnd_1962212 : Nat := 4983230072969 + 3 ^ 40 * 1962212 * 2
def baseEnd_1962212 : Nat := 1007557902020182070225957

theorem tailTrace_1962212 : CollatzResearch.WordTrace tailWord_1962212 prefixEnd_1962212 1007557902020182070225957 := by
  unfold tailWord_1962212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35783875583624258987256445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47711834111499011983008593 35783875583624258987256445)
  ·
    refine ⟨13418953343859097120221167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35783875583624258987256445 13418953343859097120221167)
    ·
      refine ⟨20128430015788645680331751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13418953343859097120221167 20128430015788645680331751)
      ·
        refine ⟨30192645023682968520497627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20128430015788645680331751 30192645023682968520497627)
        ·
          refine ⟨45288967535524452780746441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30192645023682968520497627 45288967535524452780746441)
          ·
            refine ⟨33966725651643339585559831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45288967535524452780746441 33966725651643339585559831)
            ·
              refine ⟨50950088477465009378339747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33966725651643339585559831 50950088477465009378339747)
              ·
                refine ⟨76425132716197514067509621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50950088477465009378339747 76425132716197514067509621)
                ·
                  refine ⟨7164856192143516943829027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76425132716197514067509621 7164856192143516943829027)
                  ·
                    refine ⟨10747284288215275415743541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164856192143516943829027 10747284288215275415743541)
                    ·
                      refine ⟨1007557902020182070225957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10747284288215275415743541 1007557902020182070225957)
                      ·
                        rfl

theorem cell23_1962212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1962212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962212 prefixEnd_1962212 := by exact prefixLift 1962212
  have htrace : WordTrace (prefixWord ++ tailWord_1962212) baseStart_1962212 baseEnd_1962212 := by
    simpa [prefixWord, tailWord_1962212, baseEnd_1962212] using wordTrace_append hprefix tailTrace_1962212
  have hstable : (prefixWord ++ tailWord_1962212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962212).length < 2 ^ (prefixWord ++ tailWord_1962212).sum := by decide
  have hdescent : baseEnd_1962212 < baseStart_1962212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962226 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1962226 : Nat := 118140960795 + 1962226 * 2 ^ 59
def prefixEnd_1962226 : Nat := 4983230072969 + 3 ^ 40 * 1962226 * 2
def baseEnd_1962226 : Nat := 1007565090749345015450893

theorem tailTrace_1962226 : CollatzResearch.WordTrace tailWord_1962226 prefixEnd_1962226 1007565090749345015450893 := by
  unfold tailWord_1962226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17892065447299449591380633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47712174526131865577015021 17892065447299449591380633)
  ·
    refine ⟨13419049085474587193535475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17892065447299449591380633 13419049085474587193535475)
    ·
      refine ⟨20128573628211880790303213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13419049085474587193535475 20128573628211880790303213)
      ·
        refine ⟨7548215110579455296363705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20128573628211880790303213 7548215110579455296363705)
        ·
          refine ⟨5661161332934591472272779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7548215110579455296363705 5661161332934591472272779)
          ·
            refine ⟨8491741999401887208409169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661161332934591472272779 8491741999401887208409169)
            ·
              refine ⟨6368806499551415406306877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8491741999401887208409169 6368806499551415406306877)
              ·
                refine ⟨2388302437331780777365079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6368806499551415406306877 2388302437331780777365079)
                ·
                  refine ⟨3582453655997671166047619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388302437331780777365079 3582453655997671166047619)
                  ·
                    refine ⟨5373680483996506749071429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3582453655997671166047619 5373680483996506749071429)
                    ·
                      refine ⟨1007565090749345015450893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5373680483996506749071429 1007565090749345015450893)
                      ·
                        rfl

theorem cell23_1962226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1962226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962226 prefixEnd_1962226 := by exact prefixLift 1962226
  have htrace : WordTrace (prefixWord ++ tailWord_1962226) baseStart_1962226 baseEnd_1962226 := by
    simpa [prefixWord, tailWord_1962226, baseEnd_1962226] using wordTrace_append hprefix tailTrace_1962226
  have hstable : (prefixWord ++ tailWord_1962226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962226).length < 2 ^ (prefixWord ++ tailWord_1962226).sum := by decide
  have hdescent : baseEnd_1962226 < baseStart_1962226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962252 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1962252 : Nat := 118140960795 + 1962252 * 2 ^ 59
def prefixEnd_1962252 : Nat := 4983230072969 + 3 ^ 40 * 1962252 * 2
def baseEnd_1962252 : Nat := 1007578441246361913725773

theorem tailTrace_1962252 : CollatzResearch.WordTrace tailWord_1962252 prefixEnd_1962252 1007578441246361913725773 := by
  unfold tailWord_1962252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35784605043551802402984505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47712806724735736537312673 35784605043551802402984505)
  ·
    refine ⟨26838453782663851802238379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35784605043551802402984505 26838453782663851802238379)
    ·
      refine ⟨40257680673995777703357569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26838453782663851802238379 40257680673995777703357569)
      ·
        refine ⟨30193260505496833277518177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40257680673995777703357569 30193260505496833277518177)
        ·
          refine ⟨22644945379122624958138633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30193260505496833277518177 22644945379122624958138633)
          ·
            refine ⟨16983709034341968718603975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22644945379122624958138633 16983709034341968718603975)
            ·
              refine ⟨25475563551512953077905963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16983709034341968718603975 25475563551512953077905963)
              ·
                refine ⟨38213345327269429616858945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25475563551512953077905963 38213345327269429616858945)
                ·
                  refine ⟨28660008995452072212644209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38213345327269429616858945 28660008995452072212644209)
                  ·
                    refine ⟨21495006746589054159483157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28660008995452072212644209 21495006746589054159483157)
                    ·
                      refine ⟨1007578441246361913725773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21495006746589054159483157 1007578441246361913725773)
                      ·
                        rfl

theorem cell23_1962252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1962252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962252 prefixEnd_1962252 := by exact prefixLift 1962252
  have htrace : WordTrace (prefixWord ++ tailWord_1962252) baseStart_1962252 baseEnd_1962252 := by
    simpa [prefixWord, tailWord_1962252, baseEnd_1962252] using wordTrace_append hprefix tailTrace_1962252
  have hstable : (prefixWord ++ tailWord_1962252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962252).length < 2 ^ (prefixWord ++ tailWord_1962252).sum := by decide
  have hdescent : baseEnd_1962252 < baseStart_1962252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962263 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1962263 : Nat := 118140960795 + 1962263 * 2 ^ 59
def prefixEnd_1962263 : Nat := 4983230072969 + 3 ^ 40 * 1962263 * 2
def baseEnd_1962263 : Nat := 1007584089533561370688223

theorem tailTrace_1962263 : CollatzResearch.WordTrace tailWord_1962263 prefixEnd_1962263 1007584089533561370688223 := by
  unfold tailWord_1962263
  simp only [CollatzResearch.WordTrace]
  refine ⟨71569611290063753684619443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47713074193375835789746295 71569611290063753684619443)
  ·
    refine ⟨107354416935095630526929165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71569611290063753684619443 107354416935095630526929165)
    ·
      refine ⟨40257906350660861447598437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107354416935095630526929165 40257906350660861447598437)
      ·
        refine ⟨7548357440748911521424707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40257906350660861447598437 7548357440748911521424707)
        ·
          refine ⟨11322536161123367282137061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548357440748911521424707 11322536161123367282137061)
          ·
            refine ⟨2122975530210631365400699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11322536161123367282137061 2122975530210631365400699)
            ·
              refine ⟨3184463295315947048101049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122975530210631365400699 3184463295315947048101049)
              ·
                refine ⟨2388347471486960286075787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184463295315947048101049 2388347471486960286075787)
                ·
                  refine ⟨3582521207230440429113681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388347471486960286075787 3582521207230440429113681)
                  ·
                    refine ⟨2686890905422830321835261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582521207230440429113681 2686890905422830321835261)
                    ·
                      refine ⟨1007584089533561370688223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686890905422830321835261 1007584089533561370688223)
                      ·
                        rfl

theorem cell23_1962263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1962263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962263 prefixEnd_1962263 := by exact prefixLift 1962263
  have htrace : WordTrace (prefixWord ++ tailWord_1962263) baseStart_1962263 baseEnd_1962263 := by
    simpa [prefixWord, tailWord_1962263, baseEnd_1962263] using wordTrace_append hprefix tailTrace_1962263
  have hstable : (prefixWord ++ tailWord_1962263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962263).length < 2 ^ (prefixWord ++ tailWord_1962263).sum := by decide
  have hdescent : baseEnd_1962263 < baseStart_1962263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962276 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1962276 : Nat := 118140960795 + 1962276 * 2 ^ 59
def prefixEnd_1962276 : Nat := 4983230072969 + 3 ^ 40 * 1962276 * 2
def baseEnd_1962276 : Nat := 1007590764782069819825663

theorem tailTrace_1962276 : CollatzResearch.WordTrace tailWord_1962276 prefixEnd_1962276 1007590764782069819825663 := by
  unfold tailWord_1962276
  simp only [CollatzResearch.WordTrace]
  refine ⟨35785042719508328452421341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47713390292677771269895121 35785042719508328452421341)
  ·
    refine ⟨13419391019815623169658003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35785042719508328452421341 13419391019815623169658003)
    ·
      refine ⟨20129086529723434754487005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13419391019815623169658003 20129086529723434754487005)
      ·
        refine ⟨7548407448646288032932627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20129086529723434754487005 7548407448646288032932627)
        ·
          refine ⟨11322611172969432049398941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548407448646288032932627 11322611172969432049398941)
          ·
            refine ⟨4245979189863537018524603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11322611172969432049398941 4245979189863537018524603)
            ·
              refine ⟨6368968784795305527786905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245979189863537018524603 6368968784795305527786905)
              ·
                refine ⟨4776726588596479145840179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368968784795305527786905 4776726588596479145840179)
                ·
                  refine ⟨7165089882894718718760269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776726588596479145840179 7165089882894718718760269)
                  ·
                    refine ⟨2686908706085519519535101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7165089882894718718760269 2686908706085519519535101)
                    ·
                      refine ⟨1007590764782069819825663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686908706085519519535101 1007590764782069819825663)
                      ·
                        rfl

theorem cell23_1962276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1962276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962276 prefixEnd_1962276 := by exact prefixLift 1962276
  have htrace : WordTrace (prefixWord ++ tailWord_1962276) baseStart_1962276 baseEnd_1962276 := by
    simpa [prefixWord, tailWord_1962276, baseEnd_1962276] using wordTrace_append hprefix tailTrace_1962276
  have hstable : (prefixWord ++ tailWord_1962276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962276).length < 2 ^ (prefixWord ++ tailWord_1962276).sum := by decide
  have hdescent : baseEnd_1962276 < baseStart_1962276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962280 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1962280 : Nat := 118140960795 + 1962280 * 2 ^ 59
def prefixEnd_1962280 : Nat := 4983230072969 + 3 ^ 40 * 1962280 * 2
def baseEnd_1962280 : Nat := 1007592818704687804175645

theorem tailTrace_1962280 : CollatzResearch.WordTrace tailWord_1962280 prefixEnd_1962280 1007592818704687804175645 := by
  unfold tailWord_1962280
  simp only [CollatzResearch.WordTrace]
  refine ⟨35785115665501082793994147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47713487554001443725325529 35785115665501082793994147)
  ·
    refine ⟨53677673498251624190991221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35785115665501082793994147 53677673498251624190991221)
    ·
      refine ⟨5032281890461089767905427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53677673498251624190991221 5032281890461089767905427)
      ·
        refine ⟨7548422835691634651858141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032281890461089767905427 7548422835691634651858141)
        ·
          refine ⟨2830658563384362994446803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7548422835691634651858141 2830658563384362994446803)
          ·
            refine ⟨4245987845076544491670205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830658563384362994446803 4245987845076544491670205)
            ·
              refine ⟨1592245441903704184376327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4245987845076544491670205 1592245441903704184376327)
              ·
                refine ⟨2388368162855556276564491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592245441903704184376327 2388368162855556276564491)
                ·
                  refine ⟨3582552244283334414846737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388368162855556276564491 3582552244283334414846737)
                  ·
                    refine ⟨2686914183212500811135053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582552244283334414846737 2686914183212500811135053)
                    ·
                      refine ⟨1007592818704687804175645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686914183212500811135053 1007592818704687804175645)
                      ·
                        rfl

theorem cell23_1962280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1962280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962280 prefixEnd_1962280 := by exact prefixLift 1962280
  have htrace : WordTrace (prefixWord ++ tailWord_1962280) baseStart_1962280 baseEnd_1962280 := by
    simpa [prefixWord, tailWord_1962280, baseEnd_1962280] using wordTrace_append hprefix tailTrace_1962280
  have hstable : (prefixWord ++ tailWord_1962280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962280).length < 2 ^ (prefixWord ++ tailWord_1962280).sum := by decide
  have hdescent : baseEnd_1962280 < baseStart_1962280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962293 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1962293 : Nat := 118140960795 + 1962293 * 2 ^ 59
def prefixEnd_1962293 : Nat := 4983230072969 + 3 ^ 40 * 1962293 * 2
def baseEnd_1962293 : Nat := 1007599493953196253313085

theorem tailTrace_1962293 : CollatzResearch.WordTrace tailWord_1962293 prefixEnd_1962293 1007599493953196253313085 := by
  unfold tailWord_1962293
  simp only [CollatzResearch.WordTrace]
  refine ⟨71570705479955068808211533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47713803653303379205474355 71570705479955068808211533)
  ·
    refine ⟨26839014554983150803079325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71570705479955068808211533 26839014554983150803079325)
    ·
      refine ⟨10064630458118681551154747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26839014554983150803079325 10064630458118681551154747)
      ·
        refine ⟨15096945687178022326732121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10064630458118681551154747 15096945687178022326732121)
        ·
          refine ⟨11322709265383516745049091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15096945687178022326732121 11322709265383516745049091)
          ·
            refine ⟨16984063898075275117573637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322709265383516745049091 16984063898075275117573637)
            ·
              refine ⟨3184511980889114084545057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16984063898075275117573637 3184511980889114084545057)
              ·
                refine ⟨2388383985666835563408793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184511980889114084545057 2388383985666835563408793)
                ·
                  refine ⟨1791287989250126672556595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2388383985666835563408793 1791287989250126672556595)
                  ·
                    refine ⟨2686931983875190008834893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791287989250126672556595 2686931983875190008834893)
                    ·
                      refine ⟨1007599493953196253313085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2686931983875190008834893 1007599493953196253313085)
                      ·
                        rfl

theorem cell23_1962293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1962293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962293 prefixEnd_1962293 := by exact prefixLift 1962293
  have htrace : WordTrace (prefixWord ++ tailWord_1962293) baseStart_1962293 baseEnd_1962293 := by
    simpa [prefixWord, tailWord_1962293, baseEnd_1962293] using wordTrace_append hprefix tailTrace_1962293
  have hstable : (prefixWord ++ tailWord_1962293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962293).length < 2 ^ (prefixWord ++ tailWord_1962293).sum := by decide
  have hdescent : baseEnd_1962293 < baseStart_1962293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962346 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1962346 : Nat := 118140960795 + 1962346 * 2 ^ 59
def prefixEnd_1962346 : Nat := 4983230072969 + 3 ^ 40 * 1962346 * 2
def baseEnd_1962346 : Nat := 1007626708427884545950341

theorem tailTrace_1962346 : CollatzResearch.WordTrace tailWord_1962346 prefixEnd_1962346 1007626708427884545950341 := by
  unfold tailWord_1962346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17893159637190764714972723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47715092365842039239927261 17893159637190764714972723)
  ·
    refine ⟨26839739455786147072459085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17893159637190764714972723 26839739455786147072459085)
    ·
      refine ⟨10064902295919805152172157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26839739455786147072459085 10064902295919805152172157)
      ·
        refine ⟨3774338360969926932064559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10064902295919805152172157 3774338360969926932064559)
        ·
          refine ⟨5661507541454890398096839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774338360969926932064559 5661507541454890398096839)
          ·
            refine ⟨8492261312182335597145259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661507541454890398096839 8492261312182335597145259)
            ·
              refine ⟨12738391968273503395717889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492261312182335597145259 12738391968273503395717889)
              ·
                refine ⟨9553793976205127546788417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12738391968273503395717889 9553793976205127546788417)
                ·
                  refine ⟨7165345482153845660091313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9553793976205127546788417 7165345482153845660091313)
                  ·
                    refine ⟨5374009111615384245068485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7165345482153845660091313 5374009111615384245068485)
                    ·
                      refine ⟨1007626708427884545950341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5374009111615384245068485 1007626708427884545950341)
                      ·
                        rfl

theorem cell23_1962346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1962346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962346 prefixEnd_1962346 := by exact prefixLift 1962346
  have htrace : WordTrace (prefixWord ++ tailWord_1962346) baseStart_1962346 baseEnd_1962346 := by
    simpa [prefixWord, tailWord_1962346, baseEnd_1962346] using wordTrace_append hprefix tailTrace_1962346
  have hstable : (prefixWord ++ tailWord_1962346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962346).length < 2 ^ (prefixWord ++ tailWord_1962346).sum := by decide
  have hdescent : baseEnd_1962346 < baseStart_1962346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962413 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1962413 : Nat := 118140960795 + 1962413 * 2 ^ 59
def prefixEnd_1962413 : Nat := 4983230072969 + 3 ^ 40 * 1962413 * 2
def baseEnd_1962413 : Nat := 1007661111631735783812533

theorem tailTrace_1962413 : CollatzResearch.WordTrace tailWord_1962413 prefixEnd_1962413 1007661111631735783812533 := by
  unfold tailWord_1962413
  simp only [CollatzResearch.WordTrace]
  refine ⟨71575082239520329302579893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47716721493013552868386595 71575082239520329302579893)
  ·
    refine ⟨6710163959955030872116865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71575082239520329302579893 6710163959955030872116865)
    ·
      refine ⟨5032622969966273154087649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6710163959955030872116865 5032622969966273154087649)
      ·
        refine ⟨3774467227474704865565737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5032622969966273154087649 3774467227474704865565737)
        ·
          refine ⟨2830850420606028649174303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774467227474704865565737 2830850420606028649174303)
          ·
            refine ⟨4246275630909042973761455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830850420606028649174303 4246275630909042973761455)
            ·
              refine ⟨6369413446363564460642183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246275630909042973761455 6369413446363564460642183)
              ·
                refine ⟨9554120169545346690963275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369413446363564460642183 9554120169545346690963275)
                ·
                  refine ⟨14331180254318020036444913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9554120169545346690963275 14331180254318020036444913)
                  ·
                    refine ⟨10748385190738515027333685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14331180254318020036444913 10748385190738515027333685)
                    ·
                      refine ⟨1007661111631735783812533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10748385190738515027333685 1007661111631735783812533)
                      ·
                        rfl

theorem cell23_1962413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1962413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962413 prefixEnd_1962413 := by exact prefixLift 1962413
  have htrace : WordTrace (prefixWord ++ tailWord_1962413) baseStart_1962413 baseEnd_1962413 := by
    simpa [prefixWord, tailWord_1962413, baseEnd_1962413] using wordTrace_append hprefix tailTrace_1962413
  have hstable : (prefixWord ++ tailWord_1962413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962413).length < 2 ^ (prefixWord ++ tailWord_1962413).sum := by decide
  have hdescent : baseEnd_1962413 < baseStart_1962413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962486 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1962486 : Nat := 118140960795 + 1962486 * 2 ^ 59
def prefixEnd_1962486 : Nat := 4983230072969 + 3 ^ 40 * 1962486 * 2
def baseEnd_1962486 : Nat := 1007698595719513998199697

theorem tailTrace_1962486 : CollatzResearch.WordTrace tailWord_1962486 prefixEnd_1962486 1007698595719513998199697 := by
  unfold tailWord_1962486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473609048015991423124207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47718496512170575179991541 4473609048015991423124207)
  ·
    refine ⟨6710413572023987134686311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4473609048015991423124207 6710413572023987134686311)
    ·
      refine ⟨10065620358035980702029467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710413572023987134686311 10065620358035980702029467)
      ·
        refine ⟨15098430537053971053044201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065620358035980702029467 15098430537053971053044201)
        ·
          refine ⟨11323822902790478289783151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15098430537053971053044201 11323822902790478289783151)
          ·
            refine ⟨16985734354185717434674727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323822902790478289783151 16985734354185717434674727)
            ·
              refine ⟨25478601531278576152012091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16985734354185717434674727 25478601531278576152012091)
              ·
                refine ⟨38217902296917864228018137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25478601531278576152012091 38217902296917864228018137)
                ·
                  refine ⟨28663426722688398171013603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38217902296917864228018137 28663426722688398171013603)
                  ·
                    refine ⟨42995140084032597256520405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28663426722688398171013603 42995140084032597256520405)
                    ·
                      refine ⟨1007698595719513998199697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42995140084032597256520405 1007698595719513998199697)
                      ·
                        rfl

theorem cell23_1962486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1962486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962486 prefixEnd_1962486 := by exact prefixLift 1962486
  have htrace : WordTrace (prefixWord ++ tailWord_1962486) baseStart_1962486 baseEnd_1962486 := by
    simpa [prefixWord, tailWord_1962486, baseEnd_1962486] using wordTrace_append hprefix tailTrace_1962486
  have hstable : (prefixWord ++ tailWord_1962486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962486).length < 2 ^ (prefixWord ++ tailWord_1962486).sum := by decide
  have hdescent : baseEnd_1962486 < baseStart_1962486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962500 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1962500 : Nat := 118140960795 + 1962500 * 2 ^ 59
def prefixEnd_1962500 : Nat := 4983230072969 + 3 ^ 40 * 1962500 * 2
def baseEnd_1962500 : Nat := 1007705784448676943424633

theorem tailTrace_1962500 : CollatzResearch.WordTrace tailWord_1962500 prefixEnd_1962500 1007705784448676943424633 := by
  unfold tailWord_1962500
  simp only [CollatzResearch.WordTrace]
  refine ⟨35789127695102571580498477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47718836926803428773997969 35789127695102571580498477)
  ·
    refine ⟨13420922885663464342686929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35789127695102571580498477 13420922885663464342686929)
    ·
      refine ⟨10065692164247598257015197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13420922885663464342686929 10065692164247598257015197)
      ·
        refine ⟨3774634561592849346380699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10065692164247598257015197 3774634561592849346380699)
        ·
          refine ⟨5661951842389274019571049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774634561592849346380699 5661951842389274019571049)
          ·
            refine ⟨4246463881791955514678287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661951842389274019571049 4246463881791955514678287)
            ·
              refine ⟨6369695822687933272017431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246463881791955514678287 6369695822687933272017431)
              ·
                refine ⟨9554543734031899908026147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369695822687933272017431 9554543734031899908026147)
                ·
                  refine ⟨14331815601047849862039221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9554543734031899908026147 14331815601047849862039221)
                  ·
                    refine ⟨1343607712598235924566177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14331815601047849862039221 1343607712598235924566177)
                    ·
                      refine ⟨1007705784448676943424633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343607712598235924566177 1007705784448676943424633)
                      ·
                        rfl

theorem cell23_1962500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1962500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962500 prefixEnd_1962500 := by exact prefixLift 1962500
  have htrace : WordTrace (prefixWord ++ tailWord_1962500) baseStart_1962500 baseEnd_1962500 := by
    simpa [prefixWord, tailWord_1962500, baseEnd_1962500] using wordTrace_append hprefix tailTrace_1962500
  have hstable : (prefixWord ++ tailWord_1962500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962500).length < 2 ^ (prefixWord ++ tailWord_1962500).sum := by decide
  have hdescent : baseEnd_1962500 < baseStart_1962500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962506 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1962506 : Nat := 118140960795 + 1962506 * 2 ^ 59
def prefixEnd_1962506 : Nat := 4983230072969 + 3 ^ 40 * 1962506 * 2
def baseEnd_1962506 : Nat := 335902955110867973316535

theorem tailTrace_1962506 : CollatzResearch.WordTrace tailWord_1962506 prefixEnd_1962506 335902955110867973316535 := by
  unfold tailWord_1962506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894618557045851546428843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47718982818788937457143581 17894618557045851546428843)
  ·
    refine ⟨26841927835568777319643265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894618557045851546428843 26841927835568777319643265)
    ·
      refine ⟨20131445876676582989732449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26841927835568777319643265 20131445876676582989732449)
      ·
        refine ⟨15098584407507437242299337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20131445876676582989732449 15098584407507437242299337)
        ·
          refine ⟨11323938305630577931724503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15098584407507437242299337 11323938305630577931724503)
          ·
            refine ⟨16985907458445866897586755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323938305630577931724503 16985907458445866897586755)
            ·
              refine ⟨25478861187668800346380133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16985907458445866897586755 25478861187668800346380133)
              ·
                refine ⟨4777286472687900064946275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25478861187668800346380133 4777286472687900064946275)
                ·
                  refine ⟨7165929709031850097419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777286472687900064946275 7165929709031850097419413)
                  ·
                    refine ⟨335902955110867973316535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7165929709031850097419413 335902955110867973316535)
                    ·
                      rfl

theorem cell23_1962506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1962506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962506 prefixEnd_1962506 := by exact prefixLift 1962506
  have htrace : WordTrace (prefixWord ++ tailWord_1962506) baseStart_1962506 baseEnd_1962506 := by
    simpa [prefixWord, tailWord_1962506, baseEnd_1962506] using wordTrace_append hprefix tailTrace_1962506
  have hstable : (prefixWord ++ tailWord_1962506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962506).length < 2 ^ (prefixWord ++ tailWord_1962506).sum := by decide
  have hdescent : baseEnd_1962506 < baseStart_1962506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962507 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 1, 1, 3]
def baseStart_1962507 : Nat := 118140960795 + 1962507 * 2 ^ 59
def prefixEnd_1962507 : Nat := 4983230072969 + 3 ^ 40 * 1962507 * 2
def baseEnd_1962507 : Nat := 1007709378813258416037101

theorem tailTrace_1962507 : CollatzResearch.WordTrace tailWord_1962507 prefixEnd_1962507 1007709378813258416037101 := by
  unfold tailWord_1962507
  simp only [CollatzResearch.WordTrace]
  refine ⟨71578510701179783356501775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47719007134119855571001183 71578510701179783356501775)
  ·
    refine ⟨107367766051769675034752663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71578510701179783356501775 107367766051769675034752663)
    ·
      refine ⟨161051649077654512552128995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107367766051769675034752663 161051649077654512552128995)
      ·
        refine ⟨241577473616481768828193493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161051649077654512552128995 241577473616481768828193493)
        ·
          refine ⟨5661972037886291456910785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 241577473616481768828193493 5661972037886291456910785)
          ·
            refine ⟨4246479028414718592683089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661972037886291456910785 4246479028414718592683089)
            ·
              refine ⟨3184859271311038944512317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246479028414718592683089 3184859271311038944512317)
              ·
                refine ⟨1194322226741639604192119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3184859271311038944512317 1194322226741639604192119)
                ·
                  refine ⟨1791483340112459406288179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194322226741639604192119 1791483340112459406288179)
                  ·
                    refine ⟨2687225010168689109432269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791483340112459406288179 2687225010168689109432269)
                    ·
                      refine ⟨1007709378813258416037101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687225010168689109432269 1007709378813258416037101)
                      ·
                        rfl

theorem cell23_1962507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 1, 3].length) (baseStart_1962507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962507 prefixEnd_1962507 := by exact prefixLift 1962507
  have htrace : WordTrace (prefixWord ++ tailWord_1962507) baseStart_1962507 baseEnd_1962507 := by
    simpa [prefixWord, tailWord_1962507, baseEnd_1962507] using wordTrace_append hprefix tailTrace_1962507
  have hstable : (prefixWord ++ tailWord_1962507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962507).length < 2 ^ (prefixWord ++ tailWord_1962507).sum := by decide
  have hdescent : baseEnd_1962507 < baseStart_1962507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962510 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_1962510 : Nat := 118140960795 + 1962510 * 2 ^ 59
def prefixEnd_1962510 : Nat := 4983230072969 + 3 ^ 40 * 1962510 * 2
def baseEnd_1962510 : Nat := 335903639751740634766529

theorem tailTrace_1962510 : CollatzResearch.WordTrace tailWord_1962510 prefixEnd_1962510 335903639751740634766529 := by
  unfold tailWord_1962510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947327515021114358607623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47719080080112609912573989 8947327515021114358607623)
  ·
    refine ⟨13420991272531671537911435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8947327515021114358607623 13420991272531671537911435)
    ·
      refine ⟨20131486908797507306867153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13420991272531671537911435 20131486908797507306867153)
      ·
        refine ⟨15098615181598130480150365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20131486908797507306867153 15098615181598130480150365)
        ·
          refine ⟨5661980693099298930056387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15098615181598130480150365 5661980693099298930056387)
          ·
            refine ⟨8492971039648948395084581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661980693099298930056387 8492971039648948395084581)
            ·
              refine ⟨1592432069934177824078359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8492971039648948395084581 1592432069934177824078359)
              ·
                refine ⟨2388648104901266736117539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592432069934177824078359 2388648104901266736117539)
                ·
                  refine ⟨3582972157351900104176309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388648104901266736117539 3582972157351900104176309)
                  ·
                    refine ⟨335903639751740634766529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3582972157351900104176309 335903639751740634766529)
                    ·
                      rfl

theorem cell23_1962510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_1962510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962510 prefixEnd_1962510 := by exact prefixLift 1962510
  have htrace : WordTrace (prefixWord ++ tailWord_1962510) baseStart_1962510 baseEnd_1962510 := by
    simpa [prefixWord, tailWord_1962510, baseEnd_1962510] using wordTrace_append hprefix tailTrace_1962510
  have hstable : (prefixWord ++ tailWord_1962510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962510).length < 2 ^ (prefixWord ++ tailWord_1962510).sum := by decide
  have hdescent : baseEnd_1962510 < baseStart_1962510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962558 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1962558 : Nat := 118140960795 + 1962558 * 2 ^ 59
def prefixEnd_1962558 : Nat := 4983230072969 + 3 ^ 40 * 1962558 * 2
def baseEnd_1962558 : Nat := 1007735566326637716499367

theorem tailTrace_1962558 : CollatzResearch.WordTrace tailWord_1962558 prefixEnd_1962558 1007735566326637716499367 := by
  unfold tailWord_1962558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947546352999377383326041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47720247215996679377738885 8947546352999377383326041)
  ·
    refine ⟨6710659764749533037494531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8947546352999377383326041 6710659764749533037494531)
    ·
      refine ⟨10065989647124299556241797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710659764749533037494531 10065989647124299556241797)
      ·
        refine ⟨1887373058835806166795337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10065989647124299556241797 1887373058835806166795337)
        ·
          refine ⟨1415529794126854625096503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887373058835806166795337 1415529794126854625096503)
          ·
            refine ⟨2123294691190281937644755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415529794126854625096503 2123294691190281937644755)
            ·
              refine ⟨3184942036785422906467133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123294691190281937644755 3184942036785422906467133)
              ·
                refine ⟨1194353263794533589925175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3184942036785422906467133 1194353263794533589925175)
                ·
                  refine ⟨1791529895691800384887763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194353263794533589925175 1791529895691800384887763)
                  ·
                    refine ⟨2687294843537700577331645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791529895691800384887763 2687294843537700577331645)
                    ·
                      refine ⟨1007735566326637716499367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687294843537700577331645 1007735566326637716499367)
                      ·
                        rfl

theorem cell23_1962558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1962558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962558 prefixEnd_1962558 := by exact prefixLift 1962558
  have htrace : WordTrace (prefixWord ++ tailWord_1962558) baseStart_1962558 baseEnd_1962558 := by
    simpa [prefixWord, tailWord_1962558, baseEnd_1962558] using wordTrace_append hprefix tailTrace_1962558
  have hstable : (prefixWord ++ tailWord_1962558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962558).length < 2 ^ (prefixWord ++ tailWord_1962558).sum := by decide
  have hdescent : baseEnd_1962558 < baseStart_1962558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962580 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1962580 : Nat := 118140960795 + 1962580 * 2 ^ 59
def prefixEnd_1962580 : Nat := 4983230072969 + 3 ^ 40 * 1962580 * 2
def baseEnd_1962580 : Nat := 1007746862901036630424265

theorem tailTrace_1962580 : CollatzResearch.WordTrace tailWord_1962580 prefixEnd_1962580 1007746862901036630424265 := by
  unfold tailWord_1962580
  simp only [CollatzResearch.WordTrace]
  refine ⟨35790586614957658411954597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47720782153276877882606129 35790586614957658411954597)
  ·
    refine ⟨6710734990304560952241487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35790586614957658411954597 6710734990304560952241487)
    ·
      refine ⟨10066102485456841428362231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710734990304560952241487 10066102485456841428362231)
      ·
        refine ⟨15099153728185262142543347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066102485456841428362231 15099153728185262142543347)
        ·
          refine ⟨22648730592277893213815021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15099153728185262142543347 22648730592277893213815021)
          ·
            refine ⟨8493273972104209955180633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22648730592277893213815021 8493273972104209955180633)
            ·
              refine ⟨6369955479078157466385475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8493273972104209955180633 6369955479078157466385475)
              ·
                refine ⟨9554933218617236199578213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369955479078157466385475 9554933218617236199578213)
                ·
                  refine ⟨1791549978490731787420915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9554933218617236199578213 1791549978490731787420915)
                  ·
                    refine ⟨2687324967736097681131373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791549978490731787420915 2687324967736097681131373)
                    ·
                      refine ⟨1007746862901036630424265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687324967736097681131373 1007746862901036630424265)
                      ·
                        rfl

theorem cell23_1962580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1962580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962580 prefixEnd_1962580 := by exact prefixLift 1962580
  have htrace : WordTrace (prefixWord ++ tailWord_1962580) baseStart_1962580 baseEnd_1962580 := by
    simpa [prefixWord, tailWord_1962580, baseEnd_1962580] using wordTrace_append hprefix tailTrace_1962580
  have hstable : (prefixWord ++ tailWord_1962580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962580).length < 2 ^ (prefixWord ++ tailWord_1962580).sum := by decide
  have hdescent : baseEnd_1962580 < baseStart_1962580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962596 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1962596 : Nat := 118140960795 + 1962596 * 2 ^ 59
def prefixEnd_1962596 : Nat := 4983230072969 + 3 ^ 40 * 1962596 * 2
def baseEnd_1962596 : Nat := 335918359530502855941397

theorem tailTrace_1962596 : CollatzResearch.WordTrace tailWord_1962596 prefixEnd_1962596 335918359530502855941397 := by
  unfold tailWord_1962596
  simp only [CollatzResearch.WordTrace]
  refine ⟨35790878398928675778245821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47721171198571567704327761 35790878398928675778245821)
  ·
    refine ⟨13421579399598253416842183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35790878398928675778245821 13421579399598253416842183)
    ·
      refine ⟨20132369099397380125263275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13421579399598253416842183 20132369099397380125263275)
      ·
        refine ⟨30198553649096070187894913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20132369099397380125263275 30198553649096070187894913)
        ·
          refine ⟨22648915236822052640921185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30198553649096070187894913 22648915236822052640921185)
          ·
            refine ⟨16986686427616539480690889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22648915236822052640921185 16986686427616539480690889)
            ·
              refine ⟨12740014820712404610518167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16986686427616539480690889 12740014820712404610518167)
              ·
                refine ⟨19110022231068606915777251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12740014820712404610518167 19110022231068606915777251)
                ·
                  refine ⟨28665033346602910373665877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19110022231068606915777251 28665033346602910373665877)
                  ·
                    refine ⟨335918359530502855941397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28665033346602910373665877 335918359530502855941397)
                    ·
                      rfl

theorem cell23_1962596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1962596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962596 prefixEnd_1962596 := by exact prefixLift 1962596
  have htrace : WordTrace (prefixWord ++ tailWord_1962596) baseStart_1962596 baseEnd_1962596 := by
    simpa [prefixWord, tailWord_1962596, baseEnd_1962596] using wordTrace_append hprefix tailTrace_1962596
  have hstable : (prefixWord ++ tailWord_1962596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962596).length < 2 ^ (prefixWord ++ tailWord_1962596).sum := by decide
  have hdescent : baseEnd_1962596 < baseStart_1962596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962597 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_1962597 : Nat := 118140960795 + 1962597 * 2 ^ 59
def prefixEnd_1962597 : Nat := 4983230072969 + 3 ^ 40 * 1962597 * 2
def baseEnd_1962597 : Nat := 1007755592072163063911687

theorem tailTrace_1962597 : CollatzResearch.WordTrace tailWord_1962597 prefixEnd_1962597 1007755592072163063911687 := by
  unfold tailWord_1962597
  simp only [CollatzResearch.WordTrace]
  refine ⟨71581793270853728727278045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47721195513902485818185363 71581793270853728727278045)
  ·
    refine ⟨26843172476570148272729267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71581793270853728727278045 26843172476570148272729267)
    ·
      refine ⟨40264758714855222409093901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26843172476570148272729267 40264758714855222409093901)
      ·
        refine ⟨15099284518070708403410213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40264758714855222409093901 15099284518070708403410213)
        ·
          refine ⟨2831115847138257825639415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15099284518070708403410213 2831115847138257825639415)
          ·
            refine ⟨4246673770707386738459123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831115847138257825639415 4246673770707386738459123)
            ·
              refine ⟨6370010656061080107688685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246673770707386738459123 6370010656061080107688685)
              ·
                refine ⟨2388753996022905040383257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370010656061080107688685 2388753996022905040383257)
                ·
                  refine ⟨1791565497017178780287443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2388753996022905040383257 1791565497017178780287443)
                  ·
                    refine ⟨2687348245525768170431165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791565497017178780287443 2687348245525768170431165)
                    ·
                      refine ⟨1007755592072163063911687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687348245525768170431165 1007755592072163063911687)
                      ·
                        rfl

theorem cell23_1962597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_1962597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962597 prefixEnd_1962597 := by exact prefixLift 1962597
  have htrace : WordTrace (prefixWord ++ tailWord_1962597) baseStart_1962597 baseEnd_1962597 := by
    simpa [prefixWord, tailWord_1962597, baseEnd_1962597] using wordTrace_append hprefix tailTrace_1962597
  have hstable : (prefixWord ++ tailWord_1962597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962597).length < 2 ^ (prefixWord ++ tailWord_1962597).sum := by decide
  have hdescent : baseEnd_1962597 < baseStart_1962597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962616 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1962616 : Nat := 118140960795 + 1962616 * 2 ^ 59
def prefixEnd_1962616 : Nat := 4983230072969 + 3 ^ 40 * 1962616 * 2
def baseEnd_1962616 : Nat := 1007765348204598489574099

theorem tailTrace_1962616 : CollatzResearch.WordTrace tailWord_1962616 prefixEnd_1962616 1007765348204598489574099 := by
  unfold tailWord_1962616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791243128892447486109851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47721657505189929981479801 35791243128892447486109851)
  ·
    refine ⟨53686864693338671229164777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791243128892447486109851 53686864693338671229164777)
    ·
      refine ⟨40265148520004003421873583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53686864693338671229164777 40265148520004003421873583)
      ·
        refine ⟨60397722780006005132810375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40265148520004003421873583 60397722780006005132810375)
        ·
          refine ⟨90596584170009007699215563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60397722780006005132810375 90596584170009007699215563)
          ·
            refine ⟨135894876255013511548823345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90596584170009007699215563 135894876255013511548823345)
            ·
              refine ⟨101921157191260133661617509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135894876255013511548823345 101921157191260133661617509)
              ·
                refine ⟨19110216973361275061553283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101921157191260133661617509 19110216973361275061553283)
                ·
                  refine ⟨28665325460041912592329925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19110216973361275061553283 28665325460041912592329925)
                  ·
                    refine ⟨5374748523757858611061861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28665325460041912592329925 5374748523757858611061861)
                    ·
                      refine ⟨1007765348204598489574099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5374748523757858611061861 1007765348204598489574099)
                      ·
                        rfl

theorem cell23_1962616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1962616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962616 prefixEnd_1962616 := by exact prefixLift 1962616
  have htrace : WordTrace (prefixWord ++ tailWord_1962616) baseStart_1962616 baseEnd_1962616 := by
    simpa [prefixWord, tailWord_1962616, baseEnd_1962616] using wordTrace_append hprefix tailTrace_1962616
  have hstable : (prefixWord ++ tailWord_1962616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962616).length < 2 ^ (prefixWord ++ tailWord_1962616).sum := by decide
  have hdescent : baseEnd_1962616 < baseStart_1962616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
